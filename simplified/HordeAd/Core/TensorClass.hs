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
  ( ShapeInt, IntOf, IndexOf, ShapeSh, IntSh, IndexSh
  , PrimalOf, DualOf, DynamicOf, RankedOf, ShapedOf
  , ShapedTensor(..), RankedTensor(..), ConvertTensor(..), DomainsTensor(..)
  , ADReady, ADReadyS, ADRanked, ADShaped
  , GoodScalar, DummyDual(..)
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
import           Data.Boolean
import           Data.Kind (Type)
import           Data.List (foldl1')
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           Foreign.C (CInt)
import           GHC.TypeLits
  (KnownNat, Nat, OrderingI (..), cmpNat, type (+), type (-), type (<=))
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           System.Random
import           Type.Reflection (typeRep)
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

type family IntOf (f :: TensorKind k) :: Type

-- | Thanks to the OverloadedLists mechanism, values of this type can be
-- written using the normal list notation. However, such values, if not
-- explicitly typed, do not inform the compiler about the length
-- of the list until runtime. That means that some errors are hidden
-- and also extra type applications may be needed to satisfy the compiler.
-- Therefore, there is a real trade-off between @[2]@ and @(2 :. ZI).
type IndexOf f n = Index n (IntOf f)

-- TODO: ensure this is checked (runtime-checked, if necessary):
-- | The value of this type has to be positive and less than the @n@ bound.
-- If the values are terms, this is relative to environment
-- and up to evaluation.
type IntSh f (n :: Nat) = ShapedNat n (IntOf f)

-- TODO: ensure this is checked (runtime-checked, if necessary):
-- | The values of this type are bounded by the shape.
-- If the values are terms, this is relative to environment
-- and up to evaluation.
type IndexSh f (sh :: [Nat]) = ShapedList sh (IntOf f)

class (forall r20 y20. (KnownNat y20, GoodScalar r20) => c (ranked r20 y20))
      => CRankedR ranked c where
instance (forall r20 y20. (KnownNat y20, GoodScalar r20) => c (ranked r20 y20))
         => CRankedR ranked c where

-- k is intended to be Nat or [Nat] (or nothing, if we support scalars)
type family PrimalOf (f :: TensorKind k) :: TensorKind k

type family DualOf (f :: TensorKind k) :: TensorKind k

type family DynamicOf (f :: TensorKind k) :: Type -> Type

type instance DynamicOf (Clown OD.Array) = OD.Array

type instance DynamicOf (Clown AstDynamic) = AstDynamic

type family RankedOf (f :: TensorKind k) :: RankedTensorKind

type instance RankedOf (Clown OD.Array) = Flip OR.Array

type family ShapedOf (f :: TensorKind k) :: ShapedTensorKind

type instance ShapedOf (Clown OD.Array) = Flip OS.Array

-- | The superclasses indicate that it's not only a container array,
-- but also a mathematical tensor, sporting numeric operations.
class (Integral (IntOf ranked), CRankedR ranked RealFloat)
      => RankedTensor (ranked :: RankedTensorKind) where

  -- TODO: type Scalar r = ranked r 0
  -- is a macro/TH the only way?

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
  tminIndex0 :: GoodScalar r => ranked r 1 -> IntOf ranked  -- partial
  tminIndex :: (KnownNat n, GoodScalar r)
            => ranked r n -> IndexOf ranked n
  tminIndex t = fromLinearIdx (tshape t) (tminIndex0 (tflatten t))
  tmaxIndex0 :: GoodScalar r => ranked r 1 -> IntOf ranked  -- partial
  tmaxIndex :: (GoodScalar r, KnownNat n)
            => ranked r n -> IndexOf ranked n
  tmaxIndex t = fromLinearIdx (tshape t) (tmaxIndex0 (tflatten t))
  tfloor :: GoodScalar r => ranked r 0 -> IntOf ranked

  -- Typically scalar codomain, often tensor reduction
  -- (a number suffix in the name indicates the rank of codomain)
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
  -- The let is required to preserve the sharing of the argument, which is
  -- used twice: in tminIndex0 and in tindex0.
  -- TODO: this simpler form will be possible when intLet is available
  -- and so sharing of integer expressions is not broken.
  -- tminimum t0 = tlet t0 $ \t -> tindex0 t (tminIndex t)
  tminimum t0 = tlet t0 $ \t ->
                  tlet (tflatten t) $ \tf ->
                    tindex0 t $ fromLinearIdx (tshape t) (tminIndex0 tf)
  tmaximum :: (GoodScalar r, KnownNat n)
           => ranked r n -> ranked r 0
  tmaximum t0 = tlet t0 $ \t ->
                  tlet (tflatten t) $ \tf ->
                    tindex0 t $ fromLinearIdx (tshape t) (tmaxIndex0 tf)
  tfromIndex0 :: GoodScalar r => IntOf ranked -> ranked r 0
  tfromIndex1 :: GoodScalar r => IndexOf ranked n -> ranked r 1
  tfromIndex1 = tfromList . map tfromIndex0 . indexToList
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
  tcast :: (GoodScalar r1, GoodScalar r2, KnownNat n)
        => ranked r1 n -> ranked r2 n

  -- ** No serviceable parts beyond this point ** --

  -- Needed to avoid Num (ranked r n) constraints all over the place
  -- and also wrong shape in @0@ with ranked (not shaped) tensors.
  tzero :: (GoodScalar r, KnownNat n)
        => ShapeInt n -> ranked r n
  tzero sh = treplicate0N sh 0
  tsumOfList :: (GoodScalar r, KnownNat n)
             => [ranked r n] -> ranked r n  -- TODO: declare nonempty
  tsumOfList [] = 0
  tsumOfList l = foldl1' (+) l  -- avoid unknown shape of @0@ in @sum@
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
  tletWrap :: ADShare -> ranked r n -> ranked r n
  tletWrap _l u = u
  raddDynamic :: forall r n. (GoodScalar r, KnownNat n)
              => ranked r n -> DynamicExists (DynamicOf ranked)
              -> DynamicExists (DynamicOf ranked)
  tregister :: (GoodScalar r, KnownNat n)
            => ranked r n -> [(AstVarId, DynamicExists (DynamicOf ranked))]
            -> ([(AstVarId, DynamicExists (DynamicOf ranked))], ranked r n)
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

class (Integral (IntOf shaped), CRankedS shaped RealFloat)
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
  sminIndex0 :: (GoodScalar r, KnownNat n)
             => shaped r '[n] -> IntSh shaped n  -- partial
  sminIndex :: (GoodScalar r, OS.Shape sh, KnownNat (OS.Size sh))
            => shaped r sh -> IndexSh shaped sh
  sminIndex t = ShapedList.fromLinearIdx (sshape t) (sminIndex0 (sflatten t))
  smaxIndex0 :: (GoodScalar r, KnownNat n)
             => shaped r '[n] -> IntSh shaped n  -- partial
  smaxIndex :: (GoodScalar r, OS.Shape sh, KnownNat (OS.Size sh))
            => shaped r sh -> IndexSh shaped sh
  smaxIndex t = ShapedList.fromLinearIdx (sshape t) (smaxIndex0 (sflatten t))
  sfloor :: GoodScalar r => shaped r '[] -> IntOf shaped
    -- not IntSh, because the integer can be negative
    -- TODO: shall we make it abs (floor v)?

  -- Typically scalar codomain, often tensor reduction
  -- (a number suffix in the name indicates the rank of codomain)
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
  sdot0 t u = ssum (sflatten (t `smult` u))
  smatvecmul :: forall r m n. (GoodScalar r, KnownNat m, KnownNat n)
             => shaped r '[m, n] -> shaped r '[n] -> shaped r '[m]
  smatvecmul m v = sbuild1 (\i -> sdot0 v (m !$ (consShaped i ZSH)))
  smatmul2 :: forall r n m p. (GoodScalar r, KnownNat n, KnownNat m, KnownNat p)
           => shaped r '[m, n] -> shaped r '[n, p] -> shaped r '[m, p]
  smatmul2 m1 m2 =
    ssum (stranspose (Proxy @'[2, 1, 0]) (sreplicate @shaped @r @p m1)
          * stranspose (Proxy @'[1, 0]) (sreplicate @shaped @r @m m2))
  sminimum :: forall r sh. (GoodScalar r, OS.Shape sh, KnownNat (OS.Size sh))
           => shaped r sh -> shaped r '[]
  sminimum t = gcastWith (unsafeCoerce Refl :: (sh OS.++ '[])  :~: sh)
               $ t !$ sminIndex t
  smaximum :: forall r sh.(GoodScalar r, OS.Shape sh, KnownNat (OS.Size sh))
           => shaped r sh -> shaped r '[]
  smaximum t = gcastWith (unsafeCoerce Refl :: (sh OS.++ '[])  :~: sh)
               $ t !$ smaxIndex t
  sfromIndex0 :: forall n r. (GoodScalar r, KnownNat n)
              => IntSh shaped n -> shaped r '[]
  sfromIndex1 :: forall r sh. (GoodScalar r, OS.Shape sh, KnownNat (OS.Rank sh))
              => IndexSh shaped sh -> shaped r '[OS.Rank sh]
  sfromIndex1 =
    let go :: IndexSh shaped sh1 -> [shaped r '[]]
        go ZSH = []
        go ((:$:) @n i rest) = sfromIndex0 @shaped @n (ShapedList.shapedNat i)
                               : go rest
    in sfromList . go
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
  scast :: (GoodScalar r1, GoodScalar r2, OS.Shape sh)
        => shaped r1 sh -> shaped r2 sh

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
  sletWrap :: ADShare -> shaped r sh -> shaped r sh
  sletWrap _l u = u
  saddDynamic :: forall r sh. (GoodScalar r, OS.Shape sh)
              => shaped r sh -> DynamicExists (DynamicOf shaped)
              -> DynamicExists (DynamicOf shaped)
  sregister :: (GoodScalar r, OS.Shape sh)
            => shaped r sh -> [(AstVarId, DynamicExists (DynamicOf shaped))]
            -> ([(AstVarId, DynamicExists (DynamicOf shaped))], shaped r sh)
  sregister r l = (l, r)

  -- Primal/dual things.
  sconstant :: (GoodScalar r, OS.Shape sh)
            => PrimalOf shaped r sh -> shaped r sh
  sprimalPart :: GoodScalar r
              => shaped r sh -> PrimalOf shaped r sh
  sdualPart :: GoodScalar r
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

-- Ordinary quantified constraints don't work due to the PrimalOf type family
-- but also due to the RankedOf type family inside ADShaped.
class (forall y71. KnownNat y71 => c ranked r y71)
      => CRanked71 ranked r c where
instance (forall y71. KnownNat y71 => c ranked r y71)
         => CRanked71 ranked r c where

class IfB (ranked r n) => IfBRanked ranked r n where
instance IfB (ranked r n) => IfBRanked ranked r n where

class EqB (ranked r n) => EqBRanked ranked r n where
instance EqB (ranked r n) => EqBRanked ranked r n where

class OrdB (ranked r n) => OrdBRanked ranked r n where
instance OrdB (ranked r n) => OrdBRanked ranked r n where

class IfB (PrimalOf ranked r n) => IfBPrimalOf ranked r n where
instance IfB (PrimalOf ranked r n) => IfBPrimalOf ranked r n where

class EqB (PrimalOf ranked r n) => EqBPrimalOf ranked r n where
instance EqB (PrimalOf ranked r n) => EqBPrimalOf ranked r n where

class OrdB (PrimalOf ranked r n) => OrdBPrimalOf ranked r n where
instance OrdB (PrimalOf ranked r n) => OrdBPrimalOf ranked r n where

type ADReady ranked r = ADRanked ranked r  -- backward compatibility

type ADRanked ranked r = (ADReadyR ranked r, ADReadyS (ShapedOf ranked) r)

type ADShaped shaped r = (ADReadyR (RankedOf shaped) r, ADReadyS shaped r)

type ADReadyR ranked r =
  ( RankedTensor ranked, GoodScalar r, RankedTensor (PrimalOf ranked)
  , IfB (IntOf ranked)
  , CRanked71 ranked r IfBRanked, CRanked71 ranked r IfBPrimalOf
  , EqB r, EqB (IntOf ranked)
  , CRanked71 ranked r EqBRanked, CRanked71 ranked r EqBPrimalOf
  , OrdB r, OrdB (IntOf ranked)
  , CRanked71 ranked r OrdBRanked, CRanked71 ranked r OrdBPrimalOf
  , Boolean (BooleanOf (IntOf ranked))
  , ( BooleanOf (IntOf ranked) ~ BooleanOf (ranked r 1)
    , BooleanOf (IntOf ranked) ~ BooleanOf (ranked r 2)
    , BooleanOf (IntOf ranked) ~ BooleanOf (ranked r 3)
    , BooleanOf (IntOf ranked) ~ BooleanOf (ranked r 4)
{- TODO: GHC 9.4 and 9.6 can't cope with too many of these:
    , BooleanOf (IntOf ranked) ~ BooleanOf (ranked r 5)
    , BooleanOf (IntOf ranked) ~ BooleanOf (ranked r 6) -}
    , BooleanOf (IntOf ranked) ~ BooleanOf (ranked r 7)
{-
    , BooleanOf (IntOf ranked) ~ BooleanOf (ranked r 8)
    , BooleanOf (IntOf ranked) ~ BooleanOf (ranked r 9)
    , BooleanOf (IntOf ranked) ~ BooleanOf (ranked r 10)
    , BooleanOf (IntOf ranked) ~ BooleanOf (ranked r 11)
    , BooleanOf (IntOf ranked) ~ BooleanOf (ranked r 12) -} )
  , ( BooleanOf (IntOf ranked) ~ BooleanOf (PrimalOf ranked r 0)
    , BooleanOf (IntOf ranked) ~ BooleanOf (PrimalOf ranked r 1)
    , BooleanOf (IntOf ranked) ~ BooleanOf (PrimalOf ranked r 2)
    , BooleanOf (IntOf ranked) ~ BooleanOf (PrimalOf ranked r 3)
    , BooleanOf (IntOf ranked) ~ BooleanOf (PrimalOf ranked r 4)
{-
    , BooleanOf (IntOf ranked) ~ BooleanOf (PrimalOf ranked r 5)
    , BooleanOf (IntOf ranked) ~ BooleanOf (PrimalOf ranked r 6)
    , BooleanOf (IntOf ranked) ~ BooleanOf (PrimalOf ranked r 7)
    , BooleanOf (IntOf ranked) ~ BooleanOf (PrimalOf ranked r 8)
    , BooleanOf (IntOf ranked) ~ BooleanOf (PrimalOf ranked r 9)
    , BooleanOf (IntOf ranked) ~ BooleanOf (PrimalOf ranked r 10)
    , BooleanOf (IntOf ranked) ~ BooleanOf (PrimalOf ranked r 11)
    , BooleanOf (IntOf ranked) ~ BooleanOf (PrimalOf ranked r 12) -} )
  , BooleanOf (IntOf ranked) ~ BooleanOf (ranked r 0)
      -- placing this last gives better errors
  )

type ADReadyS shaped r =
  ( ShapedTensor shaped, GoodScalar r, ShapedTensor (PrimalOf shaped)
  , IfB (IntOf shaped), IfB (shaped r '[])
  , IfB (PrimalOf shaped r '[])
  , EqB r, EqB (IntOf shaped), EqB (shaped r '[])
  , EqB (PrimalOf shaped r '[])
  , OrdB r, OrdB (IntOf shaped), OrdB (shaped r '[])
  , OrdB (PrimalOf shaped r '[])
  , Boolean (BooleanOf (IntOf shaped))
  , BooleanOf (IntOf shaped) ~ BooleanOf (PrimalOf shaped r '[])
  , BooleanOf (IntOf shaped) ~ BooleanOf (shaped r '[])
      -- placing this last gives better errors
  )


-- * Ranked tensor class instance for concrete arrays

type instance IntOf (Flip OR.Array) = CInt

type instance PrimalOf (Flip OR.Array) = Flip OR.Array

type instance DualOf (Flip OR.Array) = DummyDual

type instance DynamicOf (Flip OR.Array) = OD.Array

type instance DynamicOf AstRanked = AstDynamic

type instance RankedOf (Flip OR.Array) = Flip OR.Array

type instance ShapedOf (Flip OR.Array) = Flip OS.Array

instance RankedTensor (Flip OR.Array) where
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
  tslice i n = Flip . tsliceR i n . runFlip
  treverse = Flip . treverseR . runFlip
  ttranspose perm = Flip . ttransposeR perm . runFlip
  treshape sh = Flip . treshapeR sh . runFlip
  tbuild1 k f = Flip $ tbuild1R k (runFlip . f)
  tmap0N f t = Flip $ tmap0NR (runFlip . f . Flip) (runFlip t)
  tzipWith0N f t u = Flip $ tzipWith0NR (\v w -> runFlip $ f (Flip v) (Flip w))
                                        (runFlip t) (runFlip u)
  tgather sh t f = Flip $ tgatherZR sh (runFlip t) f
  tgather1 k t f = Flip $ tgatherZ1R k (runFlip t) f
  tcast = Flip . tcastR . runFlip

  tscaleByScalar s v =
    Flip $ tscaleByScalarR (tunScalarR $ runFlip s) (runFlip v)
  tsumIn = Flip . tsumInR . runFlip
  tdot1In u v = Flip $ tdot1InR (runFlip u) (runFlip v)
  tconst = Flip
  raddDynamic :: forall r n. (GoodScalar r, KnownNat n)
              => Flip OR.Array r n -> DynamicExists OD.Array
              -> DynamicExists OD.Array
  raddDynamic r (DynamicExists @_ @r2 d) = DynamicExists $
    if isTensorDummy d then dfromR r
    else case testEquality (typeRep @r) (typeRep @r2) of
      Just Refl -> dfromR r + d
      _ -> error "raddDynamic: type mismatch"

  tconstant = id
  tprimalPart = id
  tdualPart _ = DummyDual
  tD u _ = u
  tScale _ _ = DummyDual

data DummyDual a (b :: k) = DummyDual

instance (GoodScalar r, KnownNat n)
         => AdaptableDomains OD.Array (Flip OR.Array r n) where
  type Value (Flip OR.Array r n) = Flip OR.Array r n
  toDomains a = V.singleton $ DynamicExists $ dfromR a
  fromDomains aInit params = case V.uncons params of
    Just (DynamicExists @_ @r2 a, rest) ->
      case testEquality (typeRep @r) (typeRep @r2) of
        Just Refl -> Just (toRankedOrDummy (tshape aInit) a, rest)
        _ -> error "fromDomains: type mismatch"
    Nothing -> Nothing

instance ( GoodScalar r, KnownNat n
         , RankedTensor AstRanked, ConvertTensor AstRanked AstShaped )
         => AdaptableDomains AstDynamic (AstRanked r n) where
  type Value (AstRanked r n) = Flip OR.Array r n
  toDomains = undefined
  fromDomains aInit params = case V.uncons params of
    Just (DynamicExists @_ @r2 a, rest) ->
      case testEquality (typeRep @r) (typeRep @r2) of
        Just Refl -> Just (toRankedOrDummy (tshape aInit) a, rest)
        _ -> error "fromDomains: type mismatch"
    Nothing -> Nothing

toRankedOrDummy
  :: forall ranked shaped n r.
     ( KnownNat n, RankedTensor ranked, GoodScalar r
     , ConvertTensor ranked shaped )
  => ShapeInt n -> DynamicOf ranked r -> ranked r n
toRankedOrDummy sh x = if disDummy @ranked x
                       then tzero sh
                       else tfromD x

instance RandomDomains (Flip OR.Array r n) where
  randomVals = undefined
  toValue = id


-- * Shaped tensor class instance for concrete arrays

type instance IntOf (Flip OS.Array) = CInt

type instance PrimalOf (Flip OS.Array) = Flip OS.Array

type instance DualOf (Flip OS.Array) = DummyDual

type instance DynamicOf (Flip OS.Array) = OD.Array

type instance DynamicOf AstShaped = AstDynamic

type instance RankedOf (Flip OS.Array) = Flip OR.Array

type instance ShapedOf (Flip OS.Array) = Flip OS.Array

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
  scast = Flip . tcastS . runFlip

  sscaleByScalar s v =
    Flip $ tscaleByScalarS (tunScalarS $ runFlip s) (runFlip v)
  ssumIn = Flip . tsumInS . runFlip
  sdot1In u v = Flip $ tdot1InS (runFlip u) (runFlip v)
  sconst = Flip
  saddDynamic :: forall r sh. (GoodScalar r, OS.Shape sh)
              => Flip OS.Array r sh -> DynamicExists OD.Array
              -> DynamicExists OD.Array
  saddDynamic r (DynamicExists @_ @r2 d) = DynamicExists $
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
    Just (DynamicExists @_ @r2 a, rest) ->
      case testEquality (typeRep @r) (typeRep @r2) of
        Just Refl -> Just (toShapedOrDummy a, rest)
        _ -> error "fromDomains: type mismatch"
    Nothing -> Nothing

instance ( GoodScalar r, OS.Shape sh
         , ShapedTensor AstShaped, ConvertTensor AstRanked AstShaped )
         => AdaptableDomains AstDynamic (AstShaped r sh) where
  type Value (AstShaped r sh) = Flip OS.Array r sh
  toDomains = undefined
  fromDomains _aInit params = case V.uncons params of
    Just (DynamicExists @_ @r2 a, rest) ->
      case testEquality (typeRep @r) (typeRep @r2) of
        Just Refl -> Just (toShapedOrDummy a, rest)
        _ -> error "fromDomains: type mismatch"
    Nothing -> Nothing

toShapedOrDummy
  :: forall ranked shaped sh r.
     ( OS.Shape sh, ShapedTensor shaped, GoodScalar r
     , ConvertTensor ranked shaped )
  => DynamicOf shaped r -> shaped r sh
toShapedOrDummy x = if disDummy @ranked x
                    then 0
                    else sfromD x

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
