{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists, QuantifiedConstraints,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | A class containing array operations, with some extra algebraic operations
-- and dual numbers operations added in. This is a part of the high-level
-- API of the horde-ad library.
module HordeAd.Core.TensorClass
  ( IntOf, IndexOf, ShapeInt
  , PrimalOf, DualOf
  , Tensor(..), ConvertTensor(..), DomainsTensor(..), ADReady
  , GoodScalar, DummyDual(..), ttoRankedOrDummy
  ) where

import Prelude

import qualified Data.Array.Convert
import qualified Data.Array.DynamicS as OD
import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Flip
import           Data.Boolean
import           Data.Functor.Compose
import           Data.Kind (Constraint, Type)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Foreign.C (CInt)
import           GHC.TypeLits (KnownNat, Nat, type (+))
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           System.Random

import HordeAd.Core.Ast
import HordeAd.Core.Domains
import HordeAd.Core.SizedIndex
import HordeAd.Internal.TensorOps

-- * Tensor class definition

-- @IntOf a@ as size or shape gives more expressiveness,
-- but leads to irregular tensors, especially after vectorization,
-- and prevents statically known shapes.
-- However, if we switched to @Data.Array.Shaped@ and moved most of the shapes
-- to the type level, we'd recover some of the expressiveness, while retaining
-- statically known (type-parameterized) shapes.

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

class (forall r20. (GoodScalar r20) => c (ranked r20 0))
      => CRankedRR ranked c where
instance (forall r20. (GoodScalar r20) => c (ranked r20 0))
         => CRankedRR ranked c where

-- k is intended to be Nat or [Nat] (or nothing, if we support scalars)
type family PrimalOf (tensor :: Type -> k -> Type) :: Type -> k -> Type

type family DualOf (tensor :: Type -> k -> Type) :: Type -> k -> Type

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
  tfloor :: (GoodScalar r, RealFrac r) => ranked r 0 -> IntOf (ranked r 0)

  -- Typically scalar codomain, often tensor reduction
  -- (a number suffix in the name indicates the rank of codomain)
  tindex, (!) :: (GoodScalar r, KnownNat m, KnownNat n)
              => ranked r (m + n) -> IndexOf (ranked r 0) m -> ranked r n
  infixl 9 !
  (!) = tindex  -- prefix form better when type applications are necessary
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
  tmatmul2 :: (GoodScalar r, Num (ranked r 3))
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
  tminimum t = t ! tminIndex t
  tmaximum :: (GoodScalar r, KnownNat n)
           => ranked r n -> ranked r 0
  tmaximum t = t ! tmaxIndex t
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
  tmap0N f v = tbuild (tshape v) (\ix -> f $ v ! ix)
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
  tzipWith0N f u v = tbuild (tshape v) (\ix -> f (u ! ix) (v ! ix))
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
  tzero :: (GoodScalar r, KnownNat n, Num (ranked r 0))
        => ShapeInt n -> ranked r n
  tzero sh = treplicate0N sh 0
  tsumOfList :: (GoodScalar r, KnownNat n)
             => [ranked r n] -> ranked r n  -- TODO: declare nonempty
  default tsumOfList
    :: Num (ranked r n)
    => [ranked r n] -> ranked r n
  tsumOfList = sum
  tmult :: (GoodScalar r, KnownNat n)
        => ranked r n -> ranked r n -> ranked r n
  default tmult
    :: Num (ranked r n)
    => ranked r n -> ranked r n -> ranked r n
  tmult = (*)
  tscaleByScalar :: (GoodScalar r, KnownNat n)
                 => ranked r 0 -> ranked r n -> ranked r n
  tscaleByScalar s v = v `tmult` treplicate0N (tshape v) s
  tsumIn :: (GoodScalar r, KnownNat n) => ranked r (1 + n) -> ranked r n
  tsumIn = tsum . ttranspose [1, 0]
    -- TODO: generalize, replace by stride analysis, etc.
  tdot1In :: GoodScalar r => ranked r 2 -> ranked r 2 -> ranked r 1
  tdot1In t u = tsum (ttranspose [1, 0] (t `tmult` u))
    -- TODO: generalize, replace by stride analysis, etc.
  tconst :: (GoodScalar r, KnownNat n) => OR.Array n r -> ranked r n
  tconstBare :: (GoodScalar r, KnownNat n) => OR.Array n r -> ranked r n
  tconstBare = tconst
  tletWrap :: ADShare r -> ranked r n -> ranked r n
  tletWrap _l u = u

  -- Primal/dual things.
  tconstant :: (GoodScalar r, KnownNat n) => PrimalOf ranked r n -> ranked r n
  tprimalPart :: (GoodScalar r, KnownNat n)
              => ranked r n -> PrimalOf ranked r n
  tdualPart :: (GoodScalar r, KnownNat n)
            => ranked r n -> DualOf ranked r n
  tD :: (GoodScalar r, KnownNat n) => PrimalOf ranked r n -> DualOf ranked r n -> ranked r n
  tScale :: (GoodScalar r, KnownNat n) => PrimalOf ranked r n -> DualOf ranked r n -> DualOf ranked r n
  -- TODO: we'd probably also need dZero, dIndex0 and all others;
  -- basically DualOf a needs to have IsPrimal and HasRanks instances
  -- (and HasInputs?)
  -- TODO: if DualOf is supposed to be user-visible, we needed
  -- a better name for it; TangentOf? CotangentOf? SecondaryOf?

class (Underlying a ~ Underlying b, Underlying b ~ Underlying a)
      => UnderlyingMatches a b where
instance (Underlying a ~ Underlying b, Underlying b ~ Underlying a)
         => UnderlyingMatches a b where

class (forall r11 y. (KnownNat y, GoodScalar r11)
      => c (dynamic r11) (ranked r11 y))
      => CDynamicRanked dynamic ranked c where
instance (forall r11 y. (KnownNat y, GoodScalar r11)
         => c (dynamic r11) (ranked r11 y))
         => CDynamicRanked dynamic ranked c where

class CDynamicRanked dynamic ranked UnderlyingMatches
      => ConvertTensor (dynamic :: Type -> Type)
                       (ranked :: Type -> Nat -> Type)
                       (shaped :: Type -> [Nat] -> Type)
                       | dynamic -> ranked, dynamic -> shaped
                       , ranked -> dynamic, ranked -> shaped
                       , shaped -> dynamic, shaped -> ranked where
  tfromD :: (GoodScalar r, KnownNat n)
         => dynamic r -> ranked r n
  tfromS :: (KnownNat n, GoodScalar r, OS.Shape sh, OS.Rank sh ~ n)
         => shaped r sh -> ranked r n
  dfromR :: (GoodScalar r, KnownNat n)
         => ranked r n -> dynamic r
  dfromS :: OS.Shape sh
         => shaped r sh -> dynamic r
  sfromR :: (KnownNat n, GoodScalar r, OS.Shape sh, OS.Rank sh ~ n)
         => ranked r n -> shaped r sh
  sfromD :: OS.Shape sh
         => dynamic r -> shaped r sh
  ddummy :: Numeric r => dynamic r
  disDummy :: Numeric r => dynamic r -> Bool
  daddR :: forall n r. (GoodScalar r, KnownNat n)
        => ranked r n -> dynamic r -> dynamic r
  dshape :: GoodScalar r => dynamic r -> [Int]
  -- Operations for delayed let bindings creation
  tregister :: (GoodScalar r, KnownNat n)
            => ranked r n -> [(AstVarId, dynamic r)]
            -> ([(AstVarId, dynamic r)], ranked r n)
  tregister r l = (l, r)

class DomainsTensor (dynamic :: Type -> Type)
                    (ranked :: Type -> Nat -> Type)
                    (domainsOf :: Type -> Type)
                    | ranked -> dynamic domainsOf
                    , dynamic -> ranked domainsOf
                    , domainsOf -> ranked dynamic where
  tletDomains :: (GoodScalar r, KnownNat n)
              => domainsOf r
              -> (domainsOf r -> ranked r n)
              -> ranked r n
  tletDomains a f = f a
  dmkDomains :: Domains dynamic r -> domainsOf r
  default dmkDomains
    :: domainsOf ~ Compose Data.Vector.Vector dynamic
    => Domains dynamic r -> domainsOf r
  dmkDomains = Compose
  dlet :: (GoodScalar r, KnownNat n)
       => ranked r n -> (ranked r n -> domainsOf r)
       -> domainsOf r
  dlet a f = f a

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


-- * Tensor class instances for concrete arrays

type instance IntOf (Flip OR.Array r n) = CInt

type instance PrimalOf (Flip OR.Array) = Flip OR.Array

type instance DualOf (Flip OR.Array) = DummyDual

instance Tensor (Flip OR.Array) where
  tshape = tshapeR . runFlip
  tminIndex0 = tminIndexR . runFlip
  tmaxIndex0 = tmaxIndexR . runFlip
  tfloor = floor . tunScalarR . runFlip
  tindex v ix = Flip $ tindexZR (runFlip v) ix
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

  tconstant = id
  tprimalPart = id
  tdualPart _ = DummyDual
  tD u _ = u
  tScale _ _ = DummyDual

data DummyDual a (b :: Nat) = DummyDual

instance ConvertTensor OD.Array (Flip OR.Array) (Flip OS.Array) where
  tfromD = Flip . Data.Array.Convert.convert
  tfromS = Flip . Data.Array.Convert.convert . runFlip
  dfromR = Data.Array.Convert.convert . runFlip
  dfromS = Data.Array.Convert.convert . runFlip
  sfromR = Flip . Data.Array.Convert.convert . runFlip
  sfromD = Flip . Data.Array.Convert.convert
  ddummy = dummyTensor
  disDummy = isTensorDummy
  daddR r d = if isTensorDummy d then dfromR r else dfromR r + d
  dshape = OD.shapeL

instance DomainsTensor OD.Array (Flip OR.Array)
                       (Compose Data.Vector.Vector OD.Array) where

{- TODO: requires IncoherentInstances no matter what pragma I stick in
-- TODO2: benchmark this used for any scalar via @V.map realToFrac@
-- A special case, because for @Double@ we have faster @randomVals@,
-- though the quality of randomness is worse (going through a single @Int@).
instance {-# OVERLAPS #-} {-# OVERLAPPING #-}
         KnownNat n
         => AdaptableDomains (OR.Array n Double) where
  type Underlying (OR.Array n Double) = Double
  toDomains a =
    (V.empty, V.empty, V.empty, V.singleton (Data.Array.Convert.convert a))
  fromDomains _aInit (v0, v1) = case V.uncons v1 of
    Just (a, rest) -> (toShapedOrDummy a, (v0, v1, v2, rest))
    Nothing -> error "fromDomains in AdaptableDomains (OR.Array n r)"
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

instance (GoodScalar r, KnownNat n)
         => AdaptableDomains OD.Array (Flip OR.Array r n) where
  type Underlying (Flip OR.Array r n) = r
  type Value (Flip OR.Array r n) = Flip OR.Array r n
  toDomains a = V.singleton (dfromR a)
  fromDomains aInit params = case V.uncons params of
    Just (a, rest) ->
      Just (ttoRankedOrDummy @OD.Array @(Flip OR.Array)
                             (tshape aInit) a, rest)
    Nothing -> Nothing

ttoRankedOrDummy
  :: forall dynamic ranked shaped n r.
     ( KnownNat n, Tensor ranked, GoodScalar r, Num (ranked r 0)
     , ConvertTensor dynamic ranked shaped )
  => ShapeInt n -> dynamic r -> ranked r n
ttoRankedOrDummy sh x = if disDummy @dynamic @ranked x
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
              $ createRandomVector (OR.size undefined) g1  -- TODO
    in (Flip arr, g2)
  type ToRanked (Flip OR.Array r n) = Flip OR.Array r n
  toRanked = id

instance AdaptableDomains OD.Array (OD.Array r) where
  type Underlying (OD.Array r) = r
  type Value (OD.Array r) = OD.Array r
  toDomains = undefined
  fromDomains = undefined

instance (Numeric r, OS.Shape sh)
         => AdaptableDomains OD.Array (Flip OS.Array r sh) where
  type Underlying (Flip OS.Array r sh) = r
  type Value (Flip OS.Array r sh) = Flip OS.Array r sh
--  toDomains :: forall sh.
  toDomains a = V.singleton (dfromS a)
  fromDomains = undefined

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
