{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists, QuantifiedConstraints,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | A class containing array operations, with some extra algebraic operations
-- and dual numbers operations added in. This is a part of the high-level
-- API of the horde-ad library.
module HordeAd.Core.TensorClass
  ( Domain0, DomainR, Domains
  , domains0, domainsR, mkDomains, ttoRankedOrDummy
  , IndexOf, TensorOf, ShapeInt, CRanked, CYRanked, CRanked2
  , Tensor(..), DynamicTensor(..), DomainsTensor(..), ADReady
  ) where

import Prelude

import qualified Data.Array.Convert
import qualified Data.Array.DynamicS as OD
import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import           Data.Bifunctor.Flip
import           Data.Boolean
import           Data.Kind (Constraint, Type)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Foreign.C (CInt)
import           GHC.TypeLits (KnownNat, Nat, type (+))
import           Numeric.LinearAlgebra (Numeric)
import qualified Numeric.LinearAlgebra as LA
import           System.Random

import HordeAd.Core.Ast
import HordeAd.Core.Domains
import HordeAd.Core.SizedIndex
import HordeAd.Internal.TensorOps

-- * Domains datatypes definition

-- | Helper definitions to shorten type signatures. @Domains@, among other
-- roles, is the internal representation of domains of objective functions.
type Domain0 r = TensorOf 1 r

-- To store ranked tensors (or Ast terms) we use their untyped versions
-- instead of, e.g,. the unerlying vectors of the tensors,
-- to prevent frequent linearization of the tensors (e.g., after transpose).
type DomainR r = Data.Vector.Vector (DTensorOf r)

domains0 :: (DomainsCollection r, Tensor r) => Domains r -> Domain0 r
domains0 v = tfromD $ doms0 v

domainsR :: DomainsCollection r => Domains r -> DomainR r
domainsR = toVectorDoms . domsR

mkDomains :: (DomainsCollection r, Tensor r)
          => Domain0 r -> DomainR r -> Domains r
mkDomains d0 dR = mkDoms (dfromR d0) (fromVectorDoms dR)

ttoRankedOrDummy :: (Tensor r, DynamicTensor r, KnownNat n)
                 => ShapeInt n -> DTensorOf r -> TensorOf n r
ttoRankedOrDummy sh x = if disDummy x
                        then tzero sh
                        else tfromD x


-- * Tensor class definition

-- @IntOf r@ as size or shape gives more expressiveness,
-- but leads to irregular tensors, especially after vectorization,
-- and prevents statically known shapes.
-- However, if we switched to @Data.Array.Shaped@ and moved most of the shapes
-- to the type level, we'd recover some of the expressiveness, while retaining
-- statically known (type-parameterized) shapes.

-- | Thanks to the OverloadedLists mechanism, values of this type can be
-- written using the normal list notation. However, such values, if not
-- explicitly typed, do not inform the compiler about the length
-- of the list until runtime. That means that some errors are hidden
-- and also extra type applications may be needed to satisfy the compiler.
-- Therefore, there is a real trade-off between @[2]@ and @(2 :. ZI).
type IndexOf n r = Index n (IntOf r)
type TensorOf (n :: Nat) r = Ranked r n

class (forall y. KnownNat y => c (Ranked r y)) => CRanked c r where
instance (forall y. KnownNat y => c (Ranked r y)) => CRanked c r where

class (forall y. c y r (Ranked r y)) => CYRanked c r where
instance (forall y. c y r (Ranked r y)) => CYRanked c r where

class (forall y z. c (Ranked r y) (Ranked r z)) => CRanked2 c r where
instance (forall y z. c (Ranked r y) (Ranked r z)) => CRanked2 c r where

-- TODO: when we have several times more operations, split into
-- Array (Container) and Tensor (Numeric), with the latter containing the few
-- Ord and Num operations and numeric superclasses.
-- | The superclasses indicate that it's not only a container array,
-- but also a mathematical tensor, sporting numeric operations.
class (RealFloat r, CRanked RealFloat r, Integral (IntOf r))
      => Tensor r where
  type Ranked r = (t :: Nat -> Type) | t -> r
  type IntOf r

  tlet :: (KnownNat n, KnownNat m)
       => TensorOf n r -> (TensorOf n r -> TensorOf m r)
       -> TensorOf m r
  tlet a f = f a

  -- Integer codomain
  tshape :: KnownNat n => TensorOf n r -> ShapeInt n
  trank :: forall n. KnownNat n => TensorOf n r -> Int
  trank _ = valueOf @n
  tsize :: KnownNat n => TensorOf n r -> Int
  tsize = sizeShape . tshape
  tlength :: KnownNat n => TensorOf (1 + n) r -> Int
  tlength v = case tshape v of
    ZS -> error "tlength: impossible pattern needlessly required"
    k :$ _ -> k
  tminIndex0 :: TensorOf 1 r -> IntOf r  -- partial
  tminIndex :: KnownNat n => TensorOf n r -> IndexOf n r
  tminIndex t = fromLinearIdx (tshape t) (tminIndex0 (tflatten t))
  tmaxIndex0 :: TensorOf 1 r -> IntOf r  -- partial
  tmaxIndex :: KnownNat n => TensorOf n r -> IndexOf n r
  tmaxIndex t = fromLinearIdx (tshape t) (tmaxIndex0 (tflatten t))
  tfloor :: TensorOf 0 r -> IntOf r
  default tfloor  -- a more narrow type to rule out Ast
    :: (IntOf r ~ CInt) => TensorOf 0 r -> IntOf r
  tfloor = floor . tunScalar

  -- Typically scalar codomain, often tensor reduction
  -- (a number suffix in the name indicates the rank of codomain)
  tindex, (!) :: (KnownNat m, KnownNat n)
              => TensorOf (m + n) r -> IndexOf m r -> TensorOf n r
  infixl 9 !
  (!) = tindex  -- prefix form better when type applications are necessary
  tsum :: KnownNat n => TensorOf (1 + n) r -> TensorOf n r
  tsum0 :: KnownNat n => TensorOf n r -> TensorOf 0 r
  tsum0 = tsum . tflatten
  tdot0 :: KnownNat n => TensorOf n r -> TensorOf n r -> TensorOf 0 r
  tdot0 t u = tsum (tflatten (t `tmult` u))
  tmatmul1 :: TensorOf 2 r -> TensorOf 1 r -> TensorOf 1 r
  tmatmul1 m v = tbuild1 (tlength m) (\i -> tdot0 v (m ! [i]))
-- How to generalize (#69)? these equivalent definitions generalize differently
-- and the two tmatmul2 variants differ in what transpositions get multiplied.
-- tmatmul1 m v = tflatten $ tmap1 (tkonst 1 . tdot0 v) m
  tmatmul2 :: TensorOf 2 r -> TensorOf 2 r -> TensorOf 2 r
-- tmatmul2 m1 m2 = tbuild1 (tlength m1) (\i -> tmatmul1 m2 (m1 ! [i]))
  tmatmul2 m1 m2 = tmap1 (tmatmul1 (ttr m2)) m1
  tminimum :: KnownNat n => TensorOf n r -> TensorOf 0 r
  tminimum t = t ! tminIndex t
  tmaximum :: KnownNat n => TensorOf n r -> TensorOf 0 r
  tmaximum t = t ! tmaxIndex t
  tfromIndex0 :: IntOf r -> TensorOf 0 r
  default tfromIndex0  -- the more narrow type rules out Ast
    :: IntOf r ~ CInt => IntOf r -> TensorOf 0 r
  tfromIndex0 = tscalar . fromIntegral
  tfromIndex1 :: IndexOf n r -> TensorOf 1 r
  tfromIndex1 = tfromList . map tfromIndex0 . indexToList
  tscatter :: (KnownNat m, KnownNat n, KnownNat p)
           => ShapeInt (p + n) -> TensorOf (m + n) r
           -> (IndexOf m r -> IndexOf p r)
           -> TensorOf (p + n) r
  tscatter1 :: (KnownNat n, KnownNat p)
            => ShapeInt (p + n) -> TensorOf (1 + n) r
            -> (IntOf r -> IndexOf p r)
            -> TensorOf (p + n) r
  tscatter1 sh v f = tscatter @r @1 sh v
                              (\(i :. ZI) -> f i)

  -- Tensor codomain, often tensor construction, sometimes transformation
  -- (for these, suffix 1 doesn't mean codomain rank 1, but building up
  -- by one rank, and is omitted if a more general variant is not defined)
  tfromList :: KnownNat n => [TensorOf n r] -> TensorOf (1 + n) r
  tfromList0N :: KnownNat n => ShapeInt n -> [r] -> TensorOf n r
  tfromList0N sh = treshape sh . tfromList . map tscalar
  tfromVector :: KnownNat n
              => Data.Vector.Vector (TensorOf n r) -> TensorOf (1 + n) r
  tfromVector v = tfromList (V.toList v)  -- horribly inefficient for large vs
  tfromVector0N :: KnownNat n
                => ShapeInt n -> Data.Vector.Vector r -> TensorOf n r
  tfromVector0N sh = treshape sh . tfromVector . V.map tscalar
  tkonst :: KnownNat n => Int -> TensorOf n r -> TensorOf (1 + n) r
  tkonst0N :: KnownNat n => ShapeInt n -> TensorOf 0 r -> TensorOf n r
  tkonst0N sh = treshape sh . tkonst (sizeShape sh)
  tappend :: KnownNat n
          => TensorOf (1 + n) r -> TensorOf (1 + n) r -> TensorOf (1 + n) r
  tconcat :: KnownNat n
          => [TensorOf (1 + n) r] -> TensorOf (1 + n) r
  tconcat = foldr1 tappend
  tslice :: KnownNat n
         => Int -> Int -> TensorOf (1 + n) r -> TensorOf (1 + n) r
  tuncons :: KnownNat n
          => TensorOf (1 + n) r -> Maybe (TensorOf n r, TensorOf (1 + n) r)
  tuncons v = if tlength v == 0
              then Nothing
              else Just (v ! [0], tslice 1 (tlength v - 1) v)
  treverse :: KnownNat n => TensorOf (1 + n) r -> TensorOf (1 + n) r
  ttr :: KnownNat n => TensorOf (2 + n) r -> TensorOf (2 + n) r
  ttr = ttranspose [1, 0]
  ttranspose :: KnownNat n => Permutation -> TensorOf n r -> TensorOf n r
  tflatten :: KnownNat n => TensorOf n r -> TensorOf 1 r
  tflatten u = treshape (flattenShape $ tshape u) u
  treshape :: (KnownNat n, KnownNat m)
           => ShapeInt m -> TensorOf n r -> TensorOf m r
  tbuild :: forall m n. (KnownNat m, KnownNat n)
         => ShapeInt (m + n) -> (IndexOf m r -> TensorOf n r)
         -> TensorOf (m + n) r
  tbuild sh0 f0 =
    let buildSh :: KnownNat m1
                => ShapeInt m1 -> (IndexOf m1 r -> TensorOf n r)
                -> TensorOf (m1 + n) r
        buildSh ZS f = f ZI
        buildSh (k :$ sh) f = tbuild1 k (\i -> buildSh sh (\ix -> f (i :. ix)))
    in buildSh (takeShape @m @n sh0) f0
  tbuild1 :: KnownNat n  -- this form requires less type applications
          => Int -> (IntOf r -> TensorOf n r) -> TensorOf (1 + n) r
  tmap :: (KnownNat m, KnownNat n)
       => (TensorOf n r -> TensorOf n r)
       -> TensorOf (m + n) r -> TensorOf (m + n) r
  tmap f v = tbuild (tshape v) (\ix -> f (v ! ix))
  tmap1 :: KnownNat n
        => (TensorOf n r -> TensorOf n r)
        -> TensorOf (1 + n) r -> TensorOf (1 + n) r
  tmap1 f u = tbuild1 (tlength u) (\i -> f (u ! [i]))
  tmap0N :: KnownNat n
         => (TensorOf 0 r -> TensorOf 0 r) -> TensorOf n r -> TensorOf n r
  tmap0N f v = tbuild (tshape v) (\ix -> f $ v ! ix)
  tzipWith :: (KnownNat m, KnownNat n)
           => (TensorOf n r -> TensorOf n r -> TensorOf n r)
           -> TensorOf (m + n) r -> TensorOf (m + n) r -> TensorOf (m + n) r
  tzipWith f u v = tbuild (tshape v) (\ix -> f (u ! ix) (v ! ix))
  tzipWith1 :: KnownNat n
            => (TensorOf n r -> TensorOf n r -> TensorOf n r)
            -> TensorOf (1 + n) r -> TensorOf (1 + n) r -> TensorOf (1 + n) r
  tzipWith1 f u v = tbuild1 (tlength u) (\i -> f (u ! [i]) (v ! [i]))
  tzipWith0N :: KnownNat n
             => (TensorOf 0 r -> TensorOf 0 r -> TensorOf 0 r)
             -> TensorOf n r -> TensorOf n r -> TensorOf n r
  tzipWith0N f u v = tbuild (tshape v) (\ix -> f (u ! ix) (v ! ix))
  tgather :: (KnownNat m, KnownNat n, KnownNat p)
          => ShapeInt (m + n) -> TensorOf (p + n) r
          -> (IndexOf m r -> IndexOf p r)
          -> TensorOf (m + n) r
  tgather1 :: (KnownNat n, KnownNat p)
           => Int -> TensorOf (p + n) r
           -> (IntOf r -> IndexOf p r)
           -> TensorOf (1 + n) r
  tgather1 k v f = tgather @r @1 (k :$ dropShape (tshape v)) v
                                 (\(i :. ZI) -> f i)

  tscalar :: r -> TensorOf 0 r
  tunScalar :: TensorOf 0 r -> r


  -- ** No serviceable parts beyond this point ** --

  -- Needed to avoid Num (TensorOf n r) constraints all over the place
  -- and also wrong shape in @0@ with ranked (not shaped) tensors.
  tzero :: KnownNat n
        => ShapeInt n -> TensorOf n r
  tzero sh = tkonst0N sh 0
  tsumOfList :: KnownNat n
             => [TensorOf n r] -> TensorOf n r  -- TODO: declare nonempty
  default tsumOfList
    :: Num (TensorOf n r)
    => [TensorOf n r] -> TensorOf n r
  tsumOfList = sum
  tmult :: KnownNat n
        => TensorOf n r -> TensorOf n r -> TensorOf n r
  default tmult
    :: Num (TensorOf n r)
    => TensorOf n r -> TensorOf n r -> TensorOf n r
  tmult = (*)
  tscaleByScalar :: KnownNat n => r -> TensorOf n r -> TensorOf n r
  tscaleByScalar s v = v `tmult` tkonst0N (tshape v) (tscalar s)
  tsumIn :: KnownNat n => TensorOf (1 + n) r -> TensorOf n r
  tsumIn = tsum . ttranspose [1, 0]
    -- TODO: generalize, replace by stride analysis, etc.
  tdot1In :: TensorOf 2 r -> TensorOf 2 r -> TensorOf 1 r
  tdot1In t u = tsum (ttranspose [1, 0] (t `tmult` u))
    -- TODO: generalize, replace by stride analysis, etc.

  -- The primal/dual distinction
  type Primal r
  type DualOf (n :: Nat) r
  tconst :: KnownNat n => OR.Array n (Value r) -> TensorOf n r
  tconstant :: KnownNat n => TensorOf n (Primal r) -> TensorOf n r
  tscale0 :: Primal r -> r -> r
  tprimalPart :: KnownNat n
              => TensorOf n r -> TensorOf n (Primal r)
  tdualPart :: KnownNat n
            => TensorOf n r -> DualOf n r
  tD :: KnownNat n => TensorOf n (Primal r) -> DualOf n r -> TensorOf n r
  tScale :: KnownNat n => TensorOf n (Primal r) -> DualOf n r -> DualOf n r
  -- TODO: we'd probably also need dZero, dIndex0 and all others;
  -- basically DualOf a needs to have IsPrimal and HasRanks instances
  -- (and HasInputs?)
  -- TODO: if DualOf is supposed to be user-visible, we needed
  -- a better name for it; TangentOf? CotangentOf? SecondaryOf?

  -- Operations for delayed let bindings creation
  tregister :: KnownNat n
            => TensorOf n r -> [(AstVarId, DTensorOf r)]
            -> ([(AstVarId, DTensorOf r)], TensorOf n r)
  tregister r l = (l, r)
  tletWrap :: ADShare (Value r) -> TensorOf n r -> TensorOf n r
  tletWrap _l u = u

  -- Conversions
  tfromD :: KnownNat n
         => DTensorOf r -> TensorOf n r
  dfromR :: KnownNat n
         => TensorOf n r -> DTensorOf r

class DomainsTensor r where
  daddR :: forall n. KnownNat n
        => TensorOf n r -> DTensorOf r -> DTensorOf r
  dshape :: DTensorOf r -> [Int]
  type DomainsOf r
  tletDomains :: DomainsOf r
              -> (DomainsOf r -> TensorOf n r)
              -> TensorOf n r
  tletDomains a f = f a
  dmkDomains :: Domains r -> DomainsOf r
  default dmkDomains
    :: Domains r ~ DomainsOf r
    => Domains r -> DomainsOf r
  dmkDomains = id
  dlet :: KnownNat n
       => TensorOf n r -> (TensorOf n r -> DomainsOf r)
       -> DomainsOf r
  dlet a f = f a


-- * The giga-constraint

type Many (f :: Type -> Constraint) r = (f (TensorOf 0 r), f (TensorOf 1 r), f (TensorOf 2 r), f (TensorOf 3 r), f (TensorOf 4 r), f (TensorOf 5 r), f (TensorOf 6 r), f (TensorOf 7 r), f (TensorOf 8 r), f (TensorOf 9 r), f (TensorOf 10 r), f (TensorOf 11 r), f (TensorOf 12 r))

type ADReady r =
  ( Tensor r, Tensor (Primal r)
  , Show r, Numeric (Value r), RealFloat (Value r), Scalar r ~ r
  , IfB r, IfB (IntOf r), Many IfB r, Many IfB (Primal r)
  , EqB r, EqB (IntOf r), Many EqB r, Many EqB (Primal r)
  , OrdB r, OrdB (IntOf r), Many OrdB r, Many OrdB (Primal r)
  , Boolean (BooleanOf r)
  , ( BooleanOf r ~ BooleanOf (TensorOf 0 r)
    , BooleanOf r ~ BooleanOf (TensorOf 1 r)
    , BooleanOf r ~ BooleanOf (TensorOf 2 r)
    , BooleanOf r ~ BooleanOf (TensorOf 3 r)
    , BooleanOf r ~ BooleanOf (TensorOf 4 r)
    , BooleanOf r ~ BooleanOf (TensorOf 5 r)
    , BooleanOf r ~ BooleanOf (TensorOf 6 r)
    , BooleanOf r ~ BooleanOf (TensorOf 7 r)
    , BooleanOf r ~ BooleanOf (TensorOf 8 r)
    , BooleanOf r ~ BooleanOf (TensorOf 9 r)
    , BooleanOf r ~ BooleanOf (TensorOf 10 r)
    , BooleanOf r ~ BooleanOf (TensorOf 11 r)
    , BooleanOf r ~ BooleanOf (TensorOf 12 r) )
  , ( BooleanOf r ~ BooleanOf (TensorOf 0 (Primal r))
    , BooleanOf r ~ BooleanOf (TensorOf 1 (Primal r))
    , BooleanOf r ~ BooleanOf (TensorOf 2 (Primal r))
    , BooleanOf r ~ BooleanOf (TensorOf 3 (Primal r))
    , BooleanOf r ~ BooleanOf (TensorOf 4 (Primal r))
    , BooleanOf r ~ BooleanOf (TensorOf 5 (Primal r))
    , BooleanOf r ~ BooleanOf (TensorOf 6 (Primal r))
    , BooleanOf r ~ BooleanOf (TensorOf 7 (Primal r))
    , BooleanOf r ~ BooleanOf (TensorOf 8 (Primal r))
    , BooleanOf r ~ BooleanOf (TensorOf 9 (Primal r))
    , BooleanOf r ~ BooleanOf (TensorOf 10 (Primal r))
    , BooleanOf r ~ BooleanOf (TensorOf 11 (Primal r))
    , BooleanOf r ~ BooleanOf (TensorOf 12 (Primal r)) )
  , BooleanOf r ~ BooleanOf (IntOf r)  -- placing this last gives better errors
  )
  -- any of the @BooleanOf r ~ ...@ lines above breaks GHC <= 9.0.2


-- * Tensor class instances for concrete arrays

instance Tensor Double where
  type Ranked Double = Flip OR.Array Double
  type IntOf Double = CInt
  tshape = tshapeR . runFlip
  tminIndex0 = tminIndexR . runFlip
  tmaxIndex0 = tmaxIndexR . runFlip
  tfloor = floor . tunScalar
  tindex v ix = Flip $ tindexZR (runFlip v) ix
  tsum = Flip . tsumR . runFlip
  tsum0 = tscalar . tsum0R . runFlip
  tdot0 u v = tscalar $ tdot0R (runFlip u) (runFlip v)
  tscatter sh t f = Flip $ tscatterZR sh (runFlip t) f
  tscatter1 sh t f = Flip $ tscatterZ1R sh (runFlip t) f
  tfromList = Flip . tfromListR . map runFlip
  tfromList0N sh = Flip . tfromList0NR sh
  tfromVector = Flip . tfromVectorR . V.map runFlip
  tfromVector0N sh = Flip . tfromVector0NR sh
  tkonst k = Flip . tkonstR k . runFlip
  tkonst0N sh = Flip . tkonst0NR sh . tunScalar
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
  tscalar = Flip . tscalarR
  tunScalar = tunScalarR . runFlip
  tscaleByScalar s v = Flip $ tscaleByScalarR s (runFlip v)
  tsumIn = Flip . tsumInR . runFlip
  tdot1In u v = Flip $ tdot1InR (runFlip u) (runFlip v)
  type Primal Double = Double
  type DualOf n Double = ()
  tconst = Flip
  tconstant = id
  tscale0 r d = r * d
  tprimalPart = id
  tdualPart _ = ()
  tD u _ = u
  tScale _ _ = ()
  tfromD = Flip . Data.Array.Convert.convert
  dfromR = Data.Array.Convert.convert . runFlip

instance DomainsTensor Double where
  daddR r d = if isTensorDummy d then dfromR r else dfromR r + d
  dshape = OD.shapeL
  type DomainsOf Double = Domains Double

instance Tensor Float where
  type Ranked Float = Flip OR.Array Float
  type IntOf Float = CInt
  tshape = tshapeR . runFlip
  tminIndex0 = tminIndexR . runFlip
  tmaxIndex0 = tmaxIndexR . runFlip
  tfloor = floor . tunScalar
  tindex v ix = Flip $ tindexZR (runFlip v) ix
  tsum = Flip . tsumR . runFlip
  tsum0 = tscalar . tsum0R . runFlip
  tdot0 u v = tscalar $ tdot0R (runFlip u) (runFlip v)
  tscatter sh t f = Flip $ tscatterZR sh (runFlip t) f
  tscatter1 sh t f = Flip $ tscatterZ1R sh (runFlip t) f
  tfromList = Flip . tfromListR . map runFlip
  tfromList0N sh = Flip . tfromList0NR sh
  tfromVector = Flip . tfromVectorR . V.map runFlip
  tfromVector0N sh = Flip . tfromVector0NR sh
  tkonst k = Flip . tkonstR k . runFlip
  tkonst0N sh = Flip . tkonst0NR sh . tunScalar
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
  tscalar = Flip . tscalarR
  tunScalar = tunScalarR . runFlip
  tscaleByScalar s v = Flip $ tscaleByScalarR s (runFlip v)
  tsumIn = Flip . tsumInR . runFlip
  tdot1In u v = Flip $ tdot1InR (runFlip u) (runFlip v)
  type Primal Float = Float
  type DualOf n Float = ()
  tconst = Flip
  tconstant = id
  tscale0 r d = r * d
  tprimalPart = id
  tdualPart _ = ()
  tD u _ = u
  tScale _ _ = ()
  tfromD = Flip . Data.Array.Convert.convert
  dfromR = Data.Array.Convert.convert . runFlip

instance DomainsTensor Float where
  daddR r d = if isTensorDummy d then dfromR r else dfromR r + d
  dshape = OD.shapeL
  type DomainsOf Float = Domains Float

{- TODO: requires IncoherentInstances no matter what pragma I stick in
-- A special case, because for @Double@ we have faster @randomVals@,
-- though the quality of randomness is worse (going through a single @Int@).
instance {-# OVERLAPS #-} {-# OVERLAPPING #-}
         KnownNat n
         => AdaptableDomains (OR.Array n Double) where
  type Scalar (OR.Array n Double) = Double
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

instance ( Numeric r, KnownNat n, Tensor r, DynamicTensor r, DomainsCollection r
         , Ranked r ~ Flip OR.Array r, DTensorOf r ~ OD.Array r )
         => AdaptableDomains (OR.Array n r) where
  type Scalar (OR.Array n r) = r
  type Value (OR.Array n r) = OR.Array n r
  toDomains a = mkDoms emptyDoms0 (fromListDoms [Data.Array.Convert.convert a])
  fromDomains aInit params = case unconsR params of
    Just (a, rest) ->
      Just (runFlip $ ttoRankedOrDummy (tshape $ Flip aInit) a, rest)
    Nothing -> Nothing
  nParams _ = 1
  nScalars = OR.size

instance ( Numeric r, KnownNat n, Tensor r, DynamicTensor r, DomainsCollection r
         , Ranked r ~ Flip OR.Array r )
         => AdaptableDomains (Flip OR.Array r n) where
  type Scalar (Flip OR.Array r n) = r
  type Value (Flip OR.Array r n) = OR.Array n r
  toDomains a = mkDoms emptyDoms0 (fromListDoms [dfromR a])
  fromDomains aInit params = case unconsR params of
    Just (a, rest) ->
      Just (ttoRankedOrDummy (tshape $ Flip aInit) a, rest)
    Nothing -> Nothing
  nParams _ = 1
  nScalars = OR.size . runFlip

instance KnownNat n
         => RandomDomains (OR.Array n r) where
  randomVals range g =
    let createRandomVector n seed =
          LA.scale (2 * range)
          $ V.fromListN n (randoms seed) - LA.scalar 0.5
        (g1, g2) = split g
        arr = OR.fromVector undefined
              $ createRandomVector (OR.size undefined) g1  -- TODO
    in (arr, g2)

instance AdaptableDomains (OD.Array r) where
  type Scalar (OD.Array r) = r
  type Value (OD.Array r) = OD.Array r
  toDomains = undefined
  fromDomains = undefined
  nParams = undefined
  nScalars = undefined

{- These instances are increasingly breaking stuff, so disabled:

-- A stub just to type-check and rewrite away before any computation
-- takes place. Also many others below.
instance Eq r => Eq (a -> r) where  -- embarrassing

instance Ord r => Ord (a -> r) where

instance Num r => Num (a -> r) where

instance Enum (a -> r) where

instance (Enum (a -> r), Real r) => Integral (a -> r) where

instance Fractional r => Fractional (a -> r) where

instance Floating r => Floating (a -> r) where

instance Real r => Real (a -> r) where

instance RealFrac r => RealFrac (a -> r) where

instance RealFloat r => RealFloat (a -> r) where

type instance BooleanOf (ORB.Array n (z -> a)) = z -> BooleanOf a

-- A stub instance for experiments with stored functions
instance Tensor r
         => Tensor (a -> r) where
  type TensorOf n (a -> r) = ORB.Array n (a -> r)
  type IntOf (a -> r) = a -> IntOf r
  tshape = undefined
  tminIndex = undefined
  tmaxIndex = undefined
  tfloor = undefined
  tindex = undefined
  tsum = undefined
  tfromIndex0 = undefined
  tfromList = undefined
  tfromVector = undefined
  tkonst = undefined
  tappend = undefined
  tslice = undefined
  treverse = undefined
  ttranspose = undefined
  treshape = undefined
  tbuild1 = undefined
  tscalar = ORB.scalar
  tunScalar = ORB.unScalar
  type ScalarOf (a -> r) = ScalarOf r
  tconst = tconst
-}
