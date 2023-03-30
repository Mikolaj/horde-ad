{-# LANGUAGE AllowAmbiguousTypes, OverloadedLists #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Dual numbers and various operations on them, arithmetic and related
-- to tensors (vectors, matrices and others). This is a part of
-- the high-level API of the horde-ad library, defined using the mid-level
-- (and safely impure) API in "HordeAd.Core.DualClass". The other part
-- of the high-level API is in "HordeAd.Core.Engine".
module HordeAd.Core.TensorClass
  ( IndexOf, ShapeInt, Tensor(..), ADReady
  ) where

import Prelude

import qualified Data.Array.Convert
import qualified Data.Array.DynamicS as OD
import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import           Data.Boolean
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat, type (+))
import           Numeric.LinearAlgebra (Numeric)

import HordeAd.Core.SizedIndex
import HordeAd.Internal.TensorOps

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

-- TODO: when we have several times more operations, split into
-- Array (Container) and Tensor (Numeric), with the latter containing the few
-- Ord and Num operations and numeric superclasses.
-- | The superclasses indicate that it's not only a container array,
-- but also a mathematical tensor, sporting numeric operations.
class (Num r, Num (TensorOf 0 r), Num (TensorOf 1 r), Integral (IntOf r))
      => Tensor r where
  type TensorOf (n :: Nat) r = result | result -> n r
  type IntOf r

  tlet :: KnownNat n
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
    :: (IntOf r ~ Int, RealFrac r) => TensorOf 0 r -> IntOf r
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
  tdot0 t u = tsum (tflatten t * tflatten u)
  tmatmul1 :: TensorOf 2 r -> TensorOf 1 r -> TensorOf 1 r
  tmatmul1 m v = tbuild1 (tlength m) (\i -> tdot0 v (m ! [i]))
-- how to generalize (#69)? these equivalent definitions generalize differently:
-- tmatmul1 m v = tbuild1 (tlength m) (\i -> tsum (v * m ! [i]))
-- tmatmul1 m v = tflatten $ tmap1 (tkonst 1 . tdot0 v) m
  tmatmul2 :: TensorOf 2 r -> TensorOf 2 r -> TensorOf 2 r
  tmatmul2 m1 m2 = tmap1 (tmatmul1 (ttr m2)) m1
  tminimum :: KnownNat n => TensorOf n r -> TensorOf 0 r
  tminimum t = t ! tminIndex t
  tmaximum :: KnownNat n => TensorOf n r -> TensorOf 0 r
  tmaximum t = t ! tmaxIndex t
  tfromIndex0 :: IntOf r -> TensorOf 0 r
  default tfromIndex0  -- the more narrow type rules out Ast
    :: IntOf r ~ Int => IntOf r -> TensorOf 0 r
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
  tadd :: KnownNat n
       => TensorOf n r -> TensorOf n r -> TensorOf n r
  default tadd
    :: Num (TensorOf n r)
    => TensorOf n r -> TensorOf n r -> TensorOf n r
  tadd = (+)
  tmult :: KnownNat n
        => TensorOf n r -> TensorOf n r -> TensorOf n r
  default tmult
    :: Num (TensorOf n r)
    => TensorOf n r -> TensorOf n r -> TensorOf n r
  tmult = (*)
  tscaleByScalar :: KnownNat n => r -> TensorOf n r -> TensorOf n r
  tscaleByScalar s v = v `tmult` tkonst0N (tshape v) (tscalar s)

  -- The primal/dual distinction
  type ScalarOf r
  type Primal r
  type DualOf (n :: Nat) r
  tconst :: KnownNat n => OR.Array n (ScalarOf r) -> TensorOf n r
  tconstant :: KnownNat n => TensorOf n (Primal r) -> TensorOf n r
  tscale0 :: Primal r -> r -> r
  tprimalPart :: TensorOf n r -> TensorOf n (Primal r)
  tdualPart :: TensorOf n r -> DualOf n r
  tD :: KnownNat n => TensorOf n (Primal r) -> DualOf n r -> TensorOf n r
  tScale :: KnownNat n => TensorOf n (Primal r) -> DualOf n r -> DualOf n r
  -- TODO: we'd probably also need dZero, dIndex0 and all others;
  -- basically DualOf a needs to have IsPrimal and HasRanks instances
  -- (and HasInputs?)
  -- TODO: if DualOf is supposed to be user-visible, we needed
  -- a better name for it; TangentOf? CotangentOf? SecondaryOf?

  -- The untyped versions of the tensor, to put many ranks in one vector
  type DynamicTensor r = result | result -> r
  tdummyD :: DynamicTensor r
  tisDummyD :: DynamicTensor r -> Bool
  taddD :: DynamicTensor r -> DynamicTensor r -> DynamicTensor r
  tshapeD :: DynamicTensor r -> [Int]
  tfromR :: KnownNat n
         => TensorOf n r -> DynamicTensor r
  tfromD :: KnownNat n
         => DynamicTensor r -> TensorOf n r

type ADReady r =
  ( Tensor r, Tensor (Primal r), Show r, RealFloat r
  , RealFloat (Primal r), Numeric (ScalarOf r), RealFloat (ScalarOf r)
  , ( RealFloat (TensorOf 0 r), RealFloat (TensorOf 1 r)
    , RealFloat (TensorOf 2 r), RealFloat (TensorOf 3 r)
    , RealFloat (TensorOf 4 r), RealFloat (TensorOf 5 r)
    , RealFloat (TensorOf 6 r), RealFloat (TensorOf 7 r)
    , RealFloat (TensorOf 8 r), RealFloat (TensorOf 9 r)
    , RealFloat (TensorOf 10 r), RealFloat (TensorOf 11 r)
    , RealFloat (TensorOf 12 r) )
  , ( RealFloat (TensorOf 0 (Primal r)), RealFloat (TensorOf 1 (Primal r))
    , RealFloat (TensorOf 2 (Primal r)), RealFloat (TensorOf 3 (Primal r))
    , RealFloat (TensorOf 4 (Primal r)), RealFloat (TensorOf 5 (Primal r))
    , RealFloat (TensorOf 6 (Primal r)), RealFloat (TensorOf 7 (Primal r))
    , RealFloat (TensorOf 8 (Primal r)), RealFloat (TensorOf 9 (Primal r))
    , RealFloat (TensorOf 10 (Primal r)), RealFloat (TensorOf 11 (Primal r))
    , RealFloat (TensorOf 12 (Primal r)) )
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
  , IfB r, IfB (IntOf r)
  , ( IfB (TensorOf 0 r), IfB (TensorOf 1 r), IfB (TensorOf 2 r)
    , IfB (TensorOf 3 r), IfB (TensorOf 4 r), IfB (TensorOf 5 r)
    , IfB (TensorOf 6 r), IfB (TensorOf 7 r), IfB (TensorOf 8 r)
    , IfB (TensorOf 9 r), IfB (TensorOf 10 r), IfB (TensorOf 11 r)
    , IfB (TensorOf 12 r) )
  , ( IfB (TensorOf 0 (Primal r)), IfB (TensorOf 1 (Primal r)), IfB (TensorOf 2 (Primal r))
    , IfB (TensorOf 3 (Primal r)), IfB (TensorOf 4 (Primal r)), IfB (TensorOf 5 (Primal r))
    , IfB (TensorOf 6 (Primal r)), IfB (TensorOf 7 (Primal r)), IfB (TensorOf 8 (Primal r))
    , IfB (TensorOf 9 (Primal r)), IfB (TensorOf 10 (Primal r)), IfB (TensorOf 11 (Primal r))
    , IfB (TensorOf 12 (Primal r)) )
  , EqB r, EqB (IntOf r)
  , ( EqB (TensorOf 0 r), EqB (TensorOf 1 r), EqB (TensorOf 2 r)
    , EqB (TensorOf 3 r), EqB (TensorOf 4 r), EqB (TensorOf 5 r)
    , EqB (TensorOf 6 r), EqB (TensorOf 7 r), EqB (TensorOf 8 r)
    , EqB (TensorOf 9 r), EqB (TensorOf 10 r), EqB (TensorOf 11 r)
    , EqB (TensorOf 12 r) )
  , ( EqB (TensorOf 0 (Primal r)), EqB (TensorOf 1 (Primal r)), EqB (TensorOf 2 (Primal r))
    , EqB (TensorOf 3 (Primal r)), EqB (TensorOf 4 (Primal r)), EqB (TensorOf 5 (Primal r))
    , EqB (TensorOf 6 (Primal r)), EqB (TensorOf 7 (Primal r)), EqB (TensorOf 8 (Primal r))
    , EqB (TensorOf 9 (Primal r)), EqB (TensorOf 10 (Primal r)), EqB (TensorOf 11 (Primal r))
    , EqB (TensorOf 12 (Primal r)) )
  , OrdB r, OrdB (IntOf r)
  , ( OrdB (TensorOf 0 r), OrdB (TensorOf 1 r), OrdB (TensorOf 2 r)
    , OrdB (TensorOf 3 r), OrdB (TensorOf 4 r), OrdB (TensorOf 5 r)
    , OrdB (TensorOf 6 r), OrdB (TensorOf 7 r), OrdB (TensorOf 8 r)
    , OrdB (TensorOf 9 r), OrdB (TensorOf 10 r), OrdB (TensorOf 11 r)
    , OrdB (TensorOf 12 r) )
  , ( OrdB (TensorOf 0 (Primal r)), OrdB (TensorOf 1 (Primal r)), OrdB (TensorOf 2 (Primal r))
    , OrdB (TensorOf 3 (Primal r)), OrdB (TensorOf 4 (Primal r)), OrdB (TensorOf 5 (Primal r))
    , OrdB (TensorOf 6 (Primal r)), OrdB (TensorOf 7 (Primal r)), OrdB (TensorOf 8 (Primal r))
    , OrdB (TensorOf 9 (Primal r)), OrdB (TensorOf 10 (Primal r)), OrdB (TensorOf 11 (Primal r))
    , OrdB (TensorOf 12 (Primal r)) )
  )
  -- any of the @BooleanOf r ~ ...@ lines above breaks GHC <= 9.0.2

-- * Tensor class instances for arrays

-- These instances are a faster way to get an objective function value.
-- However, they don't do vectorization, so won't work on GPU, ArrayFire, etc.
-- For vectorization, go through Ast and valueOnDomains.
instance Tensor Double where
  type TensorOf n Double = OR.Array n Double
  type IntOf Double = Int
  tshape = tshapeR
  tminIndex0 = tminIndexR
  tmaxIndex0 = tmaxIndexR
  tfloor = floor . tunScalar
  tindex = tindexZR
  tsum = tsumR
  tsum0 = tscalar . tsum0R
  tdot0 u v = tscalar $ tdot0R u v
  tscatter = tscatterZR
  tscatter1 = tscatterZ1R
  tfromList = tfromListR
  tfromList0N = tfromList0NR
  tfromVector = tfromVectorR
  tfromVector0N = tfromVector0NR
  tkonst = tkonstR
  tkonst0N sh = tkonst0NR sh . tunScalar
  tappend = tappendR
  tslice = tsliceR
  treverse = treverseR
  ttranspose = ttransposeR
  treshape = treshapeR
  tbuild = tbuildNR
  tbuild1 = tbuild1R
  tmap0N = tmap0NR
  tzipWith0N = tzipWith0NR
  tgather = tgatherZR
  tgather1 = tgatherZ1R
  tscalar = tscalarR
  tunScalar = tunScalarR
  tscaleByScalar = tscaleByScalarR
  type ScalarOf Double = Double
  type Primal Double = Double
  type DualOf n Double = ()
  tconst = id
  tconstant = id
  tscale0 r d = r * d
  tprimalPart = id
  tdualPart _ = ()
  tD u _ = u
  tScale _ _ = ()
  type DynamicTensor Double = OD.Array Double
  tdummyD = dummyTensor
  tisDummyD = isTensorDummy
  taddD = (+)
  tshapeD = OD.shapeL
  tfromR = Data.Array.Convert.convert
  tfromD = Data.Array.Convert.convert

instance Tensor Float where
  type TensorOf n Float = OR.Array n Float
  type IntOf Float = Int
  tshape = tshapeR
  tminIndex0 = tminIndexR
  tmaxIndex0 = tmaxIndexR
  tfloor = floor . tunScalar
  tindex = tindexZR
  tsum = tsumR
  tsum0 = tscalar . tsum0R
  tdot0 u v = tscalar $ tdot0R u v
  tscatter = tscatterZR
  tscatter1 = tscatterZ1R
  tfromList = tfromListR
  tfromList0N = tfromList0NR
  tfromVector = tfromVectorR
  tfromVector0N = tfromVector0NR
  tkonst = tkonstR
  tkonst0N sh = tkonst0NR sh . tunScalar
  tappend = tappendR
  tslice = tsliceR
  treverse = treverseR
  ttranspose = ttransposeR
  treshape = treshapeR
  tbuild = tbuildNR
  tbuild1 = tbuild1R
  tmap0N = tmap0NR
  tzipWith0N = tzipWith0NR
  tgather = tgatherZR
  tgather1 = tgatherZ1R
  tscalar = tscalarR
  tunScalar = tunScalarR
  tscaleByScalar = tscaleByScalarR
  type ScalarOf Float = Float
  type Primal Float = Float
  type DualOf n Float = ()
  tconst = id
  tconstant = id
  tscale0 r d = r * d
  tprimalPart = id
  tdualPart _ = ()
  tD u _ = u
  tScale _ _ = ()
  type DynamicTensor Float = OD.Array Float
  tdummyD = dummyTensor
  tisDummyD = isTensorDummy
  taddD = (+)
  tshapeD = OD.shapeL
  tfromR = Data.Array.Convert.convert
  tfromD = Data.Array.Convert.convert

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
