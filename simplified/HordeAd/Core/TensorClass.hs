{-# LANGUAGE AllowAmbiguousTypes, ConstraintKinds, DataKinds, FlexibleInstances,
             MultiParamTypeClasses, OverloadedLists, TypeFamilyDependencies,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Dual numbers and various operations on them, arithmetic and related
-- to tensors (vectors, matrices and others). This is a part of
-- the high-level API of the horde-ad library, defined using the mid-level
-- (and safely impure) API in "HordeAd.Core.DualClass". The other part
-- of the high-level API is in "HordeAd.Core.Engine".
module HordeAd.Core.TensorClass
  ( IndexOf, ShapeInt, Tensor(..), HasPrimal(..), ADReady
  , simplifyAst, interpretAst, AstVar(..), funToAstR, extendEnvR
  , ADModeAndNumTensor, scale1, relu1, reluLeaky1
  ) where

import Prelude

import qualified Data.Array.DynamicS as OT
import           Data.Array.Internal (valueOf)
import qualified Data.Array.Ranked as ORB
import qualified Data.Array.RankedS as OR
import           Data.Boolean
import qualified Data.Strict.IntMap as IM
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat, type (+))
import           Numeric.LinearAlgebra (Numeric, Vector)

import HordeAd.Core.Ast
import HordeAd.Core.AstSimplify
import HordeAd.Core.AstVectorize
import HordeAd.Core.DualClass
import HordeAd.Core.DualNumber hiding (build1)
import HordeAd.Core.SizedIndex
import HordeAd.Internal.SizedList
import HordeAd.Internal.TensorOps

-- * Tensor class definition and instances for arrays, ADVal and Ast

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
-- The @VectorNumeric@ superclass is for @IntOf@ and potential interoperability
-- (TODO: add coversions between VectorOf and TensorOf to facilitate this)
-- but all its operations have straightforwardly generalized analogues below.
-- Eventually, we'll remove @VectorNumeric@ or define it in terms of @Tensor@.
class ( RealFloat r, RealFloat (TensorOf 0 r), RealFloat (TensorOf 1 r)
      , Integral (IntOf r) )
      => Tensor r where
  type TensorOf (n :: Nat) r = result | result -> n r
  type IntOf r

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
  tminIndex0 :: TensorOf 1 r -> IntOf r
  tminIndex :: KnownNat n => TensorOf n r -> IndexOf n r
  tminIndex t = fromLinearIdx (fmap fromIntegral $ tshape t)
                              (tminIndex0 (tflatten t))
  tmaxIndex0 :: TensorOf 1 r -> IntOf r
  tmaxIndex :: KnownNat n => TensorOf n r -> IndexOf n r
  tmaxIndex t = fromLinearIdx (fmap fromIntegral $ tshape t)
                              (tmaxIndex0 (tflatten t))
  tfloor :: TensorOf 0 r -> IntOf r

  -- Typically scalar codomain, often tensor reduction
  -- (a number suffix in the name indicates the rank of codomain)
  tindex, (!) :: (KnownNat n, KnownNat m)
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

  -- Tensor codomain, often tensor construction, sometimes transformation
  -- (for these, suffix 1 doesn't mean codomain rank 1, but building up
  -- by one rank, and is omitted if a more general variant is not defined)
  tfromList :: KnownNat n => [TensorOf n r] -> TensorOf (1 + n) r
  tfromList0N :: KnownNat n => ShapeInt n -> [r] -> TensorOf n r
  tfromList0N sh = treshape sh . tfromList . map tscalar
  tfromVector :: KnownNat n
              => Data.Vector.Vector (TensorOf n r) -> TensorOf (1 + n) r
  tfromVector0N :: KnownNat n
                => ShapeInt n -> Data.Vector.Vector r -> TensorOf n r
  tfromVector0N sh = treshape sh . tfromVector . V.map tscalar
  tkonst :: KnownNat n => Int -> TensorOf n r -> TensorOf (1 + n) r
  tkonst0N :: KnownNat n => ShapeInt n -> TensorOf 0 r -> TensorOf n r
  tkonst0N sh = treshape sh . tkonst (sizeShape sh)
  tappend :: KnownNat n
          => TensorOf (1 + n) r -> TensorOf (1 + n) r -> TensorOf (1 + n) r
  tslice :: KnownNat n => Int -> Int -> TensorOf (1 + n) r -> TensorOf (1 + n) r
  treverse :: KnownNat n => TensorOf (1 + n) r -> TensorOf (1 + n) r
  ttr :: KnownNat n => TensorOf (2 + n) r -> TensorOf (2 + n) r
  ttr = ttranspose [1, 0]
  ttranspose :: KnownNat n => Permutation -> TensorOf n r -> TensorOf n r
  tflatten :: KnownNat n => TensorOf n r -> TensorOf 1 r
  tflatten u = treshape (flattenShape $ tshape u) u
  treshape :: (KnownNat m, KnownNat n)
           => ShapeInt m -> TensorOf n r -> TensorOf m r
  tbuild :: forall n m. (KnownNat n, KnownNat m)
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
  tgather1 :: (KnownNat p, KnownNat n)
           => Int -> TensorOf (p + n) r
           -> (IntOf r -> IndexOf p r)
           -> TensorOf (1 + n) r

  tscalar :: r -> TensorOf 0 r
  tunScalar :: TensorOf 0 r -> r

type ADReady r =
  ( Tensor r, HasPrimal r, Tensor (Primal r), Show r
  , Numeric (ScalarOf r), RealFloat (ScalarOf r)
  , ( RealFloat (TensorOf 2 r), RealFloat (TensorOf 3 r)
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
  tindex = tindexNR
  tsum = tsumR
  tsum0 = tscalar . tsum0R
  tdot0 u v = tscalar $ tdot0R u v
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
  tgather = tgatherNR
  tgather1 = tgather1R
  tscalar = tscalarR
  tunScalar = tunScalarR

instance Tensor Float where
  type TensorOf n Float = OR.Array n Float
  type IntOf Float = Int
  tshape = tshapeR
  tminIndex0 = tminIndexR
  tmaxIndex0 = tmaxIndexR
  tfloor = floor . tunScalar
  tindex = tindexNR
  tsum = tsumR
  tsum0 = tscalar . tsum0R
  tdot0 u v = tscalar $ tdot0R u v
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
  -- TODO: low priority: implement for speed and use for ADVal, too
  -- tmap = tmapR
  -- tmap0N = tmap0NR
  -- tzipWith = tzipWithR
  -- tzipWith0N = tzipWith0NR
  tgather = tgatherNR
  tgather1 = tgather1R
  tscalar = tscalarR
  tunScalar = tunScalarR

-- Not that this instance doesn't do vectorization. To enable it,
-- use the Ast instance, which vectorizes and finally interpret in ADVal.
-- In principle, this instance is only useful for comparative tests,
-- though for code without build/map/etc., it should be equivalent
-- to going via Ast.
instance ADModeAndNumTensor d r => Tensor (ADVal d r) where
  type TensorOf n (ADVal d r) = ADVal d (OR.Array n r)
  type IntOf (ADVal d r) = Int

  -- Here and elsewhere I can't use methods of the @r@ instance of @Tensor@
  -- (the one implemented as @OR.Array n r@). Therefore, I inline them
  -- manually. There is probably no solution to that (2 parameters to Tensor
  -- would solve this, but we'd need infinitely many instances
  -- for @ADVal d (OR.Array n r)@ and @OR.Array n r@). As a workaround,
  -- the methods are defined as calls to tensor functions provided elsewhere,
  -- so there is no code duplication.
  tshape = shape
  tminIndex0 (D u _) = tminIndexR u
  tmaxIndex0 (D u _) = tmaxIndexR u
  tfloor (D u _) = floor $ tunScalarR u

  tindex = indexZ  -- for simplicity, out of bounds indexing permitted
  tsum = sum'
  tsum0 = tscalar . sum0
  tdot0 u v = tscalar $ dot0 u v

  tfromList = fromList
  tfromList0N = fromList0N
  tfromVector = fromVector
  tfromVector0N = fromVector0N
  tkonst = konst
  tkonst0N sh = konst0N sh . unScalar
  tappend = append
  tslice = slice
  treverse = reverse'
  ttranspose = transpose
  treshape = reshape
  tbuild1 k f =
    let g i = let D u _ = f i in u
        h i = let D _ u' = f i in u'
    in dD (tbuild1R k g) (dBuild1 k h)
      -- uses the implementation that stores closures on tape to test against
      -- the elementwise implementation used by fallback from vectorizing Ast
  tgather = gatherNClosure  -- for simplicity, out of bounds indexing permitted
  tgather1 = gather1Closure

  tscalar = scalar
  tunScalar = unScalar

instance ( Numeric r, RealFloat r, RealFloat (Vector r)
         , Show r, Numeric r )  -- needed only to display errors properly
         => Tensor (Ast 0 r) where
  type TensorOf n (Ast 0 r) = Ast n r
  type IntOf (Ast 0 r) = AstInt r

  tshape = shapeAst
  tminIndex0 = AstMinIndex1
  tmaxIndex0 = AstMaxIndex1
  tfloor = AstIntFloor

  tindex = AstIndexZ
  tsum = AstSum
  tfromIndex0 = AstConstInt
    -- toInteger is not defined for Ast, hence a special implementation

  tfromList = AstFromList
  tfromList0N sh = AstReshape sh . AstFromList
  tfromVector = AstFromVector
  tfromVector0N sh = AstReshape sh . AstFromVector
  tkonst = AstKonst
  tappend = AstAppend
  tslice = AstSlice
  treverse = AstReverse
  ttranspose = AstTranspose
  treshape = AstReshape
  tbuild1 = astBuild1
  tgather sh t f = AstGatherN sh t (funToAstIndex f)  -- introduces new vars
  tgather1 k t f = AstGather1 k t (funToAstI f)  -- introduces new vars

  tscalar = id  -- Ast confuses the two ranks
  tunScalar = id

-- This is a vectorizing combinator that also simplifies
-- the terms touched during vectorization, but not any others.
-- Due to how the Ast instance of Tensor is defined above, vectorization
-- works bottom-up, which removes the need to backtrack in the vectorization
-- pass or repeat until a fixed point is reached.
-- This combinator also introduces new variable names.
astBuild1 :: (KnownNat n, Show r, Numeric r)
          => Int -> (AstInt r -> Ast n r) -> Ast (1 + n) r
astBuild1 k f = build1Vectorize k $ funToAstI f

instance ( Numeric r, RealFloat r, RealFloat (Vector r)
         , Show r, Numeric r )
         => Tensor (AstPrimalPart 0 r) where
  type TensorOf n (AstPrimalPart 0 r) = AstPrimalPart n r
  type IntOf (AstPrimalPart 0 r) = AstInt r

  tshape = shapeAst . unAstPrimalPart
  tminIndex0 = AstMinIndex1 . unAstPrimalPart
  tmaxIndex0 = AstMaxIndex1 . unAstPrimalPart
  tfloor = AstIntFloor . unAstPrimalPart

  tindex v ix = AstPrimalPart $ AstIndexZ (unAstPrimalPart v) ix
  tsum = AstPrimalPart . AstSum . unAstPrimalPart
  tfromIndex0 = AstPrimalPart . AstConstInt
    -- toInteger is not defined for Ast, hence a special implementation

  tfromList = AstPrimalPart . AstFromList . map unAstPrimalPart
  tfromList0N sh =
    AstPrimalPart . AstReshape sh . AstFromList . map unAstPrimalPart
  tfromVector = AstPrimalPart . AstFromVector . V.map unAstPrimalPart
  tfromVector0N sh =
    AstPrimalPart . AstReshape sh . AstFromVector . V.map unAstPrimalPart
  tkonst k = AstPrimalPart . AstKonst k . unAstPrimalPart
  tappend u v =
    AstPrimalPart $ AstAppend (unAstPrimalPart u) (unAstPrimalPart v)
  tslice i k = AstPrimalPart . AstSlice i k  . unAstPrimalPart
  treverse = AstPrimalPart . AstReverse . unAstPrimalPart
  ttranspose perm = AstPrimalPart . AstTranspose perm . unAstPrimalPart
  treshape sh = AstPrimalPart . AstReshape sh  . unAstPrimalPart
  tbuild1 k f = AstPrimalPart $ AstBuild1 k
                $ funToAstI  -- this introduces new variable names
                $ unAstPrimalPart . f
  tgather sh t f = AstPrimalPart $ AstGatherN sh (unAstPrimalPart t)
                   $ funToAstIndex f  -- this introduces new variable names
  tgather1 k t f = AstPrimalPart $ AstGather1 k (unAstPrimalPart t)
                   $ funToAstI f  -- this introduces new variable names

  tscalar = id
  tunScalar = id

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

-- * HasPrimal class and instances for all relevant types

-- We could accept any @RealFloat@ instead of @Primal a@, but then
-- we'd need to coerce, e.g., via realToFrac, which is risky and lossy.
-- Also, the stricter typing is likely to catch real errors most of the time,
-- not just sloppy omission ofs explicit coercions.
class HasPrimal r where
  type ScalarOf r
  type Primal r
  type DualOf (n :: Nat) r
  tconst :: KnownNat n => OR.Array n (ScalarOf r) -> TensorOf n r
  tconstant :: KnownNat n => TensorOf n (Primal r) -> TensorOf n r
  tprimalPart :: TensorOf n r -> TensorOf n (Primal r)
  tdualPart :: TensorOf n r -> DualOf n r
  tD :: KnownNat n => TensorOf n (Primal r) -> DualOf n r -> TensorOf n r
  -- TODO: we'd probably also need dZero, dIndex0 and all others;
  -- basically DualOf a needs to have IsPrimal and HasRanks instances
  -- (and HasInputs?)
  -- TODO: if DualOf is supposed to be user-visible, we needed
  -- a better name for it; TangentOf? CotangentOf? SecondaryOf?

instance HasPrimal Double where
  type ScalarOf Double = Double
  type Primal Double = Double
  type DualOf n Double = ()
  tconst = id
  tconstant = id
  tprimalPart = id
  tdualPart _ = ()
  tD u _ = u

instance HasPrimal Float where
  type ScalarOf Float = Float
  type Primal Float = Float
  type DualOf n Float = ()
  tconst = id
  tconstant = id
  tprimalPart = id
  tdualPart _ = ()
  tD u _ = u

instance ADModeAndNumTensor d r => HasPrimal (ADVal d r) where
  type ScalarOf (ADVal d r) = r
  type Primal (ADVal d r) = r
  type DualOf n (ADVal d r) = Dual d (OR.Array n r)
  tconst t = dD t dZero
  tconstant t = dD (toArray t) dZero
  tprimalPart (D u _) = fromArray u
  tdualPart (D _ u') = u'
  tD u = dD (toArray u)

type ADModeAndNumTensor (d :: ADMode) r =
  ( ADModeAndNum d r
  , Tensor r
  , TensorOf 1 r ~ OR.Array 1 r
  , IntOf r ~ Int
  , TensorIsArray r
  )

class TensorIsArray r where
  toArray :: TensorOf n r -> OR.Array n r
  fromArray :: OR.Array n r -> TensorOf n r

instance TensorIsArray Double where
  toArray = id
  fromArray = id

instance TensorIsArray Float where
  toArray = id
  fromArray = id

instance HasPrimal (Ast 0 r) where
  type ScalarOf (Ast 0 r) = r
  type Primal (Ast 0 r) = AstPrimalPart 0 r
  type DualOf n (Ast 0 r) = ()  -- TODO: data AstDualPart: dScale, dAdd, dkonst1
  tconst = AstConst
  tconstant = AstConstant
  tprimalPart = AstPrimalPart
  tdualPart = error "TODO"
  tD = error "TODO"

instance HasPrimal (AstPrimalPart 0 r) where
  type ScalarOf (AstPrimalPart 0 r) = r
  type Primal (AstPrimalPart 0 r) = AstPrimalPart 0 r
  type DualOf n (AstPrimalPart 0 r) = ()
  tconst = AstPrimalPart . AstConst
  tconstant = AstPrimalPart . AstConstant
  tprimalPart = id
  tdualPart = error "TODO"
  tD = error "TODO"


-- * Odds and ends

scale1 :: (ADReady r, KnownNat n, Num (TensorOf n r))
       => TensorOf n (Primal r) -> TensorOf n r -> TensorOf n r
scale1 a d = tconstant a * d

relu1, reluLeaky1
  :: forall n r. (ADReady r, KnownNat n, Num (TensorOf n r))
  => TensorOf n r -> TensorOf n r
relu1 v =
  let oneIfGtZero = tmap0N (\x -> ifB (x >* 0) 1 0)
                           (tprimalPart v)
  in scale1 oneIfGtZero v

reluLeaky1 v =
  let oneIfGtZero = tmap0N (\x -> ifB (x >* 0) 1 0.01)
                           (tprimalPart v)
  in scale1 oneIfGtZero v


-- * ADVal combinators generalizing ranked tensor operations

shape :: KnownNat n => ADVal d (OR.Array n r) -> ShapeInt n
shape (D u _) = tshapeR u

-- TODO: speed up by using tindex0R and dIndex0 if the codomain is 0
-- and dD (u `tindex1R` ix) (dIndex1 u' ix (tlengthR u)) if only outermost
-- dimension affected.
--
-- First index is for outermost dimension; empty index means identity,
-- index ouf of bounds produces zero (but beware of vectorization).
indexZ :: forall m n d r. (ADModeAndNumTensor d r, KnownNat m, KnownNat n)
       => ADVal d (OR.Array (m + n) r) -> IndexInt m
       -> ADVal d (OR.Array n r)
indexZ (D u u') ix =
  let sh = tshapeR u
  in if ixInBounds (indexToList ix) (shapeToList sh)
     then dD (tindexNR u ix) (dIndexN u' ix sh)
     else dD (tkonst0NR (dropShape @m sh) 0) dZero

sum' :: (ADModeAndNumTensor d r, KnownNat n)
     => ADVal d (OR.Array (1 + n) r) -> ADVal d (OR.Array n r)
sum' (D u u') = dD (tsumR u) (dSum1 (tlengthR u) u')

sum0 :: (ADModeAndNumTensor d r, KnownNat n)
     => ADVal d (OR.Array n r) -> ADVal d r
sum0 (D u u') = dD (tsum0R u) (dSum0 (tshapeR u) u')

dot0 :: (ADModeAndNumTensor d r, KnownNat n)
     => ADVal d (OR.Array n r) -> ADVal d (OR.Array n r) -> ADVal d r
dot0 (D u u') (D v v') = dD (tdot0R u v)
                            (dAdd (dDot0 v u') (dDot0 u v'))

fromList :: (ADModeAndNumTensor d r, KnownNat n)
         => [ADVal d (OR.Array n r)]
         -> ADVal d (OR.Array (1 + n) r)
fromList lu =
  -- TODO: if lu is empty, crash if n =\ 0 or use List.NonEmpty.
  dD (tfromListR $ map (\(D u _) -> u) lu)
     (dFromList1 $ map (\(D _ u') -> u') lu)

fromList0N :: (ADModeAndNumTensor d r, KnownNat n)
           => ShapeInt n -> [ADVal d r]
           -> ADVal d (OR.Array n r)
fromList0N sh l =
  dD (tfromList0NR sh $ map (\(D u _) -> u) l)  -- I hope this fuses
     (dFromList01 sh $ map (\(D _ u') -> u') l)

fromVector :: (ADModeAndNumTensor d r, KnownNat n)
           => Data.Vector.Vector (ADVal d (OR.Array n r))
           -> ADVal d (OR.Array (1 + n) r)
fromVector lu =
  dD (tfromVectorR $ V.map (\(D u _) -> u) lu)
     (dFromVector1 $ V.map (\(D _ u') -> u') lu)

fromVector0N :: (ADModeAndNumTensor d r, KnownNat n)
             => ShapeInt n -> Data.Vector.Vector (ADVal d r)
             -> ADVal d (OR.Array n r)
fromVector0N sh l =
  dD (tfromVector0NR sh $ V.convert $ V.map (\(D u _) -> u) l)  -- hope it fuses
     (dFromVector01 sh $ V.map (\(D _ u') -> u') l)

konst :: (ADModeAndNumTensor d r, KnownNat n)
      => Int -> ADVal d (OR.Array n r) -> ADVal d (OR.Array (1 + n) r)
konst k (D u u') = dD (tkonstR k u) (dKonst1 k u')

konst0N :: (ADModeAndNumTensor d r, KnownNat n)
        => ShapeInt n -> ADVal d r -> ADVal d (OR.Array n r)
konst0N sh (D u u') = dD (tkonst0NR sh u) (dKonst01 sh u')

append :: (ADModeAndNumTensor d r, KnownNat n)
       => ADVal d (OR.Array (1 + n) r) -> ADVal d (OR.Array (1 + n) r)
       -> ADVal d (OR.Array (1 + n) r)
append (D u u') (D v v') = dD (tappendR u v) (dAppend1 u' (tlengthR u) v')

slice :: (ADModeAndNumTensor d r, KnownNat n)
      => Int -> Int -> ADVal d (OR.Array (1 + n) r)
      -> ADVal d (OR.Array (1 + n) r)
slice i k (D u u') = dD (tsliceR i k u) (dSlice1 i k u' (tlengthR u))

reverse' :: (ADModeAndNumTensor d r, KnownNat n)
         => ADVal d (OR.Array (1 + n) r) -> ADVal d (OR.Array (1 + n) r)
reverse' (D u u') = dD (treverseR u) (dReverse1 u')

transpose :: (ADModeAndNumTensor d r, KnownNat n)
          => Permutation -> ADVal d (OR.Array n r) -> ADVal d (OR.Array n r)
transpose perm (D u u') = dD (ttransposeR perm u) (dTranspose1 perm u')

reshape :: (ADModeAndNumTensor d r, KnownNat m, KnownNat n)
        => ShapeInt m -> ADVal d (OR.Array n r) -> ADVal d (OR.Array m r)
reshape sh (D u u') = dD (treshapeR sh u) (dReshape1 (tshapeR u) sh u')

-- The element-wise (POPL) version, but only one rank at a time.
build1 :: (ADModeAndNumTensor d r, KnownNat n)
       => Int -> (Int -> ADVal d (OR.Array n r))
       -> ADVal d (OR.Array (1 + n) r)
build1 k f = fromList $ map f [0 .. k - 1]

-- Note that if any index is out of bounds, the result of that particular
-- projection is defined and is 0 (but beware of vectorization).
gatherNClosure :: (ADModeAndNumTensor d r, KnownNat m, KnownNat p, KnownNat n)
               => ShapeInt (m + n) -> ADVal d (OR.Array (p + n) r)
               -> (IndexInt m -> IndexInt p)
               -> ADVal d (OR.Array (m + n) r)
gatherNClosure sh (D u u') f =
  dD (tgatherZR sh u f) (dGatherN f (tshapeR u) u' sh)

-- Note that if any index is out of bounds, the result of that particular
-- projection is defined and is 0 (but beware of vectorization).
gather1Closure :: (ADModeAndNumTensor d r, KnownNat p, KnownNat n)
               => Int -> ADVal d (OR.Array (p + n) r)
               -> (Int -> IndexInt p)
               -> ADVal d (OR.Array (1 + n) r)
gather1Closure k (D u u') f = dD (tgatherZ1R k u f) (dGather1 f (tshapeR u) u' k)

scalar :: ADModeAndNumTensor d r => ADVal d r -> ADVal d (OR.Array 0 r)
scalar (D u u') = dD (OR.scalar u) (dScalar1 u')

unScalar :: ADModeAndNumTensor d r => ADVal d (OR.Array 0 r) -> ADVal d r
unScalar (D u u') = dD (OR.unScalar u) (dUnScalar0 u')


-- * Interpretation of Ast in ADVal

-- We are very close to being able to interpret Ast in any Tensor
-- and HasPrimal instance.
-- However, this proves impossible, because we'd need to adorn interpretAst
-- with constraints like RealFloat (Tensor n r) for all @n@ in use,
-- which includes, e.g., @m + p@, where @m@ and @p@ are not mentioned
-- nor can be deduced from the signature of interpretAst.
-- I don't know if we could hack around by creating and explicitly
-- passing the relevant dictionaries. Users of the library may find
-- similar problems in large enough programs, so developing a technique
-- for that would be useful.
-- For now, we interpret only in the concrete ADVal instance,
-- which is the only interpretation needed for anything apart from tests.

type AstEnv (d :: ADMode) r = IM.IntMap (AstVar (ADVal d (OT.Array r)))

data AstVar a =
    AstVarR a
  | AstVarI Int
 deriving Show

extendEnvR :: ADModeAndNumTensor d r
           => AstVarName (OR.Array n r) -> ADVal d (OR.Array n r)
           -> AstEnv d r -> AstEnv d r
extendEnvR (AstVarName var) d =
  IM.insertWithKey (\v _ _ -> error $ "extendEnvR: duplicate " ++ show v)
                   var (AstVarR $ from1X d)

extendEnvI :: AstVarName Int -> Int
           -> AstEnv d r -> AstEnv d r
extendEnvI (AstVarName var) i =
  IM.insertWithKey (\v _ _ -> error $ "extendEnvI: duplicate " ++ show v)
                   var (AstVarI i)

interpretLambdaI
  :: (ADModeAndNumTensor d r, KnownNat n)
  => AstEnv d r
  -> (AstVarName Int, Ast n r)
  -> Int -> ADVal d (OR.Array n r)
interpretLambdaI env (var, ast) =
  \i -> interpretAst (extendEnvI var i env) ast

interpretLambdaIndex
  :: ADModeAndNumTensor d r
  => AstEnv d r
  -> (AstVarName Int, AstIndex n r)
  -> Int -> IndexInt n
interpretLambdaIndex env (var, asts) =
  \i -> fmap (interpretAstInt (extendEnvI var i env)) asts

interpretLambdaIndexToIndex
  :: ADModeAndNumTensor d r
  => AstEnv d r
  -> (AstVarList m, AstIndex p r)
  -> IndexInt m -> IndexInt p
interpretLambdaIndexToIndex env (vars, asts) =
  \ix -> let assocs = zip (sizedListToList vars) (indexToList ix)
             env2 = foldr (uncurry extendEnvI) env assocs
         in fmap (interpretAstInt env2) asts

-- We could duplicate interpretAst to save some time (sadly, we can't
-- interpret Ast uniformly in any Tensor and HasPrimal instance due to typing,
-- so we can't just use an instance of interpretation to OR.Array for that),
-- but it's not a huge saving, because all dual parts are gone before
-- we do any differentiation and they are mostly symbolic, so don't even
-- double the amount of tensor computation performed. The biggest problem is
-- allocation of tensors, but they are mostly shared with the primal part.
--
-- A more interesting case is if we want to use Ast for something else,
-- e.g., to differentiate directly, and so we'd first interpret it in itself,
-- simplifying, and its primal part in OR.Array.
interpretAstPrimal
  :: (ADModeAndNumTensor d r, KnownNat n)
  => AstEnv d r
  -> AstPrimalPart n r -> OR.Array n r
interpretAstPrimal env (AstPrimalPart v) =
  toArray $ tprimalPart $ interpretAst env v

interpretAst
  :: forall n r d. (ADModeAndNumTensor d r, KnownNat n)
  => AstEnv d r
  -> Ast n r -> ADVal d (OR.Array n r)
interpretAst env = \case
  AstVar _sh (AstVarName var) -> case IM.lookup var env of
    Just (AstVarR d) -> fromX1 d
    Just AstVarI{} ->
      error $ "interpretAst: type mismatch for Var" ++ show var
    Nothing -> error $ "interpretAst: unknown variable Var" ++ show var
  AstOp opCode args ->
    interpretAstOp (interpretAst env) opCode args
  AstConst a -> tconst a
  AstConstant a -> tconst $ interpretAstPrimal env a
  AstConstInt i -> fromIntegral $ interpretAstInt env i
  AstIndexZ v is -> indexZ (interpretAst env v) (fmap (interpretAstInt env) is)
    -- if index is out of bounds, the operations returns with an undefined
    -- value of the correct rank and shape; this is needed, because
    -- vectorization can produce out of bound indexing from code where
    -- the indexing is guarded by conditionals
  AstSum v -> sum' (interpretAst env v)
    -- TODO: recognize when sum0 may be used instead, which is much cheaper
    -- or should I do that in Delta instead? no, because tsum0R is cheaper, too
    -- TODO: recognize dot0 patterns and speed up their evaluation
  AstFromList l -> fromList (map (interpretAst env) l)
  AstFromVector l -> fromVector (V.map (interpretAst env) l)
  AstKonst k v -> konst k (interpretAst env v)
  AstAppend x y -> append (interpretAst env x) (interpretAst env y)
  AstSlice i k v -> slice i k (interpretAst env v)
  AstReverse v -> reverse' (interpretAst env v)
  AstTranspose perm v -> transpose perm $ interpretAst env v
  AstFlatten v -> let d = interpretAst env v
                  in reshape (flattenShape $ shape d) d
  AstReshape sh v -> reshape sh (interpretAst env v)
  AstBuild1 k (var, AstConstant r) ->
    tconstant $ fromArray
    $ OR.ravel . ORB.fromVector [k] . V.generate k
    $ \j -> toArray $ tprimalPart $ interpretLambdaI env (var, AstConstant r) j
  AstBuild1 k (var, v) -> build1 k (interpretLambdaI env (var, v))
    -- to be used only in tests; this is the POPL implementation of build
    -- (memory blowup, but avoids functions on tape), to test against
    -- the closure version that the direct ADVal Tensor instance uses
  AstGather1 k v (var, ix) ->
    gather1Closure k (interpretAst env v) (interpretLambdaIndex env (var, ix))
    -- TODO: currently we store the function on tape, because it doesn't
    -- cause recomputation of the gradient per-cell, unlike storing the build
    -- function on tape; for GPUs and libraries that don't understand Haskell
    -- closures, we cneck if the expressions involve tensor operations
    -- too hard for GPUs and, if not, we can store the AST expression
    -- on tape and translate it to whatever backend sooner or later;
    -- and if yes, fall back to POPL pre-computation that, unfortunately,
    -- leads to a tensor of deltas
  AstGatherN sh v (vars, ix) ->
    gatherNClosure sh (interpretAst env v)
                   (interpretLambdaIndexToIndex env (vars, ix))
    -- both gather operations accept out of bounds indexes,
    -- for the same reason ordinary indexing does, see above


interpretAstInt :: ADModeAndNumTensor d r
                => AstEnv d r
                -> AstInt r -> Int
interpretAstInt env = \case
  AstIntVar (AstVarName var) -> case IM.lookup var env of
    Just AstVarR{} ->
      error $ "interpretAstInt: type mismatch for Var" ++ show var
    Just (AstVarI i) -> i
    Nothing -> error $ "interpretAstInt: unknown variable Var" ++ show var
  AstIntOp opCodeInt args ->
    interpretAstIntOp (interpretAstInt env) opCodeInt args
  AstIntConst a -> a
  AstIntFloor v -> let D u _ = interpretAst env v
                   in floor $ tunScalarR u
  AstIntCond b a1 a2 -> if interpretAstBool env b
                        then interpretAstInt env a1
                        else interpretAstInt env a2
  AstMinIndex1 v -> tminIndex0 $ interpretAst env v
  AstMaxIndex1 v -> tmaxIndex0 $ interpretAst env v

interpretAstBool :: ADModeAndNumTensor d r
                 => AstEnv d r
                 -> AstBool r -> Bool
interpretAstBool env = \case
  AstBoolOp opCodeBool args ->
    interpretAstBoolOp (interpretAstBool env) opCodeBool args
  AstBoolConst a -> a
  AstRel opCodeRel args ->
    let f v = interpretAstPrimal env (AstPrimalPart v)
    in interpretAstRelOp f opCodeRel args
  AstRelInt opCodeRel args ->
    let f = interpretAstInt env
    in interpretAstRelOp f opCodeRel args

interpretAstOp :: RealFloat b
               => (c -> b) -> OpCode -> [c] -> b
{-# INLINE interpretAstOp #-}
interpretAstOp f PlusOp [u, v] = f u + f v
interpretAstOp f MinusOp [u, v] = f u - f v
interpretAstOp f TimesOp [u, v] = f u * f v
interpretAstOp f NegateOp [u] = negate $ f u
interpretAstOp f AbsOp [u] = abs $ f u
interpretAstOp f SignumOp [u] = signum $ f u
interpretAstOp f DivideOp [u, v] = f u / f v
interpretAstOp f RecipOp [u] = recip $ f u
interpretAstOp f ExpOp [u] = exp $ f u
interpretAstOp f LogOp [u] = log $ f u
interpretAstOp f SqrtOp [u] = sqrt $ f u
interpretAstOp f PowerOp [u, v] = f u ** f v
interpretAstOp f LogBaseOp [u, v] = logBase (f u) (f v)
interpretAstOp f SinOp [u] = sin $ f u
interpretAstOp f CosOp [u] = cos $ f u
interpretAstOp f TanOp [u] = tan $ f u
interpretAstOp f AsinOp [u] = asin $ f u
interpretAstOp f AcosOp [u] = acos $ f u
interpretAstOp f AtanOp [u] = atan $ f u
interpretAstOp f SinhOp [u] = sinh $ f u
interpretAstOp f CoshOp [u] = cosh $ f u
interpretAstOp f TanhOp [u] = tanh $ f u
interpretAstOp f AsinhOp [u] = asinh $ f u
interpretAstOp f AcoshOp [u] = acosh $ f u
interpretAstOp f AtanhOp [u] = atanh $ f u
interpretAstOp f Atan2Op [u, v] = atan2 (f u) (f v)
interpretAstOp f MaxOp [u, v] = max (f u) (f v)
interpretAstOp f MinOp [u, v] = min (f u) (f v)
interpretAstOp _ opCode args =
  error $ "interpretAstOp: wrong number of arguments"
          ++ show (opCode, length args)

interpretAstIntOp :: (AstInt r -> Int) -> OpCodeInt -> [AstInt r] -> Int
{-# INLINE interpretAstIntOp #-}
interpretAstIntOp f PlusIntOp [u, v] = f u + f v
interpretAstIntOp f MinusIntOp [u, v] = f u - f v
interpretAstIntOp f TimesIntOp [u, v] = f u * f v
interpretAstIntOp f NegateIntOp [u] = negate $ f u
interpretAstIntOp f AbsIntOp [u] = abs $ f u
interpretAstIntOp f SignumIntOp [u] = signum $ f u
interpretAstIntOp f MaxIntOp [u, v] = max (f u) (f v)
interpretAstIntOp f MinIntOp [u, v] = min (f u) (f v)
interpretAstIntOp f QuotIntOp [u, v] = quot (f u) (f v)
interpretAstIntOp f RemIntOp [u, v] = rem (f u) (f v)
interpretAstIntOp f DivIntOp [u, v] = div (f u) (f v)
interpretAstIntOp f ModIntOp [u, v] = mod (f u) (f v)
interpretAstIntOp _ opCodeInt args =
  error $ "interpretAstIntOp: wrong number of arguments"
          ++ show (opCodeInt, length args)

interpretAstBoolOp :: (AstBool r -> Bool) -> OpCodeBool -> [AstBool r]
                   -> Bool
{-# INLINE interpretAstBoolOp #-}
interpretAstBoolOp f NotOp [u] = not $ f u
interpretAstBoolOp f AndOp [u, v] = f u && f v
interpretAstBoolOp f OrOp [u, v] = f u || f v
interpretAstBoolOp _ opCodeBool args =
  error $ "interpretAstBoolOp: wrong number of arguments"
          ++ show (opCodeBool, length args)

interpretAstRelOp :: Ord b => (a -> b) -> OpCodeRel -> [a] -> Bool
{-# INLINE interpretAstRelOp #-}
interpretAstRelOp f EqOp [u, v] = f u == f v
interpretAstRelOp f NeqOp [u, v] = f u /= f v
interpretAstRelOp f LeqOp [u, v] = f u <= f v
interpretAstRelOp f GeqOp [u, v] = f u >= f v
interpretAstRelOp f LsOp [u, v] = f u < f v
interpretAstRelOp f GtOp [u, v] = f u > f v
interpretAstRelOp _ opCodeRel args =
  error $ "interpretAstRelOp: wrong number of arguments"
          ++ show (opCodeRel, length args)
