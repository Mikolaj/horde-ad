{-# LANGUAGE OverloadedLists, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Dual numbers and various operations on them, arithmetic and related
-- to tensors (vectors, matrices and others). This is a part of
-- the high-level API of the horde-ad library, defined using the mid-level
-- (and safely impure) API in "HordeAd.Core.DualClass". The other part
-- of the high-level API is in "HordeAd.Core.Engine".
module HordeAd.Core.TensorClass
  ( IndexOf, ShapeInt, Tensor(..), HasPrimal(..), ADReady
  , simplifyAst, scale1, relu1, reluLeaky1
  ) where


import Prelude

import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import           Data.Boolean
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat, type (+))
import           Numeric.LinearAlgebra (Numeric, Vector)

import HordeAd.Core.Ast
import HordeAd.Core.AstSimplify
import HordeAd.Core.AstVectorize
import HordeAd.Core.SizedIndex
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
  default tfloor  -- a more narrow type to rule out Ast
    :: IntOf r ~ Int => TensorOf 0 r -> IntOf r
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
  tslice :: KnownNat n => Int -> Int -> TensorOf (1 + n) r -> TensorOf (1 + n) r
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
  tfromIndex0 = AstConstant . AstPrimalPart . AstConstInt
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
  tgather sh t f = AstGatherZ sh t (funToAstIndex f)  -- introduces new vars

  tscalar = id  -- Ast confuses the two ranks
  tunScalar = id

-- This is a vectorizing combinator that also simplifies
-- the terms touched during vectorization, but not any others.
-- Due to how the Ast instance of Tensor is defined above, vectorization
-- works bottom-up, which removes the need to backtrack in the vectorization
-- pass or repeat until a fixed point is reached.
-- This combinator also introduces new variable names.
astBuild1 :: (KnownNat n, Show r, Numeric r, Num (Vector r))
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
                -- TODO: $ AstConstant . f
                -- that's the correct one, but unvectorized tests fail with it
  tgather sh t f = AstPrimalPart $ AstGatherZ sh (unAstPrimalPart t)
                   $ funToAstIndex f  -- this introduces new variable names

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

instance HasPrimal (Ast 0 r) where
  type ScalarOf (Ast 0 r) = r
  type Primal (Ast 0 r) = AstPrimalPart 0 r
  type DualOf n (Ast 0 r) = ()  -- TODO: data AstDualPart: dScale, dAdd, dkonst1
  tconst = AstConstant . AstPrimalPart . AstConst
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
