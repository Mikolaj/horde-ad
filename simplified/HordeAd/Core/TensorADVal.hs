{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Dual numbers and various operations on them, arithmetic and related
-- to tensors (vectors, matrices and others). This is a part of
-- the high-level API of the horde-ad library, defined using the mid-level
-- (and safely impure) API in "HordeAd.Core.DualClass". The other part
-- of the high-level API is in "HordeAd.Core.Engine".
module HordeAd.Core.TensorADVal
  ( ADTensor
  ) where

import Prelude hiding ((<*))

import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import           Data.Boolean
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, type (+))
import           Numeric.LinearAlgebra (Numeric, Vector)

import HordeAd.Core.Ast
import HordeAd.Core.DualClass
import HordeAd.Core.DualNumber hiding (build1)
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorClass
import HordeAd.Internal.TensorOps

type ADTensor r =
  ( IsPrimal r
  , HasRanks r
  , Tensor r
  )

--TODO:remove
class TensorIsArray r where
  toArray :: TensorOf n r -> OR.Array n r
  fromArray :: OR.Array n r -> TensorOf n r

instance TensorIsArray Double where
  toArray = id
  fromArray = id

instance TensorIsArray Float where
  toArray = id
  fromArray = id

instance (Num (Vector r), Numeric r, Show r, KnownNat n)
         => IfB (ADVal (Ast n r)) where
  ifB b v w = tindex (tfromList [v, w]) (singletonIndex $ ifB b 0 1)

instance (Num (Vector r), Numeric r, Show r)
         => IfB (ADVal (Ast0 r)) where
  ifB b v w = tunScalar $ ifB b (tscalar v) (tscalar w)

-- Not that this instance doesn't do vectorization. To enable it,
-- use the Ast instance, which vectorizes and finally interpret in ADVal.
-- In principle, this instance is only useful for comparative tests,
-- though for code without build/map/etc., it should be equivalent
-- to going via Ast.
instance Tensor (ADVal Double) where
  type TensorOf n (ADVal Double) = ADVal (OR.Array n Double)
  type IntOf (ADVal Double) = Int

  -- Here and elsewhere I can't use methods of the @r@ instance of @Tensor@
  -- (the one implemented as @OR.Array n r@). Therefore, I inline them
  -- manually. There is probably no solution to that (2 parameters to Tensor
  -- would solve this, but we'd need infinitely many instances
  -- for @ADVal (OR.Array n r)@ and @OR.Array n r@). As a workaround,
  -- the methods are defined as calls to tensor functions provided elsewhere,
  -- so there is no code duplication.
  tshape = shape
  tminIndex0 (D u _) = tminIndexR u
  tmaxIndex0 (D u _) = tmaxIndexR u
  tfloor (D u _) = floor $ tunScalarR u

  tindex = indexZ
  tsum = sum'
  tsum0 = tscalar . sum0
  tdot0 u v = tscalar $ dot0 u v
  tscatter = scatterNClosure

  tfromList = fromList
--  tfromList0N = fromList0N
  tfromVector = fromVector
--  tfromVector0N = fromVector0N
  tkonst = konst
--  tkonst0N sh = konst0N sh . unScalar
  tappend = append
  tslice = slice
  treverse = reverse'
  ttranspose = transpose
  treshape = reshape
  tbuild1 = build1
  tgather = gatherNClosure

  tscalar = scalar
  tunScalar = unScalar

  type ScalarOf (ADVal Double) = Double
  type Primal (ADVal Double) = Double
  type DualOf n (ADVal Double) = Dual (OR.Array n Double)
  tconst t = dD t dZero
  tconstant t = dD (toArray t) dZero
  tprimalPart (D u _) = fromArray u
  tdualPart (D _ u') = u'
  tD u = dD (toArray u)
  type DynamicTensor (ADVal Double) = ADVal (OD.Array Double)
  tdummyD = undefined  -- not used for dual numbers
  tisDummyD = undefined  -- not used for dual numbers
  taddD = (+)
  tshapeD (D u _) = OD.shapeL u
  tfromR = from1D
  tfromD = fromD1

instance Tensor (ADVal Float) where
  type TensorOf n (ADVal Float) = ADVal (OR.Array n Float)
  type IntOf (ADVal Float) = Int

  tshape = shape
  tminIndex0 (D u _) = tminIndexR u
  tmaxIndex0 (D u _) = tmaxIndexR u
  tfloor (D u _) = floor $ tunScalarR u

  tindex = indexZ
  tsum = sum'
  tsum0 = tscalar . sum0
  tdot0 u v = tscalar $ dot0 u v
  tscatter = scatterNClosure

  tfromList = fromList
--  tfromList0N = fromList0N
  tfromVector = fromVector
--  tfromVector0N = fromVector0N
  tkonst = konst
--  tkonst0N sh = konst0N sh . unScalar
  tappend = append
  tslice = slice
  treverse = reverse'
  ttranspose = transpose
  treshape = reshape
  tbuild1 = build1
  tgather = gatherNClosure

  tscalar = scalar
  tunScalar = unScalar

  type ScalarOf (ADVal Float) = Float
  type Primal (ADVal Float) = Float
  type DualOf n (ADVal Float) = Dual (OR.Array n Float)
  tconst t = dD t dZero
  tconstant t = dD (toArray t) dZero
  tprimalPart (D u _) = fromArray u
  tdualPart (D _ u') = u'
  tD u = dD (toArray u)
  -- TODO: if ever used, define, if not, use an Error type
  type DynamicTensor (ADVal Float) = ADVal (OD.Array Float)
  tdummyD = undefined  -- not used for dual numbers
  tisDummyD = undefined  -- not used for dual numbers
  taddD = (+)
  tshapeD (D u _) = OD.shapeL u
  tfromR = from1D
  tfromD = fromD1

instance (ADTensor (Ast0 r), Numeric r, Show r, Num (Vector r))
         => Tensor (ADVal (Ast0 r)) where
  type TensorOf n (ADVal (Ast0 r)) = ADVal (Ast n r)
  type IntOf (ADVal (Ast0 r)) = AstInt r

  tshape = shape @(Ast0 r)
  tminIndex0 (D u _) = AstMinIndex1 u
  tmaxIndex0 (D u _) = AstMaxIndex1 u
  tfloor (D u _) = AstIntFloor u

  tindex = indexZ
  tsum = sum'
  tsum0 = tscalar . sum0
  tdot0 u v = tscalar $ dot0 u v
  tfromIndex0 i = tconstant $ AstConstInt i
  tscatter = scatterNClosure

  tfromList = fromList
--  tfromList0N = fromList0N
  tfromVector = fromVector
--  tfromVector0N = fromVector0N
  tkonst = konst
--  tkonst0N sh = konst0N sh . unScalar
  tappend = append
  tslice = slice
  treverse = reverse'
  ttranspose = transpose
  treshape = reshape
  tbuild1 = build1
  tgather = gatherNClosure

  tscalar = scalar
  tunScalar = unScalar

  type ScalarOf (ADVal (Ast0 r)) = r
  type Primal (ADVal (Ast0 r)) = Ast0 r
  type DualOf n (ADVal (Ast0 r)) = Dual (Ast n r)
  tconst t = dD (AstConst t) dZero
  tconstant t = dD t dZero
  tprimalPart (D u _) = u
  tdualPart (D _ u') = u'
  tD = dD
  type DynamicTensor (ADVal (Ast0 r)) = ADVal (AstDynamic r)
  tdummyD = undefined  -- not used for dual numbers
  tisDummyD = undefined  -- not used for dual numbers
  taddD (D u u') (D v v') = dD (AstDynamicPlus u v) (dAdd u' v')
  tshapeD (D u _) = tshapeD u
  tfromR = from1D
  tfromD = fromD1


-- * ADVal combinators generalizing ranked tensor operations

shape :: (ADTensor r, KnownNat n)
      => ADVal (TensorOf n r) -> ShapeInt n
shape (D u _) = tshape u

-- TODO: speed up by using tindex0R and dIndex0 if the codomain is 0
-- and dD (u `tindex1R` ix) (dIndex1 u' ix (tlengthR u)) if only outermost
-- dimension affected.
--
-- First index is for outermost dimension; empty index means identity,
-- index ouf of bounds produces zero (but beware of vectorization).
indexZ :: forall m n r.
          (ADTensor r, IsPrimal (TensorOf n r), KnownNat m, KnownNat n)
       => ADVal (TensorOf (m + n) r) -> IndexOf m r
       -> ADVal (TensorOf n r)
indexZ (D u u') ix = dD (tindex u ix) (dIndexZ u' ix (tshape u))

sum' :: (ADTensor r, IsPrimal (TensorOf n r), KnownNat n)
     => ADVal (TensorOf (1 + n) r) -> ADVal (TensorOf n r)
sum' (D u u') = dD (tsum u) (dSum1 (tlength u) u')

sum0 :: (ADTensor r, KnownNat n)
     => ADVal (TensorOf n r) -> ADVal r
sum0 (D u u') = dD (tunScalar $ tsum0 u) (dSum0 (tshape u) u')

dot0 :: (ADTensor r, KnownNat n)
     => ADVal (TensorOf n r) -> ADVal (TensorOf n r) -> ADVal r
dot0 (D u u') (D v v') = dD (tunScalar $ tdot0 u v)
                            (dAdd (dDot0 v u') (dDot0 u v'))

scatterNClosure :: ( ADTensor r, IsPrimal (TensorOf (p + n) r)
                   , KnownNat m, KnownNat p, KnownNat n )
                => ShapeInt (p + n) -> ADVal (TensorOf (m + n) r)
                -> (IndexOf m r -> IndexOf p r)
                -> ADVal (TensorOf (p + n) r)
scatterNClosure sh (D u u') f =
  dD (tscatter sh u f) (dScatterZ sh u' f (tshape u))

fromList :: (ADTensor r, IsPrimal (TensorOf (1 + n) r), KnownNat n)
         => [ADVal (TensorOf n r)]
         -> ADVal (TensorOf (1 + n) r)
fromList lu =
  -- TODO: if lu is empty, crash if n =\ 0 or use List.NonEmpty.
  dD (tfromList $ map (\(D u _) -> u) lu)
     (dFromList1 $ map (\(D _ u') -> u') lu)

--fromList0N :: (ADTensor r, KnownNat n)
--           => ShapeInt n -> [ADVal r]
--           -> ADVal (TensorOf n r)
--fromList0N sh l =
--  dD (tfromList0N sh $ map (\(D u _) -> u) l)  -- I hope this fuses
--     (dFromList01 sh $ map (\(D _ u') -> u') l)

fromVector :: (ADTensor r, IsPrimal (TensorOf (1 + n) r), KnownNat n)
           => Data.Vector.Vector (ADVal (TensorOf n r))
           -> ADVal (TensorOf (1 + n) r)
fromVector lu =
  dD (tfromVector $ V.map (\(D u _) -> u) lu)
     (dFromVector1 $ V.map (\(D _ u') -> u') lu)

--fromVector0N :: (ADTensor r, KnownNat n)
--             => ShapeInt n -> Data.Vector.Vector (ADVal r)
--             -> ADVal (TensorOf n r)
--fromVector0N sh l =
--  dD (tfromVector0N sh $ V.convert $ V.map (\(D u _) -> u) l)  -- hope it fuses
--     (dFromVector01 sh $ V.map (\(D _ u') -> u') l)

konst :: (ADTensor r, IsPrimal (TensorOf (1 + n) r), KnownNat n)
      => Int -> ADVal (TensorOf n r) -> ADVal (TensorOf (1 + n) r)
konst k (D u u') = dD (tkonst k u) (dKonst1 k u')

--konst0N :: (ADTensor r, KnownNat n)
--        => ShapeInt n -> ADVal r -> ADVal (TensorOf n r)
--konst0N sh (D u u') = dD (tkonst0N sh u) (dKonst01 sh u')

append :: (ADTensor r, IsPrimal (TensorOf (1 + n) r), KnownNat n)
       => ADVal (TensorOf (1 + n) r) -> ADVal (TensorOf (1 + n) r)
       -> ADVal (TensorOf (1 + n) r)
append (D u u') (D v v') = dD (tappend u v) (dAppend1 u' (tlength u) v')

slice :: (ADTensor r, IsPrimal (TensorOf (1 + n) r), KnownNat n)
      => Int -> Int -> ADVal (TensorOf (1 + n) r)
      -> ADVal (TensorOf (1 + n) r)
slice i k (D u u') = dD (tslice i k u) (dSlice1 i k u' (tlength u))

reverse' :: (ADTensor r, IsPrimal (TensorOf (1 + n) r), KnownNat n)
         => ADVal (TensorOf (1 + n) r) -> ADVal (TensorOf (1 + n) r)
reverse' (D u u') = dD (treverse u) (dReverse1 u')

transpose :: (ADTensor r, IsPrimal (TensorOf n r), KnownNat n)
          => Permutation -> ADVal (TensorOf n r) -> ADVal (TensorOf n r)
transpose perm (D u u') = dD (ttranspose perm u) (dTranspose1 perm u')

reshape :: (ADTensor r, IsPrimal (TensorOf m r), KnownNat m, KnownNat n)
        => ShapeInt m -> ADVal (TensorOf n r) -> ADVal (TensorOf m r)
reshape sh (D u u') = dD (treshape sh u) (dReshape1 (tshape u) sh u')

build1, _build1Closure
  :: (ADTensor r, KnownNat n, IsPrimal (TensorOf (1 + n) r))
  => Int -> (IntOf r -> ADVal (TensorOf n r))
  -> ADVal (TensorOf (1 + n) r)
build1 k f = fromList $ map (f . fromIntegral) [0 .. k - 1]
               -- element-wise (POPL) version

-- Strangely, this variant slows down simplifiedOnlyTest 3 times. Perhaps
-- that's because k is very low and the f functions are simple enough.
_build1Closure k f =  -- stores closures on tape
  let g i = let D u _ = f i in u
      h i = let D _ u' = f i in u'
  in dD (tbuild1 k g) (dBuild1 k h)

-- Note that if any index is out of bounds, the result of that particular
-- projection is defined and is 0 (but beware of vectorization).
gatherNClosure :: ( ADTensor r, IsPrimal (TensorOf (m + n) r)
                  , KnownNat m, KnownNat p, KnownNat n )
               => ShapeInt (m + n) -> ADVal (TensorOf (p + n) r)
               -> (IndexOf m r -> IndexOf p r)
               -> ADVal (TensorOf (m + n) r)
gatherNClosure sh (D u u') f =
  dD (tgather sh u f) (dGatherZ sh u' f (tshape u))

scalar :: (ADTensor r, IsPrimal (TensorOf 0 r))
       => ADVal r -> ADVal (TensorOf 0 r)
scalar (D u u') = dD (tscalar u) (dScalar1 u')

unScalar :: ADTensor r => ADVal (TensorOf 0 r) -> ADVal r
unScalar (D u u') = dD (tunScalar u) (dUnScalar0 u')

fromD1 :: forall n r. (ADTensor r, KnownNat n)
       => ADVal (DynamicTensor r) -> ADVal (TensorOf n r)
fromD1 (D u u') = dDnotShared (tfromD u) (dFromD1 u')

from1D :: (ADTensor r, KnownNat n)
       => ADVal (TensorOf n r) -> ADVal (DynamicTensor r)
from1D (D u u') = dDnotShared (tfromR u) (dFrom1D u')
