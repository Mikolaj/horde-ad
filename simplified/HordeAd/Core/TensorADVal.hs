{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | 'Tensor' class instances for dual number. The dual numbers are built
-- either from concrete floats or from 'Ast' term.
module HordeAd.Core.TensorADVal
  ( ADTensor
  ) where

import Prelude hiding ((<*))

import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import           Data.Boolean
import           Data.List (foldl1')
import           Data.MonoTraversable (Element)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           Foreign.C (CInt)
import           GHC.TypeLits (KnownNat, type (+))

import HordeAd.Core.Ast
import HordeAd.Core.AstSimplify
import HordeAd.Core.DualClass
import HordeAd.Core.DualNumber
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorClass

type ADTensor r =
  ( IsPrimal r
  , HasRanks r
  , Tensor r
  )

type instance BooleanOf (ADVal a) = BooleanOf a

instance (EqB a, IsPrimal a) => EqB (ADVal a) where
  D l1 u _ ==* D l2 v _ = letWrapPrimal l1 u ==* letWrapPrimal l2 v
  D l1 u _ /=* D l2 v _ = letWrapPrimal l1 u /=* letWrapPrimal l2 v

instance (OrdB a, IsPrimal a) => OrdB (ADVal a) where
  D l1 u _ <* D l2 v _ = letWrapPrimal l1 u <* letWrapPrimal l2 v
  D l1 u _ <=* D l2 v _ = letWrapPrimal l1 u <=* letWrapPrimal l2 v
  D l1 u _ >* D l2 v _ = letWrapPrimal l1 u >* letWrapPrimal l2 v
  D l1 u _ >=* D l2 v _ = letWrapPrimal l1 u >=* letWrapPrimal l2 v

instance IfB (ADVal Double) where
  ifB b v w = if b then v else w

instance IfB (ADVal Float) where
  ifB b v w = if b then v else w

instance IfB (ADVal (OR.Array n r)) where
  ifB b v w = if b then v else w

-- This requires the Tensor instance, hence the definitions must be here.
instance (KnownNat n, ShowAstSimplify r)
         => IfB (ADVal (Ast n r)) where
  ifB b v w = tindex (tfromList [v, w]) (singletonIndex $ ifB b 0 1)

instance ShowAstSimplify r
         => IfB (ADVal (Ast0 r)) where
  ifB b v w = tunScalar $ ifB b (tscalar v) (tscalar w)

-- We should really only have one @ADVal r@ instance, but typing problems caused
-- by ranks (and probably too strict injectivity checks) make us copy the code.
-- Not that these instances don't do vectorization. To enable it,
-- use the Ast instance and only then interpret in ADVal.
-- In any case, the first instances here are only used for tests.
-- Only the @ADVal (Ast0 r)@ instance is used in the codebase,
-- in particular, to satisfy the constraints needed for the interpretation
-- of @Ast@ in @ADVal (Ast0 r)@.
instance Tensor (ADVal Double) where
  type TensorOf n (ADVal Double) = ADVal (OR.Array n Double)
  type IntOf (ADVal Double) = CInt

  tshape (D _ u _) = tshape u
  tminIndex0 (D _ u _) = tminIndex0 u
  tmaxIndex0 (D _ u _) = tmaxIndex0 u
  tfloor (D _ u _) = tfloor u

  tindex = indexZ
  tsum = sum'
  tsum0 = sum0
  tdot0 = dot0
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
  type DualOf n (ADVal Double) = Dual (TensorOf n Double)
  tconst t = dD emptyADShare t dZero
  tconstant t = dD emptyADShare t dZero
  tscale0 r (D l u u') = dD l (r * u) (dScale r u')
  tprimalPart (D _ u _) = u
  tdualPart (D _ _ u') = u'
  tD = dD emptyADShare
  tScale = dScale
  tfromD = fromD

instance DynamicTensor (ADVal Double) where
  type DTensorOf (ADVal Double) = ADVal (OD.Array Double)
  dfromR = fromR

instance Tensor (ADVal Float) where
  type TensorOf n (ADVal Float) = ADVal (OR.Array n Float)
  type IntOf (ADVal Float) = CInt

  tshape (D _ u _) = tshape u
  tminIndex0 (D _ u _) = tminIndex0 u
  tmaxIndex0 (D _ u _) = tmaxIndex0 u
  tfloor (D _ u _) = tfloor u

  tindex = indexZ
  tsum = sum'
  tsum0 = sum0
  tdot0 = dot0
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
  type DualOf n (ADVal Float) = Dual (TensorOf n Float)
  tconst t = dD emptyADShare t dZero
  tconstant t = dD emptyADShare t dZero
  tscale0 r (D l u u') = dD l (r * u) (dScale r u')
  tprimalPart (D _ u _) = u
  tdualPart (D _ _ u') = u'
  tD = dD emptyADShare
  tScale = dScale
  tfromD = fromD

instance DynamicTensor (ADVal Float) where
  type DTensorOf (ADVal Float) = ADVal (OD.Array Float)
  dfromR = fromR

instance (ADTensor (Ast0 r), ShowAstSimplify r)
         => Tensor (ADVal (Ast0 r)) where
  type TensorOf n (ADVal (Ast0 r)) = ADVal (Ast n r)
  type IntOf (ADVal (Ast0 r)) = AstInt r

  tlet (D l u u') f =
    let (l2, var2) = astRegisterADShare u l
    in f (D l2 var2 u')
      -- TODO: What about sharing u'?

  tshape (D _ u _) = tshape u
  -- This is very slow, but is fortunately not needed:
  -- tshape (D l u _) = tshape (tletWrap l u)
  tminIndex0 (D l u _) = tminIndex0 (tletWrap l u)
  tmaxIndex0 (D l u _) = tmaxIndex0 (tletWrap l u)
  tfloor (D l u _) = tfloor (tletWrap l u)

  tindex = indexZ
  tsum = sum'
  tsum0 = sum0
  tdot0 = dot0
  tfromIndex0 = tconstant . tfromIndex0
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

  tsumOfList lu = dD (flattenADShare $ map ((\(D l _ _) -> l)) lu)
                     (tsumOfList $ map (\(D _ u _) -> u) lu)
                     (foldl1' dAdd $ map (\(D _ _ u') -> u') lu)

  type ScalarOf (ADVal (Ast0 r)) = r
  type Primal (ADVal (Ast0 r)) = Ast0 r
  type DualOf n (ADVal (Ast0 r)) =
    (ADShare (Ast0 r), Dual (TensorOf n (Ast0 r)))
  tconst t = dD emptyADShare (tconst t) dZero
  tconstant t = dD emptyADShare t dZero
  tscale0 r (D l u u') = dD l (r * u) (dScale r u')
  tprimalPart (D l u _) = tletWrap l u
  tdualPart (D l _ u') = (l, u')
  tD ast (l, delta) = dD l ast delta
  tScale s (l, delta) = (l, dScale s delta)

  tfromD = fromD

instance ShowAstSimplify r
         => DynamicTensor (ADVal (Ast0 r)) where
  type DTensorOf (ADVal (Ast0 r)) = ADVal (AstDynamic r)
  dfromR = fromR


-- * ADVal combinators generalizing ranked tensor operations

sum0 :: ( ADTensor r, IsPrimal (TensorOf 0 r), KnownNat n
        , Element (TensorOf 0 r) ~ Element (TensorOf n r) )
     => ADVal (TensorOf n r) -> ADVal (TensorOf 0 r)
sum0 (D l u u') = dD l (tsum0 u) (dScalarR $ dSum0 (tshape u) u')

dot0 :: ( ADTensor r, IsPrimal (TensorOf n  r), IsPrimal (TensorOf 0 r)
        , KnownNat n, Element (TensorOf 0 r) ~ Element (TensorOf n r)
        , Element (TensorOf n r) ~ r )
     => ADVal (TensorOf n r) -> ADVal (TensorOf n r) -> ADVal (TensorOf 0 r)
dot0 (D l1 ue u') (D l2 ve v') =
  let (l3, u) = recordSharingPrimal ue $ l1 `mergeADShare` l2
      (l4, v) = recordSharingPrimal ve l3
  in dD l4 (tdot0 u v) (dScalarR $ dAdd (dDot0 v u') (dDot0 u v'))

-- TODO: speed up by using tindex0R and dIndex0 if the codomain is 0
-- and dD (u `tindex1R` ix) (dIndex1 u' ix (tlengthR u)) if only outermost
-- dimension affected.
--
-- First index is for outermost dimension; empty index means identity,
-- index ouf of bounds produces zero (but beware of vectorization).
indexZ :: forall m n r.
          ( ADTensor r, IsPrimal (TensorOf n r), KnownNat m, KnownNat n
          , Element (TensorOf (m + n) r) ~ Element (TensorOf n r) )
       => ADVal (TensorOf (m + n) r) -> IndexOf m r
       -> ADVal (TensorOf n r)
indexZ (D l u u') ix = dD l (tindex u ix) (dIndexZ u' ix (tshape u))

sum' :: ( ADTensor r, IsPrimal (TensorOf n r), KnownNat n
        , Element (TensorOf n r) ~ Element (TensorOf (1 + n) r) )
     => ADVal (TensorOf (1 + n) r) -> ADVal (TensorOf n r)
sum' (D l u u') = dD l (tsum u) (dSumR (tlength u) u')

scatterNClosure
  :: ( ADTensor r, IsPrimal (TensorOf (p + n) r)
     , KnownNat m, KnownNat p, KnownNat n
     , Element (TensorOf (p + n) r) ~ Element (TensorOf (m + n) r) )
  => ShapeInt (p + n) -> ADVal (TensorOf (m + n) r)
  -> (IndexOf m r -> IndexOf p r)
  -> ADVal (TensorOf (p + n) r)
scatterNClosure sh (D l u u') f =
  dD l (tscatter sh u f) (dScatterZ sh u' f (tshape u))

fromList :: ( ADTensor r, IsPrimal (TensorOf (1 + n) r), KnownNat n
            , Element (TensorOf n r) ~ Element (TensorOf (1 + n) r) )
         => [ADVal (TensorOf n r)]
         -> ADVal (TensorOf (1 + n) r)
fromList lu =
  -- TODO: if lu is empty, crash if n =\ 0 or use List.NonEmpty.
  dD (flattenADShare $ map ((\(D l _ _) -> l)) lu)
     (tfromList $ map (\(D _ u _) -> u) lu)
     (dFromListR $ map (\(D _ _ u') -> u') lu)

--fromList0N :: (ADTensor r, KnownNat n)
--           => ShapeInt n -> [ADVal r]
--           -> ADVal (TensorOf n r)
--fromList0N sh l =
--  dD (tfromList0N sh $ map (\(D u _) -> u) l)  -- I hope this fuses
--     (dFromList01 sh $ map (\(D _ u') -> u') l)

fromVector :: ( ADTensor r, IsPrimal (TensorOf (1 + n) r), KnownNat n
              , Element (TensorOf n r) ~ Element (TensorOf (1 + n) r) )
           => Data.Vector.Vector (ADVal (TensorOf n r))
           -> ADVal (TensorOf (1 + n) r)
fromVector lu =
  dD (flattenADShare $ map ((\(D l _ _) -> l)) $ V.toList lu)
     (tfromVector $ V.map (\(D _ u _) -> u) lu)
     (dFromVectorR $ V.map (\(D _ _ u') -> u') lu)

--fromVector0N :: (ADTensor r, KnownNat n)
--             => ShapeInt n -> Data.Vector.Vector (ADVal r)
--             -> ADVal (TensorOf n r)
--fromVector0N sh l =
--  dD (tfromVector0N sh $ V.convert $ V.map (\(D u _) -> u) l)  -- hope it fuses
--     (dFromVector01 sh $ V.map (\(D _ u') -> u') l)

konst :: ( ADTensor r, IsPrimal (TensorOf (1 + n) r), KnownNat n
         , Element (TensorOf n r) ~ Element (TensorOf (1 + n) r) )
      => Int -> ADVal (TensorOf n r) -> ADVal (TensorOf (1 + n) r)
konst k (D l u u') = dD l (tkonst k u) (dKonstR k u')

--konst0N :: (ADTensor r, KnownNat n)
--        => ShapeInt n -> ADVal r -> ADVal (TensorOf n r)
--konst0N sh (D u u') = dD (tkonst0N sh u) (dKonst01 sh u')

append :: (ADTensor r, IsPrimal (TensorOf (1 + n) r), KnownNat n)
       => ADVal (TensorOf (1 + n) r) -> ADVal (TensorOf (1 + n) r)
       -> ADVal (TensorOf (1 + n) r)
append (D l1 u u') (D l2 v v') =
  dD (l1 `mergeADShare` l2) (tappend u v) (dAppendR u' (tlength u) v')

slice :: (ADTensor r, IsPrimal (TensorOf (1 + n) r), KnownNat n)
      => Int -> Int -> ADVal (TensorOf (1 + n) r)
      -> ADVal (TensorOf (1 + n) r)
slice i k (D l u u') = dD l (tslice i k u) (dSliceR i k u' (tlength u))

reverse' :: (ADTensor r, IsPrimal (TensorOf (1 + n) r), KnownNat n)
         => ADVal (TensorOf (1 + n) r) -> ADVal (TensorOf (1 + n) r)
reverse' (D l u u') = dD l (treverse u) (dReverseR u')

transpose :: (ADTensor r, IsPrimal (TensorOf n r), KnownNat n)
          => Permutation -> ADVal (TensorOf n r) -> ADVal (TensorOf n r)
transpose perm (D l u u') = dD l (ttranspose perm u) (dTransposeR perm u')

reshape :: ( ADTensor r, IsPrimal (TensorOf m r), KnownNat m, KnownNat n
           , Element (TensorOf n r) ~ Element (TensorOf m r) )
        => ShapeInt m -> ADVal (TensorOf n r) -> ADVal (TensorOf m r)
reshape sh (D l u u') = dD l (treshape sh u) (dReshapeR (tshape u) sh u')

build1
  :: ( ADTensor r, KnownNat n, IsPrimal (TensorOf (1 + n) r)
     , Element (TensorOf n r) ~ Element (TensorOf (1 + n) r) )
  => Int -> (IntOf r -> ADVal (TensorOf n r))
  -> ADVal (TensorOf (1 + n) r)
build1 k f = fromList $ map (f . fromIntegral) [0 .. k - 1]
               -- element-wise (POPL) version

-- Strangely, this variant slows down simplifiedOnlyTest 3 times. Perhaps
-- that's because k is very low and the f functions are simple enough.
_build1Closure
  :: (ADTensor r, KnownNat n, IsPrimal (TensorOf (1 + n) r))
  => Int -> (IntOf r -> ADVal (TensorOf n r))
  -> ADVal (TensorOf (1 + n) r)
_build1Closure k f =  -- stores closures on tape
  let g i = let D _ u _ = f i in u
      h i = let D _ _ u' = f i in u'
  in dD emptyADShare (tbuild1 k g) (dBuildR k h)
       -- TODO: is the empty sharing list fine?

-- Note that if any index is out of bounds, the result of that particular
-- projection is defined and is 0 (but beware of vectorization).
gatherNClosure
  :: ( ADTensor r, IsPrimal (TensorOf (m + n) r)
     , KnownNat m, KnownNat p, KnownNat n
     , Element (TensorOf (p + n) r) ~ Element (TensorOf (m + n) r) )
  => ShapeInt (m + n) -> ADVal (TensorOf (p + n) r)
  -> (IndexOf m r -> IndexOf p r)
  -> ADVal (TensorOf (m + n) r)
gatherNClosure sh (D l u u') f =
  dD l (tgather sh u f) (dGatherZ sh u' f (tshape u))

scalar :: ( ADTensor r, IsPrimal (TensorOf 0 r)
          , Element (TensorOf 0 r) ~ Element r )
       => ADVal r -> ADVal (TensorOf 0 r)
scalar (D l u u') = dD l (tscalar u) (dScalarR u')

unScalar :: (ADTensor r, Element (TensorOf 0 r) ~ Element r)
         => ADVal (TensorOf 0 r) -> ADVal r
unScalar (D l u u') = dD l (tunScalar u) (dUnScalar0 u')

fromD :: forall n r.
         ( ADTensor r, KnownNat n
         , Element (TensorOf n r) ~ Element (DTensorOf r) )
       => ADVal (DTensorOf r) -> ADVal (TensorOf n r)
fromD (D l u u') = dDnotShared l (tfromD u) (dFromD u')

fromR :: ( ADTensor r, DynamicTensor r, KnownNat n
         , Element (TensorOf n r) ~ Element (DTensorOf r) )
       => ADVal (TensorOf n r) -> ADVal (DTensorOf r)
fromR (D l u u') = dDnotShared l (dfromR u) (dFromR u')
