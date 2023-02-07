{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleInstances,
             MultiParamTypeClasses, OverloadedLists, TypeFamilyDependencies #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Dual numbers and various operations on them, arithmetic and related
-- to tensors (vectors, matrices and others). This is a part of
-- the high-level API of the horde-ad library, defined using the mid-level
-- (and safely impure) API in "HordeAd.Core.DualClass". The other part
-- of the high-level API is in "HordeAd.Core.Engine".
module HordeAd.Core.TensorClass
  ( HasPrimal(..), Tensor(..)
  , interpretAst, AstVar(..)
  , ADReady
  , scalar, unScalar, leqAst, gtAst, gtIntAst, relu, reluLeaky, reluAst
  ) where

import Prelude

import qualified Data.Array.DynamicS as OT
import qualified Data.Array.Ranked as ORB
import qualified Data.Array.RankedS as OR
import           Data.MonoTraversable (MonoFunctor (omap))
import qualified Data.Strict.IntMap as IM
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat, type (+))
import           Numeric.LinearAlgebra (Numeric, Vector)
import           System.IO.Unsafe (unsafePerformIO)

import HordeAd.Core.Ast
import HordeAd.Core.AstVectorize
import HordeAd.Core.DualClass
import HordeAd.Core.DualNumber hiding (build1)
import HordeAd.Core.SizedIndex
import HordeAd.Internal.SizedList
import HordeAd.Internal.TensorOps

-- * Odds and ends

type ADModeAndNumTensor (d :: ADMode) r =
  ( ADModeAndNum d r
  , Tensor r
  , TensorOf 1 r ~ OR.Array 1 r
  , IntOf r ~ Int
  )

leqAst :: Ast 0 r -> Ast 0 r -> AstBool r
leqAst d e = AstRel LeqOp [d, e]

gtAst :: Ast 0 r -> Ast 0 r -> AstBool r
gtAst d e = AstRel GtOp [d, e]

gtIntAst :: AstInt r -> AstInt r -> AstBool r
gtIntAst i j = AstRelInt GtOp [i, j]

relu, reluLeaky
  :: ( HasPrimal a, MonoFunctor (PrimalOf a), Num (PrimalOf a)
     , Ord (Element (PrimalOf a)), Fractional (Element (PrimalOf a)) )
  => a -> a
relu v =
  let oneIfGtZero = omap (\x -> if x > 0 then 1 else 0) (primalPart v)
  in scale oneIfGtZero v

reluLeaky v =
  let oneIfGtZero = omap (\x -> if x > 0 then 1 else 0.01) (primalPart v)
  in scale oneIfGtZero v

-- TODO: generalize the function @relu@ above so that
-- it has a sensible Ast instance and then kill reluAst;
-- we'd need Conditional class that works with our AstBool type
-- and some sugar to be able to use >, &&, etc.
reluAst
  :: forall n r. (KnownNat n, Num (Vector r), Numeric r)
  => Ast n r -> Ast n r
reluAst v =
  let oneIfGtZero = omap (\(AstPrimalPart1 x) ->
                            AstPrimalPart1 $ AstCond (AstRel GtOp [x, 0]) 1 0)
                         (primalPart v)
  in scale oneIfGtZero v


-- * HasPrimal class and instances for all relevant types

-- We could accept any @RealFloat@ instead of @PrimalOf a@, but then
-- we'd need to coerce, e.g., via realToFrac, which is risky and lossy.
-- Also, the stricter typing is likely to catch real errors most of the time,
-- not just sloppy omission ofs explicit coercions.
class HasPrimal a where
  type PrimalOf a
  type DualOf a
  constant :: PrimalOf a -> a
  scale :: Num (PrimalOf a) => PrimalOf a -> a -> a
    -- expressible with @constant@ and multiplication, but we want the same
    -- name in each class instance, so it needs to be included in the class
  primalPart :: a -> PrimalOf a
  dualPart :: a -> DualOf a
  ddD :: PrimalOf a -> DualOf a -> a
  -- TODO: we'd probably also need dZero, dIndex0 and all others;
  -- basically DualOf a needs to have IsPrimal and HasRanks instances
  -- (and HasInputs?)
  -- TODO: if DualOf is supposed to be user-visible, we needed
  -- a better name for it; TangentOf? CotangentOf? SecondaryOf?
  --
  -- TODO: also put conditionals with AstBool condition here, at least initially

instance (Num a, IsPrimal d a) => HasPrimal (ADVal d a) where
  type PrimalOf (ADVal d a) = a
  type DualOf (ADVal d a) = Dual d a
  constant a = dD a dZero
  scale a (D u u') = dD (a * u) (dScale a u')
  primalPart (D u _) = u
  dualPart (D _ u') = u'
  ddD = dD

instance HasPrimal Float where
  type PrimalOf Float = Float
  type DualOf Float = ()
  constant = id
  scale = (*)
  primalPart = id
  dualPart _ = ()
  ddD u _ = u

instance HasPrimal Double where
  type PrimalOf Double = Double
  type DualOf Double = ()
  constant = id
  scale = (*)
  primalPart = id
  dualPart _ = ()
  ddD u _ = u

-- The constraint requires UndecidableInstances.
instance Numeric r
         => HasPrimal (OR.Array n r) where
  type PrimalOf (OR.Array n r) = OR.Array n r
  type DualOf (OR.Array n r) = ()
  constant = id
  scale = (*)
  primalPart = id
  dualPart _ = ()
  ddD u _ = u

instance HasPrimal (Ast n r) where
  type PrimalOf (Ast n r) = AstPrimalPart1 n r
  type DualOf (Ast n r) = ()  -- TODO: data AstDualPart: dScale, dAdd, dkonst1
  constant = AstConstant
  scale = AstScale
  primalPart = AstPrimalPart1
  dualPart = error "TODO"
  ddD = error "TODO"


-- * Tensor class definition and instances for arrays, ADVal and Ast

-- @IntOf r@ as size or shape gives more expressiveness,
-- but leads to irregular tensors, especially after vectorization,
-- and prevents statically known shapes.
-- However, if we switched to @Data.Array.Shaped@ and moved most of the shapes
-- to the type level, we'd recover some of the expressiveness, while retaining
-- statically known (type-parameterized) shapes.

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
  tsize :: KnownNat n => TensorOf n r -> Int
  tsize = sizeShape . tshape
  tlength :: KnownNat n => TensorOf (1 + n) r -> Int
  tlength v = case tshape v of
    ZS -> error "tlength:  impossible pattern needlessly required"
    k :$ _ -> k
  tminIndex :: TensorOf 1 r -> IntOf r
  tmaxIndex :: TensorOf 1 r -> IntOf r

  -- Typically scalar codomain, often tensor reduction
  tindex, (!) :: (KnownNat m, KnownNat n)
              => TensorOf (m + n) r -> IndexOf m r -> TensorOf n r
  infixl 9 !
  (!) = tindex  -- prefix form better when type applications are necessary
  tsum :: KnownNat n => TensorOf (1 + n) r -> TensorOf n r
  tsum0 :: KnownNat n => TensorOf n r -> TensorOf 0 r
  tsum0 = tsum . tflatten
  tdot0 :: KnownNat n => TensorOf n r -> TensorOf n r -> TensorOf 0 r
  tdot0 t u = tsum (tflatten t * tflatten u)
  tminimum0 :: TensorOf 1 r -> TensorOf 0 r
  tminimum0 t = t ! [tminIndex t]
  tmaximum0 :: TensorOf 1 r -> TensorOf 0 r
  tmaximum0 t = t ! [tmaxIndex t]
  tfromIntOf0 :: IntOf r -> TensorOf 0 r
  tfromIntOf0 = tscalar . fromIntegral  -- fails for the Ast instance

  -- Tensor codomain, often tensor construction, sometimes transformation
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
  tkonst0N ZS = id
  tkonst0N sh@(k :$ _) = treshape sh . tkonst k
  tappend :: KnownNat n
          => TensorOf (1 + n) r -> TensorOf (1 + n) r -> TensorOf (1 + n) r
  tslice :: KnownNat n => Int -> Int -> TensorOf (1 + n) r -> TensorOf (1 + n) r
  treverse :: KnownNat n => TensorOf n r -> TensorOf n r
  ttranspose :: KnownNat n => TensorOf n r -> TensorOf n r
  ttranspose = ttransposeGeneral [1, 0]
  ttransposeGeneral :: KnownNat n => Permutation -> TensorOf n r -> TensorOf n r
  tflatten :: KnownNat n => TensorOf n r -> TensorOf 1 r
  tflatten u = treshape (flattenShape $ tshape u) u
  treshape :: (KnownNat m, KnownNat n)
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
         => (r -> r) -> TensorOf n r -> TensorOf n r
  tmap0N f v = tbuild (tshape v)
                      (\ix -> tscalar $ f $ tunScalar $ v ! ix)
  tzipWith :: (KnownNat m, KnownNat n)
           => (TensorOf n r -> TensorOf n r -> TensorOf n r)
           -> TensorOf (m + n) r -> TensorOf (m + n) r -> TensorOf (m + n) r
  tzipWith f u v = tbuild (tshape v) (\ix -> f (u ! ix) (v ! ix))
  tzipWith1 :: KnownNat n
            => (TensorOf n r -> TensorOf n r -> TensorOf n r)
            -> TensorOf (1 + n) r -> TensorOf (1 + n) r -> TensorOf (1 + n) r
  tzipWith1 f u v = tbuild1 (tlength u) (\i -> f (u ! [i]) (v ! [i]))
  tzipWith0N :: KnownNat n
             => (r -> r -> r) -> TensorOf n r -> TensorOf n r -> TensorOf n r
  tzipWith0N f u v = tbuild (tshape v)
                            (\ix -> tscalar $ f (tunScalar $ u ! ix)
                                                (tunScalar $ v ! ix))

  tscalar :: r -> TensorOf 0 r
  tunScalar :: TensorOf 0 r -> r

type ADReady r = (Tensor r, HasPrimal r)
  -- TODO: there is probably no way to also specify
  -- HasPrimal (TensorOf 17 r))
  -- for all n, not just 17. That means the user needs add such
  -- constraints for all n relevant to the defined function (usually
  -- just an unspecified n and sometimes also n+1).

-- These instances are a faster way to get an objective function value.
-- However, they don't do vectorization, so won't work on GPU, ArrayFire, etc.
-- For vectorization, go through Ast and valueOnDomains.
instance Tensor Double where
  type TensorOf n Double = OR.Array n Double
  type IntOf Double = Int
  tshape = tshapeR
  tminIndex = tminIndexR
  tmaxIndex = tmaxIndexR
  tindex = tindexNR
  tsum = tsumR
  tsum0 = tscalar . tsum0R
  tdot0 u v = tscalar $ tdot0R u v
  tminimum0 = tscalar . tminimum0R
  tmaximum0 = tscalar . tmaximum0R
  tfromList = tfromListR
  tfromList0N = tfromList0NR
  tfromVector = tfromVectorR
  tfromVector0N = tfromVector0NR
  tkonst = tkonstR
  tkonst0N sh = tkonst0NR sh . tunScalar
  tappend = tappendR
  tslice = tsliceR
  treverse = treverseR
  ttransposeGeneral = ttransposeGeneralR
  treshape = treshapeR
  tbuild = tbuildNR
  tbuild1 = tbuild1R
  tscalar = tscalarR
  tunScalar = tunScalarR

instance Tensor Float where
  type TensorOf n Float = OR.Array n Float
  type IntOf Float = Int
  tshape = tshapeR
  tminIndex = tminIndexR
  tmaxIndex = tmaxIndexR
  tindex = tindexNR
  tsum = tsumR
  tsum0 = tscalar . tsum0R
  tdot0 u v = tscalar $ tdot0R u v
  tminimum0 = tscalar . tminimum0R
  tmaximum0 = tscalar . tmaximum0R
  tfromList = tfromListR
  tfromList0N = tfromList0NR
  tfromVector = tfromVectorR
  tfromVector0N = tfromVector0NR
  tkonst = tkonstR
  tkonst0N sh = tkonst0NR sh . tunScalar
  tappend = tappendR
  tslice = tsliceR
  treverse = treverseR
  ttransposeGeneral = ttransposeGeneralR
  treshape = treshapeR
  tbuild = tbuildNR
  tbuild1 = tbuild1R
  -- TODO: low priority: implement for speed and use for ADVal, too
  -- tmap = tmapR
  -- tmap0N = tmap0NR
  -- tzipWith = tzipWithR
  -- tzipWith0N = tzipWith0NR
  tscalar = tscalarR
  tunScalar = tunScalarR

-- Not that this instance doesn't do vectorization. To enable it,
-- use the Ast instance, which vectorizes and finally interpret in ADVal.
-- In principle, this instance is only useful for comparative tests,
-- though for code without build/map/etc., it should be equivalent
-- to going via Ast.
instance (ADModeAndNumTensor d r, TensorOf 1 r ~ OR.Array 1 r)
         => Tensor (ADVal d r) where
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
  tminIndex (D u _) = tminIndexR u
  tmaxIndex (D u _) = tmaxIndexR u

  tindex = indexN
  tsum = sum'
  tsum0 = tscalar . sum0
  tdot0 u v = tscalar $ dot0 u v
  tminimum0 (D u u') =
    let ix = tminIndex u
    in dD (tindex1R u ix) (dIndex1 u' ix (tlength u))
  tmaximum0 (D u u') =
    let ix = tmaxIndex u
    in dD (tindex1R u ix) (dIndex1 u' ix (tlength u))

  tfromList = fromList
  tfromList0N = fromList0N
  tfromVector = fromVector
  tfromVector0N = fromVector0N
  tkonst = konst
  tkonst0N sh = konst0N sh . unScalar
  tappend = append
  tslice = slice
  treverse = reverse'
  ttransposeGeneral = transposeGeneral
  treshape = reshape
  tbuild1 k f =
    let g i = let D u _ = f i in u
        h i = let D _ u' = f i in u'
    in dD (tbuild1R k g) (dBuild1 k h)
      -- uses the implementation that stores closures on tape to test against
      -- the elementwise implementation used by fallback from vectorizing Ast

  tscalar = scalar
  tunScalar = unScalar

instance ( Numeric r, RealFloat r, RealFloat (Vector r)
         , Show r, Numeric r )  -- needed only to display errors properly
         => Tensor (Ast 0 r) where
  type TensorOf n (Ast 0 r) = Ast n r
  type IntOf (Ast 0 r) = AstInt r

  tshape = shapeAst
  tminIndex = AstMinIndex
  tmaxIndex = AstMaxIndex

  tindex = AstIndexN
  tsum = AstSum
  tfromIntOf0 = AstConstInt
    -- toInteger is not defined for Ast, hence a special implementation

  tfromList = AstFromList
  tfromList0N sh = AstReshape sh . AstFromList
  tfromVector = AstFromVector
  tfromVector0N sh = AstReshape sh . AstFromVector
  tkonst = AstKonst
  tappend = AstAppend
  tslice = AstSlice
  treverse = AstReverse
  ttransposeGeneral = AstTransposeGeneral
  treshape = AstReshape
  tbuild1 = astBuild1

  tscalar = id  -- Ast confuses the two ranks
  tunScalar = id

instance ( Numeric r, RealFloat r, RealFloat (Vector r)
         , Show r, Numeric r )
         => Tensor (AstPrimalPart1 0 r) where
  type TensorOf n (AstPrimalPart1 0 r) = AstPrimalPart1 n r
  type IntOf (AstPrimalPart1 0 r) = AstInt r

  tshape = shapeAst . unAstPrimalPart
  tminIndex = AstMinIndex . unAstPrimalPart
  tmaxIndex = AstMaxIndex . unAstPrimalPart

  tindex v ix = AstPrimalPart1 $ AstIndexN (unAstPrimalPart v) ix
  tsum = AstPrimalPart1 . AstSum . unAstPrimalPart
  tfromIntOf0 = AstPrimalPart1 . AstConstInt
    -- toInteger is not defined for Ast, hence a special implementation

  tfromList = AstPrimalPart1 . AstFromList . map unAstPrimalPart
  tfromList0N sh =
    AstPrimalPart1 . AstReshape sh . AstFromList . map unAstPrimalPart
  tfromVector = AstPrimalPart1 . AstFromVector . V.map unAstPrimalPart
  tfromVector0N sh =
    AstPrimalPart1 . AstReshape sh . AstFromVector . V.map unAstPrimalPart
  tkonst k = AstPrimalPart1 . AstKonst k . unAstPrimalPart
  tappend u v =
    AstPrimalPart1 $ AstAppend (unAstPrimalPart u) (unAstPrimalPart v)
  tslice i k = AstPrimalPart1 . AstSlice i k  . unAstPrimalPart
  treverse = AstPrimalPart1 . AstReverse . unAstPrimalPart
  ttransposeGeneral perm =
    AstPrimalPart1 . AstTransposeGeneral perm . unAstPrimalPart
  treshape sh = AstPrimalPart1 . AstReshape sh  . unAstPrimalPart
  tbuild1 k f = AstPrimalPart1 $ astBuild1 k $ \ix -> unAstPrimalPart $ f ix

  tscalar = id
  tunScalar = id

astBuild1 :: (KnownNat n, Show r, Numeric r)
          => Int -> (AstInt r -> Ast n r) -> Ast (1 + n) r
{-# NOINLINE astBuild1 #-}
astBuild1 k f = unsafePerformIO $ do
  freshAstVar <- unsafeGetFreshAstVar
  return $! build1Vectorize k (freshAstVar, f (AstIntVar freshAstVar))
    -- TODO: this vectorizes depth-first, which is needed. But do we
    -- also need a translation to non-vectorized terms for anything
    -- (other than for comparative tests)?

-- A stub instance for experiments with stored functions
instance Tensor r
         => Tensor (a -> r) where
  type TensorOf n (a -> r) = ORB.Array n (a -> r)
  type IntOf (a -> r) = IntOf r


-- * ADVal combinators generalizing ranked tensor operations

shape :: KnownNat n => ADVal d (OR.Array n r) -> ShapeInt n
shape (D u _) = tshapeR u

-- | First index is for outermost dimension; empty index means identity.
-- TODO: speed up by using tindex0R and dIndex0 if the codomain is 0
-- and dD (u `tindex1R` ix) (dIndex1 u' ix (tlengthR u)) if only outermost
-- dimension affected.
indexN :: forall m n d r. (ADModeAndNumTensor d r, KnownNat m, KnownNat n)
       => ADVal d (OR.Array (m + n) r) -> IndexInt m
       -> ADVal d (OR.Array n r)
indexN (D u u') ixs = dD (tindexNR u ixs)
                         (dIndexN u' ixs (tshapeR u))

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
         => ADVal d (OR.Array n r) -> ADVal d (OR.Array n r)
reverse' (D u u') = dD (treverseR u) (dReverse1 u')

transposeGeneral :: (ADModeAndNumTensor d r, KnownNat n)
                 => Permutation
                 -> ADVal d (OR.Array n r) -> ADVal d (OR.Array n r)
transposeGeneral perm (D u u') = dD (ttransposeGeneralR perm u)
                                    (dTransposeGeneral1 perm u')

reshape :: (ADModeAndNumTensor d r, KnownNat m, KnownNat n)
        => ShapeInt m -> ADVal d (OR.Array n r) -> ADVal d (OR.Array m r)
reshape sh (D u u') = dD (treshapeR sh u) (dReshape1 (tshapeR u) sh u')

-- The element-wise (POPL) version, but only one rank at a time.
build1 :: (ADModeAndNumTensor d r, KnownNat n)
       => Int -> (Int -> ADVal d (OR.Array n r))
       -> ADVal d (OR.Array (1 + n) r)
build1 k f = fromList $ map f [0 .. k - 1]

gatherNClosure :: (ADModeAndNumTensor d r, KnownNat m, KnownNat p, KnownNat n)
               => (IndexInt m -> IndexInt p)
               -> ADVal d (OR.Array (p + n) r)
               -> ShapeInt (m + n) -> ADVal d (OR.Array (m + n) r)
gatherNClosure f (D u u') sh =
  dD (tgatherNR f u sh) (dGatherN f (tshapeR u) u' sh)

gather1Closure :: (ADModeAndNumTensor d r, KnownNat p, KnownNat n)
               => (Int -> IndexInt p)
               -> ADVal d (OR.Array (p + n) r)
               -> Int -> ADVal d (OR.Array (1 + n) r)
gather1Closure f (D u u') k = dD (tgather1R f u k) (dGather1 f (tshapeR u) u' k)

scalar :: ADModeAndNumTensor d r => ADVal d r -> ADVal d (OR.Array 0 r)
scalar (D u u') = dD (OR.scalar u) (dScalar1 u')

unScalar :: ADModeAndNumTensor d r => ADVal d (OR.Array 0 r) -> ADVal d r
unScalar (D u u') = dD (OR.unScalar u) (dUnScalar0 u')


-- * Interpretation of Ast in ADVal

type AstEnv (d :: ADMode) r = IM.IntMap (AstVar (ADVal d (OT.Array r)))

data AstVar a =
    AstVarR a
  | AstVarI Int
 deriving Show

interpretLambdaR
  :: ADModeAndNumTensor d r
  => AstEnv d r
  -> (AstVarName (OR.Array 0 r), Ast 0 r)
  -> ADVal d r -> ADVal d r
interpretLambdaR env (AstVarName var, ast) =
  \d -> let dT = from1X (scalar d)
        in unScalar $ interpretAst (IM.insert var (AstVarR dT) env) ast

interpretLambdaI
  :: (ADModeAndNumTensor d r, KnownNat n)
  => AstEnv d r
  -> (AstVarName Int, Ast n r)
  -> Int -> ADVal d (OR.Array n r)
interpretLambdaI env (AstVarName var, ast) =
  \i -> interpretAst (IM.insert var (AstVarI i) env) ast

interpretLambdaIndex
  :: ADModeAndNumTensor d r
  => AstEnv d r
  -> (AstVarName Int, AstIndex n r)
  -> Int -> IndexInt n
interpretLambdaIndex env (AstVarName var, asts) =
  \i -> fmap (interpretAstInt (IM.insert var (AstVarI i) env)) asts

interpretLambdaIndexToIndex
  :: ADModeAndNumTensor d r
  => AstEnv d r
  -> (AstVarList m, AstIndex p r)
  -> IndexInt m -> IndexInt p
interpretLambdaIndexToIndex env (vars, asts) =
  \ix -> let f (AstVarName var) i = (var, AstVarI i)
             assocs = zipWith f (sizedListToList vars) (indexToList ix)
             env2 = env `IM.union` IM.fromList assocs
         in fmap (interpretAstInt env2) asts

interpretAstPrimal
  :: (ADModeAndNumTensor d r, KnownNat n)
  => AstEnv d r
  -> Ast n r -> OR.Array n r
interpretAstPrimal env v = let D u _ = interpretAst env v in u

interpretAst
  :: (ADModeAndNumTensor d r, KnownNat n)
  => AstEnv d r
  -> Ast n r -> ADVal d (OR.Array n r)
interpretAst env = \case
  AstVar _sh (AstVarName var) -> case IM.lookup var env of
    Just (AstVarR d) -> fromX1 d
    Just AstVarI{} ->
      error $ "interpretAst: type mismatch for var " ++ show var
    Nothing -> error $ "interpretAst: unknown variable var " ++ show var
  AstOp opCode args ->
    interpretAstOp (interpretAst env) opCode args
  AstConst a -> constant a
  AstConstant (AstPrimalPart1 a) -> constant $ interpretAstPrimal env a
  AstScale (AstPrimalPart1 r) d ->
    scale (interpretAstPrimal env r) (interpretAst env d)
  AstCond b a1 a2 -> if interpretAstBool env b
                     then interpretAst env a1
                     else interpretAst env a2
  AstConstInt i -> fromIntegral $ interpretAstInt env i
  AstIndexN v is -> indexN (interpretAst env v) (fmap (interpretAstInt env) is)
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
  AstTranspose v -> interpretAst env $ AstTransposeGeneral [1, 0] v
  AstTransposeGeneral perm v ->
    let d@(D u _) = interpretAst env v
    in if OR.rank u < length perm then d else transposeGeneral perm d
  AstFlatten v -> let d = interpretAst env v
                  in reshape (flattenShape $ shape d) d
  AstReshape sh v -> reshape sh (interpretAst env v)
  AstBuild1 k (var, AstConstant r) ->
    constant
    $ OR.ravel . ORB.fromVector [k] . V.generate k
    $ \j -> let D v _ = interpretLambdaI env (var, AstConstant r) j
            in v
  AstBuild1 k (var, v) -> build1 k (interpretLambdaI env (var, v))
      -- fallback to POPL (memory blowup, but avoids functions on tape);
      -- an alternative is to use dBuild1 and store function on tape
  AstGather1 (var, ix) v k ->
    gather1Closure (interpretLambdaIndex env (var, ix)) (interpretAst env v) k
    -- TODO: currently we store the function on tape, because it doesn't
    -- cause recomputation of the gradient per-cell, unlike storing the build
    -- function on tape; for GPUs and libraries that don't understand Haskell
    -- closures, we cneck if the expressions involve tensor operations
    -- too hard for GPUs and, if not, we can store the AST expression
    -- on tape and translate it to whatever backend sooner or later;
    -- and if yes, fall back to POPL pre-computation that, unfortunately,
    -- leads to a tensor of deltas
  AstGatherN (vars, ix) v sh ->
    gatherNClosure (interpretLambdaIndexToIndex env (vars, ix))
                   (interpretAst env v) sh
  AstOMap (var, r) e ->  -- this only works on the primal part hence @constant@
    constant
    $ omap (\x -> let D u _ = interpretLambdaR env (var, r) (constant x)
                  in u)
           (interpretAstPrimal env e)

interpretAstInt :: ADModeAndNumTensor d r
                => AstEnv d r
                -> AstInt r -> Int
interpretAstInt env = \case
  AstIntVar (AstVarName var) -> case IM.lookup var env of
    Just AstVarR{} ->
      error $ "interpretAstInt: type mismatch for var " ++ show var
    Just (AstVarI i) -> i
    Nothing -> error $ "interpretAstInt: unknown variable var " ++ show var
  AstIntOp opCodeInt args ->
    interpretAstIntOp (interpretAstInt env) opCodeInt args
  AstIntConst a -> a
  AstIntFloor v -> floor $ interpretAst env v
  AstIntCond b a1 a2 -> if interpretAstBool env b
                        then interpretAstInt env a1
                        else interpretAstInt env a2
  AstMinIndex v -> tminIndex $ interpretAst env v
  AstMaxIndex v -> tmaxIndex $ interpretAst env v

interpretAstBool :: ADModeAndNumTensor d r
                 => AstEnv d r
                 -> AstBool r -> Bool
interpretAstBool env = \case
  AstBoolOp opCodeBool args ->
    interpretAstBoolOp (interpretAstBool env) opCodeBool args
  AstBoolConst a -> a
  AstRel opCodeRel args ->
    let f = interpretAstPrimal env
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
interpretAstBoolOp f IffOp [u, v] = f u == f v
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
