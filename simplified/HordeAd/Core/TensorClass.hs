{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleInstances,
             MultiParamTypeClasses, TypeFamilyDependencies #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Dual numbers and various operations on them, arithmetic and related
-- to tensors (vectors, matrices and others). This is a part of
-- the high-level API of the horde-ad library, defined using the mid-level
-- (and safely impure) API in "HordeAd.Core.DualClass". The other part
-- of the high-level API is in "HordeAd.Core.Engine".
module HordeAd.Core.TensorClass
  ( HasPrimal(..), Tensor(..)
  , interpretAst
  , ADReady
  , scalar, unScalar, leqAst, gtAst, gtIntAst, relu, reluLeaky, reluAst
  ) where

import Prelude

import qualified Data.Array.DynamicS as OT
import           Data.Array.Internal (valueOf)
import qualified Data.Array.Ranked as ORB
import qualified Data.Array.RankedS as OR
import           Data.IORef.Unboxed (Counter, atomicAddCounter_, newCounter)
import           Data.MonoTraversable (MonoFunctor (omap))
import qualified Data.Strict.IntMap as IM
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat, type (+))
import           Numeric.LinearAlgebra (Numeric, Vector)
import           System.IO.Unsafe (unsafePerformIO)
import           Unsafe.Coerce (unsafeCoerce)

import HordeAd.Core.Ast
import HordeAd.Core.DualClass
import HordeAd.Core.DualNumber
import HordeAd.Internal.SizedIndex
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
class (RealFloat r, RealFloat (TensorOf 1 r), Integral (IntOf r))
      => Tensor r where
  type TensorOf (n :: Nat) r = result | result -> n r
  type IntOf r

  tshape :: KnownNat n => TensorOf n r -> ShapeInt n
  tsize :: KnownNat n => TensorOf n r -> Int
  tsize = shapeSize . tshape
  tlength :: KnownNat n => TensorOf (1 + n) r -> Int
  tlength v = case tshape v of
    ZS -> error "tlength:  impossible pattern needlessly required"
    n :$ _ -> n
  tminIndex :: TensorOf 1 r -> IntOf r
  tmaxIndex :: TensorOf 1 r -> IntOf r

  tindex :: KnownNat n => TensorOf (1 + n) r -> IntOf r -> TensorOf n r
  tindexN :: (KnownNat n, KnownNat m)
          => TensorOf (m + n) r -> IndexOf m r -> TensorOf n r
  tsum :: KnownNat n => TensorOf (1 + n) r -> TensorOf n r
  tsum0 :: KnownNat n => TensorOf n r -> TensorOf 0 r
  tdot0 :: KnownNat n => TensorOf n r -> TensorOf n r -> TensorOf 0 r
  tminimum0 :: TensorOf 1 r -> TensorOf 0 r
  tmaximum0 :: TensorOf 1 r -> TensorOf 0 r
  tfromIntOf0 :: IntOf r -> TensorOf 0 r
  tfromIntOf0 = tscalar . fromIntegral

  tfromList :: KnownNat n => [TensorOf n r] -> TensorOf (1 + n) r
  tfromList0N :: KnownNat n => ShapeInt n -> [r] -> TensorOf n r
  tfromVector :: KnownNat n
              => Data.Vector.Vector (TensorOf n r) -> TensorOf (1 + n) r
  tfromVector0N :: KnownNat n
                => ShapeInt n -> Data.Vector.Vector r -> TensorOf n r
  tkonst :: KnownNat n => Int -> TensorOf n r -> TensorOf (1 + n) r
  tkonst0N :: KnownNat n => ShapeInt n -> r -> TensorOf n r
  tappend :: KnownNat n
          => TensorOf (1 + n) r -> TensorOf (1 + n) r -> TensorOf (1 + n) r
  tslice :: KnownNat n => Int -> Int -> TensorOf (1 + n) r -> TensorOf (1 + n) r
  treverse :: KnownNat n => TensorOf n r -> TensorOf n r
  ttranspose :: KnownNat n => TensorOf n r -> TensorOf n r
  ttranspose = ttransposeGeneral [1, 0]
  ttransposeGeneral :: KnownNat n => Permutation -> TensorOf n r -> TensorOf n r
  tflatten :: KnownNat n => TensorOf n r -> TensorOf 1 r
  tflatten u = treshape (flattenShape $ tshape u) u
  treshape :: (KnownNat n, KnownNat m)
           => ShapeInt m -> TensorOf n r -> TensorOf m r
  tbuild :: KnownNat n
         => Int -> (IntOf r -> TensorOf n r) -> TensorOf (1 + n) r
  tbuild0N :: KnownNat n => ShapeInt n -> (IndexOf n r -> r) -> TensorOf n r
  tmap :: KnownNat n
       => (TensorOf n r -> TensorOf n r)
       -> TensorOf (1 + n) r -> TensorOf (1 + n) r
  tmap f u = tbuild (tlength u) (\i -> f (u `tindex` i))
  tmap0N :: (r -> r) -> TensorOf 1 r -> TensorOf 1 r  -- TODO: less general type until sized lists let us type build0N sanely
  tzipWith :: KnownNat n
           => (TensorOf n r -> TensorOf n r -> TensorOf n r)
           -> TensorOf (1 + n) r -> TensorOf (1 + n) r -> TensorOf (1 + n) r
  tzipWith f u v = tbuild (tlength u) (\i -> f (u `tindex` i) (v `tindex` i))
  tzipWith0N :: KnownNat n
             => (r -> r -> r) -> TensorOf n r -> TensorOf n r -> TensorOf n r

  tscalar :: r -> TensorOf 0 r
  tunScalar :: TensorOf 0 r -> r

type ADReady r = ( Tensor r, HasPrimal r
                 , RealFloat (TensorOf 0 r), RealFloat (TensorOf 1 r) )
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
  tindex = tindexR
  tindexN = tindexNR
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
  tkonst0N = tkonst0NR
  tappend = tappendR
  tslice = tsliceR
  treverse = treverseR
  ttransposeGeneral = ttransposeGeneralR
  treshape = treshapeR
  tbuild = tbuildR
  tbuild0N = tbuild0NR
  tmap0N = tmap0NR
  tzipWith0N = tzipWith0NR
  tscalar = tscalarR
  tunScalar = tunScalarR

instance Tensor Float where
  type TensorOf n Float = OR.Array n Float
  type IntOf Float = Int
  tshape = tshapeR
  tminIndex = tminIndexR
  tmaxIndex = tmaxIndexR
  tindex = tindexR
  tindexN = tindexNR
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
  tkonst0N = tkonst0NR
  tappend = tappendR
  tslice = tsliceR
  treverse = treverseR
  ttransposeGeneral = ttransposeGeneralR
  treshape = treshapeR
  tbuild = tbuildR
  tbuild0N = tbuild0NR
  tmap0N = tmap0NR
  tzipWith0N = tzipWith0NR
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

  tindex = index
  tindexN = indexN
  tsum = sum'
  tsum0 = tscalar . sum0
  tdot0 u v = tscalar $ dot0 u v
  tminimum0 (D u u') =
    let ix = tminIndex u
    in dD (tindexR u ix) (dIndex1 u' ix (tlength u))
      -- no default methods for these two, because of the speedups like this
  tmaximum0 (D u u') =
    let ix = tmaxIndex u
    in dD (tindexR u ix) (dIndex1 u' ix (tlength u))

  tfromList = fromList
  tfromList0N = fromList0N
  tfromVector = fromVector
  tfromVector0N = fromVector0N
  tkonst = konst
  tkonst0N = konst0N
  tappend = append
  tslice = slice
  treverse = reverse'
  ttransposeGeneral = transposeGeneral
  treshape = reshape
  tbuild n f =
    let g i = let D u _ = f i in u
        h i = let D _ u' = f i in u'
    in dD (tbuildR n g) (dBuild1 n h)
      -- uses the implementation that stores closures on tape to test against
      -- the elementwise implementation used by fallback from vectorizing Ast
  tbuild0N sh f =
    let g ixs = let D u _ = f ixs in u
        h ixs = let D _ u' = f ixs in u'
    in dD (tbuild0NR sh g) (dBuild01 sh h)
  tmap0N f v = tbuild (tlength v) (\i -> scalar $ f (unScalar $ v `tindex` i))
  tzipWith0N = undefined  -- TODO

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

  tindex = AstIndex
  tindexN = AstIndexN
  tsum = AstSum
  tsum0 = AstSum0
  tdot0 = AstDot0
  tminimum0 v = AstIndex v (AstMinIndex v)
  tmaximum0 v = AstIndex v (AstMaxIndex v)
  tfromIntOf0 = AstConstInt
    -- toInteger is not defined for Ast, hence a special implementation

  tfromList = AstFromList
  tfromList0N = AstFromList0N
  tfromVector = AstFromVector
  tfromVector0N = AstFromVector0N
  tkonst = AstKonst
  tkonst0N = AstKonst0N
  tappend = AstAppend
  tslice = AstSlice
  treverse = AstReverse
  ttransposeGeneral = AstTransposeGeneral
  treshape = AstReshape
  tbuild = astBuild
  tbuild0N = undefined  -- TODO: type-level woes
  tmap0N f v = astBuild (tlength v) (\i -> f (v `tindex` i))
    -- TODO: without sharing v gets duplicated a lot
  tzipWith0N = undefined  -- TODO

  tscalar = id  -- Ast confuses the two ranks
  tunScalar = id

-- Impure but in the most trivial way (only ever incremented counter).
unsafeAstVarCounter :: Counter
{-# NOINLINE unsafeAstVarCounter #-}
unsafeAstVarCounter = unsafePerformIO (newCounter 0)

unsafeGetFreshAstVar :: IO (AstVarName a)
{-# INLINE unsafeGetFreshAstVar #-}
unsafeGetFreshAstVar = AstVarName <$> atomicAddCounter_ unsafeAstVarCounter 1

astBuild :: (KnownNat n, Show r, Numeric r)
         => Int -> (AstInt r -> Ast n r) -> Ast (1 + n) r
{-# NOINLINE astBuild #-}
astBuild n f = unsafePerformIO $ do
  freshAstVar <- unsafeGetFreshAstVar
  return $! build1Vectorize n ( freshAstVar
                              , (f (AstIntVar freshAstVar)) )
    -- TODO: this vectorizes depth-first, which is needed. But do we
    -- also need a translation to non-vectorized terms for anything
    -- (other than for comparative tests)?


-- * Vectorization of the build operation

build1Vectorize
  :: (KnownNat n, Show r, Numeric r)
  => Int -> (AstVarName Int, Ast n r) -> Ast (1 + n) r
build1Vectorize n (var, u) =
  if intVarInAst var u
  then build1VectorizeVar n (var, u)
  else AstKonst n u

-- | The variable is known to occur in the term.
build1VectorizeVar
  :: (KnownNat n, Show r, Numeric r)
  => Int -> (AstVarName Int, Ast n r) -> Ast (1 + n) r
build1VectorizeVar n (var, u) =
  case u of
    AstOp opCode args ->
      AstOp opCode $ map (\w -> build1Vectorize n (var, w)) args
    AstCond b v w ->
      build1VectorizeVar
        n (var, AstIndex (AstFromList [v, w]) (AstIntCond b 0 1))
    AstConstInt{} -> AstConstant $ AstPrimalPart1 $ AstBuildPair n (var, u)
    AstConst{} ->
      error "build1VectorizeVar: AstConst can't have free int variables"
    AstConstant{} -> AstConstant $ AstPrimalPart1 $ AstBuildPair n (var, u)
      -- this is very fast when interpreted in a smart way, but constant
      -- character needs to be exposed for nested cases;
      -- TODO: similarly propagate AstConstant upwards elsewhere
    AstScale (AstPrimalPart1 r) d ->
      AstScale (AstPrimalPart1 $ AstBuildPair n (var, r))  -- no need to vect
               (build1Vectorize n (var, d))
    AstVar{} ->
      error "build1VectorizeVar: AstVar can't have free int variables"

    AstIndex v i -> build1VectorizeIndex n var v (singletonIndex i)
      -- @var@ is in @v@ or @i@; TODO: simplify i first or even fully
      -- evaluate (may involve huge data processing) if contains no vars
      -- and then some things simplify a lot, e.g., if constant index,
      -- we may just pick the right element of a AstFromList
    AstIndexN v is -> build1VectorizeIndex n var v is
    AstSum v -> AstTranspose $ AstSum $ AstTranspose
                $ build1VectorizeVar n (var, v)
      -- that's because @build n (f . g) == map f (build n g)@
      -- and @map f == transpose1 . f . transpose1@
      -- TODO: though only for some f; check and fail early
    AstFromList l ->
      AstTranspose
      $ AstFromList (map (\v -> build1Vectorize n (var, v)) l)
    AstFromVector l ->
      AstTranspose
      $ AstFromVector (V.map (\v -> build1Vectorize n (var, v)) l)
    AstKonst k v -> AstTranspose $ AstKonst k $ AstTranspose
                    $ build1VectorizeVar n (var, v)
    AstAppend v w -> AstTranspose $ AstAppend
                       (AstTranspose $ build1Vectorize n (var, v))
                       (AstTranspose $ build1Vectorize n (var, w))
    AstSlice i k v -> AstTranspose $ AstSlice i k $ AstTranspose
                      $ build1VectorizeVar n (var, v)
    AstReverse v -> AstTranspose $ AstReverse $ AstTranspose
                    $ build1VectorizeVar n (var, v)
    AstTranspose v ->
      build1VectorizeVar n (var, AstTransposeGeneral [1, 0] v)
    AstTransposeGeneral perm v -> AstTransposeGeneral (0 : map succ perm)
                                  $ build1VectorizeVar n (var, v)
    AstFlatten v ->
      build1VectorizeVar n (var, AstReshape (flattenShape $ shapeAst u) v)
    AstReshape sh v -> AstReshape (n :$ sh) $ build1VectorizeVar n (var, v)
    AstBuildPair{} -> AstBuildPair n (var, u)
      -- TODO: a previous failure of vectorization that should have
      -- led to an abort instead of showing up late; or not, see below
    AstGatherPair _n (_var2, _ixs2) _v -> AstBuildPair n (var, u)
      -- TODO: if var not in _v, then create a generalized gather
      -- that builds more than one rank using var and var2 together;
      -- then the function would be from a list of build1 indexes,
      -- but for this I *really* need a Nat-sized list, becuause I will
      -- then need to vectorize buildN and so all vectorization function
      -- signatures will contain complex type-level arithmetic
    -- AstScatterPair (var2, ixs2) v sh -> ...
    -- no idea how to vectorize AstScatterPair, so let's not add it prematurely

    -- Rewriting syntactic sugar in the simplest way (but much more efficient
    -- non-sugar implementations/vectorizations exist):
    AstSum0 v -> build1VectorizeVar n (var, AstSum $ AstFlatten v)
    AstDot0 v w ->
      build1VectorizeVar n (var, AstSum (AstOp TimesOp [ AstFlatten v
                                                          , AstFlatten w ]))
      -- AstDot1 is dubious, because dot product results in a scalar,
      -- not in one rank less and also (some) fast implementations
      -- depend on it resulting in a scalar.
      -- AstOp does not require Numeric constraint, so better than @*@.
    AstFromList0N sh l ->
      build1VectorizeVar n (var, AstReshape sh $ AstFromList l)
    AstFromVector0N sh l ->
      build1VectorizeVar n (var, AstReshape sh $ AstFromVector l)
    AstKonst0N sh v ->
      let k = shapeSize sh
      in build1VectorizeVar n (var, AstReshape sh $ AstKonst k v)
    AstBuildPair0N{} -> AstBuildPair n (var, u)  -- see AstBuildPair above

    AstOMap{} -> AstConstant $ AstPrimalPart1 $ AstBuildPair n (var, u)
    -- All other patterns are redundant due to GADT typing.

-- | The application @build1VectorizeIndex n var v is@
-- vectorizes the term @AstBuildPair n (var, AstIndexN v is@.
-- The length of the index is @m@
--
-- We try to push indexing down as far as needed to eliminated the occurence
-- of @var@ from @v@ (but not necessarily from @is@).
build1VectorizeIndex
  :: forall m n r. (KnownNat n, KnownNat m, Show r, Numeric r)
  => Int -> AstVarName Int -> Ast (m + n) r -> AstIndex m r
  -> Ast (1 + n) r
build1VectorizeIndex n var v Z =
  unsafeCoerce $ build1Vectorize n (var, v)
build1VectorizeIndex n var v is@(iN :. restN) =
  if | intVarInAst var v -> build1VectorizeIndexVar n var v is  -- push deeper
     | or (fmap (intVarInAstInt var) restN) -> AstGatherPair n (var, is) v
     | intVarInAstInt var iN ->
       let w = AstIndexN v restN
       in case build1VectorizeIndexAnalyze n var w iN of
            Just u -> u  -- an extremely simple form found
            Nothing -> AstGatherPair n (var, is) v
              -- we didn't really need it anyway
     | otherwise -> AstKonst n (AstIndexN v is)

-- | The variable is known to occur in the main vectorized term.
-- We try to push the indexing down the term tree and partially
-- evaluate/simplify the term, if only possible in constant time.
build1VectorizeIndexVar
  :: forall m n r. (KnownNat n, KnownNat m, Show r, Numeric r)
  => Int -> AstVarName Int -> Ast (m + n) r -> AstIndex m r
  -> Ast (1 + n) r
build1VectorizeIndexVar n var v1 Z =
  unsafeCoerce $ build1VectorizeVar n (var, v1)
build1VectorizeIndexVar n var v1 is@(_ :. _) =
  let (rest1, i1) = unsnocIndex is  -- TODO: rename to (init1, last1)?
  in case v1 of
    AstOp opCode args ->
      AstOp opCode $ map (\w -> build1VectorizeIndex n var w is) args
    AstCond b v w ->
      build1VectorizeIndex n var (AstFromList [v, w])
                           (snocIndex is (AstIntCond b 0 1))
    AstConstInt{} ->
      AstConstant $ AstPrimalPart1 $ AstBuildPair @n n (var, AstIndexN v1 is)
    AstConst{} ->
      error "build1VectorizeIndexVar: AstConst can't have free int variables"
    AstConstant{} ->
      AstConstant $ AstPrimalPart1 $ AstBuildPair n (var, AstIndexN v1 is)
    AstScale (AstPrimalPart1 r) d ->
      AstScale (AstPrimalPart1 $ AstBuildPair n (var, AstIndexN r is))
               (build1VectorizeIndex n var d is)
    AstVar{} ->
      error "build1VectorizeIndexVar: AstVar can't have free int variables"

    AstIndex v i -> build1VectorizeIndex n var v (snocIndex is i)
    AstIndexN v is2 -> build1VectorizeIndex n var v (appendIndex is is2)
    AstSum v ->
      build1VectorizeVar n
        (var, AstSum (AstTranspose $ AstIndexN (AstTranspose v) is))
          -- that's because @index (sum v) i == sum (map (index i) v)@
    AstFromList l | intVarInAstInt var i1 ->
      -- This is pure desperation. I build separately for each list element,
      -- instead of picking the right element for each build iteration
      -- (which to pick depends on the build variable).
      -- @build1VectorizeIndexAnalyze@ is not applicable, because var is in v1.
      -- The only thing to do is constructing a AstGatherPair via a trick.
      -- There's no other reduction left to perform and hope the build vanishes.
      let t = AstFromList $ map (\v ->
            build1Vectorize n (var, AstIndexN v rest1)) l
      in AstGatherPair n (var, i1 :. AstIntVar var :. Z) t
    AstFromList l ->
      AstIndex (AstFromList $ map (\v ->
        build1Vectorize n (var, AstIndexN v rest1)) l) i1
    AstFromVector l | intVarInAstInt var i1 ->
      let t = AstFromVector $ V.map (\v ->
            build1Vectorize n (var, AstIndexN v rest1)) l
      in AstGatherPair n (var, i1 :. AstIntVar var :. Z) t
    AstFromVector l ->
      AstIndex (AstFromVector $ V.map (\v ->
        build1Vectorize n (var, AstIndexN v rest1)) l) i1
    -- Partially evaluate in constant time:
    AstKonst _k v -> build1VectorizeIndexVar n var v rest1
    AstAppend v w ->
      let vlen = AstIntConst $ lengthAst v
          is2 = fmap (\i -> AstIntOp PlusIntOp [i, vlen]) is
      in build1Vectorize n
           (var, AstCond (AstRelInt LsOp [i1, vlen])
                         (AstIndexN v is)
                         (AstIndexN w is2))
          -- this is basically partial evaluation, but in constant
          -- time unlike evaluating AstFromList, etc.
    AstSlice i2 _k v ->
      build1VectorizeIndexVar n var v (fmap (\i ->
        AstIntOp PlusIntOp [i, AstIntConst i2]) is)
    AstReverse v ->
      let revIs = AstIntOp MinusIntOp [AstIntConst (lengthAst v - 1), i1]
                  :. rest1
      in build1VectorizeIndexVar n var v revIs
    AstTranspose v -> case (rest1, shapeAst v) of
      (Z, ZS) ->
        build1VectorizeIndexVar @m @n n var v is  -- if rank too low, it's id
      (Z, _ :$ ZS) ->
        build1VectorizeIndexVar n var v is  -- if rank too low, it's id
      (Z, _) -> AstBuildPair n (var, AstIndexN v1 is)  -- we give up
      (i2 :. rest2, _) -> build1VectorizeIndexVar n var v (i2 :. i1 :. rest2)
    AstTransposeGeneral perm v ->
      let lenp = length perm
          is2 = permutePrefixIndex perm is
      in if | valueOf @(m + n) < lenp ->
                build1VectorizeIndexVar n var v is
                  -- the operation is an identity if rank too small
            | valueOf @m < lenp ->
                AstBuildPair n (var, AstIndexN v1 is)  -- we give up
                  -- TODO: for this we really need generalized paths that
                  -- first project, then transpose and generalized gather;
                  -- or instead push down transpose, but it may be expensive
                  -- or get stuck as well
            | otherwise -> build1VectorizeIndexVar n var v is2
    AstFlatten v -> case rest1 of
      Z ->
        let ixs2 = fromLinearIdx (fmap AstIntConst (shapeAst v)) i1
        in build1VectorizeIndexVar n var v ixs2
      _ -> error "build1VectorizeIndexVar: AstFlatten: impossible pattern needlessly required"
    AstReshape{} -> AstBuildPair n (var, AstIndexN v1 is)  -- we give up
      {- TODO: This angle of attack fails, because AstSlice with variable
         first argument doesn't vectorize in build1Vectorize. For it
         to vectorize, we'd need a new operation, akin to gather,
         with the semantics of build (slice), a gradient, a way to vectorize
         it, in turn, normally and with indexing applied, etc.
      let i = toLinearIdx2 (fmap AstIntConst sh) is
          -- This converts indexing into a slice and flatten, which in general
          -- is avoided, because it causes costly linearlization, but here
          -- we are going to reshape outside, anyway, and also we are desperate.
          -- BTW, slice has to accept variable first argument precisely
          -- to be usable for convering indexing into. Note that this argument
          -- does not affect shape, so shapes remain static.
          v2 = AstSlice i (product $ drop (length is) sh) $ AstFlatten v
      in AstReshape (n : sh) $ build1VectorizeVar n (var, v2)
      -}
    AstBuildPair _n2 (var2, v) ->
      -- TODO: a previous failure of vectorization that should have
      -- led to an abort instead of showing up late
      -- TODO: or a wonderful chance to recover failed vectorization,
      -- by taking only an element of this build! so shall failed
      -- vectorization not abort, after all? and only check at whole program
      -- vectorization end that no build has been left unvectorized?
      build1VectorizeIndexVar n var (substituteAst i1 var2 v) rest1
    AstGatherPair _n2 (var2, ixs2) v ->
      let ixs3 = fmap (substituteAstInt i1 var2) ixs2
      in build1VectorizeIndex n var v (appendIndex rest1 ixs3)

    AstSum0{} -> error "build1VectorizeIndexVar: wrong rank"
    AstDot0{} -> error "build1VectorizeIndexVar: wrong rank"
    AstFromList0N sh l ->
      build1VectorizeIndexVar n var (AstReshape sh $ AstFromList l) is
    AstFromVector0N sh l ->
      build1VectorizeIndexVar n var (AstReshape sh $ AstFromVector l) is
    AstKonst0N sh v ->
      let k = shapeSize sh
      in build1VectorizeIndexVar n var (AstReshape sh $ AstKonst k v) is
    AstBuildPair0N _sh ([], _r) ->
      error "build1VectorizeIndexVar: impossible case; is would have to be []"
    -- TODO: too hard until we have a sized list of variables names
    -- so we coerce for now:
    AstBuildPair0N sh (var2 : vars, r) ->
      build1VectorizeIndexVar
        n var (unsafeCoerce $ AstBuildPair0N sh (vars, substituteAst i1 var2 r)) rest1

    AstOMap{} ->
      AstConstant $ AstPrimalPart1 $ AstBuildPair n (var, AstIndexN v1 is)
    -- All other patterns are redundant due to GADT typing.

-- TODO: we probably need to simplify to some normal form, but possibly
-- this would be even better to do and take advantage of earlier,
-- perhaps even avoiding pushing all the other indexing down
build1VectorizeIndexAnalyze
  :: forall n r.
     Int -> AstVarName Int -> Ast (1 + n) r -> AstInt r
  -> Maybe (Ast (1 + n) r)
build1VectorizeIndexAnalyze n var v iN = case iN of
  AstIntVar var2 | var2 == var ->
    Just $ AstSlice 0 n v
  AstIntOp PlusIntOp [AstIntVar var2, AstIntConst i2] | var2 == var ->
      Just $ AstSlice i2 n v
  AstIntOp PlusIntOp [AstIntConst i2, AstIntVar var2] | var2 == var ->
      Just $ AstSlice i2 n v
  _ -> Nothing
    -- TODO: many more cases; not sure how systematic it can be;
    -- more cases are possible if shapes can contain Ast variables;
    -- @Data.Array.Shaped@ doesn't help in this case;
    -- however, AstGatherPair covers all this, at the cost of relatively
    -- simple expressions on tape

intVarInAst :: AstVarName Int -> Ast n r -> Bool
intVarInAst var = \case
  AstOp _ l -> or $ map (intVarInAst var) l
  AstCond b x y ->
    intVarInAstBool var b || intVarInAst var x || intVarInAst var y
  AstConstInt n -> intVarInAstInt var n
  AstConst{} -> False
  AstConstant (AstPrimalPart1 v) -> intVarInAst var v
  AstScale (AstPrimalPart1 v) u -> intVarInAst var v || intVarInAst var u
  AstVar{} -> False  -- not an int variable

  AstIndex v ix -> intVarInAst var v || intVarInAstInt var ix
  AstIndexN v is -> intVarInAst var v || or (fmap (intVarInAstInt var) is)
  AstSum v -> intVarInAst var v
  AstFromList l -> or $ map (intVarInAst var) l  -- down from rank 1 to 0
  AstFromVector vl -> or $ map (intVarInAst var) $ V.toList vl
  AstKonst _ v -> intVarInAst var v
  AstAppend v u -> intVarInAst var v || intVarInAst var u
  AstSlice _ _ v -> intVarInAst var v
  AstReverse v -> intVarInAst var v
  AstTranspose v -> intVarInAst var v
  AstTransposeGeneral _ v -> intVarInAst var v
  AstFlatten v -> intVarInAst var v
  AstReshape _ v -> intVarInAst var v
  AstBuildPair _ (_, v) -> intVarInAst var v
  AstGatherPair _ (_, is) v -> or (fmap (intVarInAstInt var) is)
                               || intVarInAst var v

  AstSum0 v -> intVarInAst var v
  AstDot0 v u -> intVarInAst var v || intVarInAst var u
  AstFromList0N _ l -> or (map (intVarInAst var) l)
  AstFromVector0N _ l -> V.or (V.map (intVarInAst var) l)
  AstKonst0N _ v -> intVarInAst var v
  AstBuildPair0N _ (_, v) -> intVarInAst var v

  AstOMap (_, v) u -> intVarInAst var v || intVarInAst var u
    -- the variable in binder position, so ignored (and should be distinct)

intVarInAstInt :: AstVarName Int -> AstInt r -> Bool
intVarInAstInt var = \case
  AstIntOp _ l -> or $ fmap (intVarInAstInt var) l
  AstIntCond b x y ->
    intVarInAstBool var b || intVarInAstInt var x || intVarInAstInt var y
  AstIntConst{} -> False
  AstIntVar var2 -> var == var2  -- the only int variable not in binder position
  AstMinIndex v -> intVarInAst var v
  AstMaxIndex v -> intVarInAst var v

intVarInAstBool :: AstVarName Int -> AstBool r -> Bool
intVarInAstBool var = \case
  AstBoolOp _ l -> or $ map (intVarInAstBool var) l
  AstBoolConst{} -> False
  AstRel _ l -> or $ map (intVarInAst var) l
  AstRelInt _ l  -> or $ fmap (intVarInAstInt var) l


-- * ADVal combinators generalizing ranked tensor operations

shape :: KnownNat n => ADVal d (OR.Array n r) -> ShapeInt n
shape (D u _) = tshapeR u

-- First come definition of some ADVal combinators to be used below.
-- They are more general than their legacy versions for rank 1 above
-- and sometimes more general than the Ast operations.
index :: (ADModeAndNumTensor d r, KnownNat n)
      => ADVal d (OR.Array (1 + n) r) -> Int -> ADVal d (OR.Array n r)
index (D u u') ix = dD (u `tindexR` ix) (dIndex1 u' ix (tlengthR u))

-- | First index is for outermost dimension; empty index means identity.
-- TODO: speed up by using atPathInTensorR and dIndex0 if the codomain is 0.
indexN :: forall m n d r. (ADModeAndNumTensor d r, KnownNat n, KnownNat m)
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

unScalar :: ADModeAndNumTensor d r => ADVal d (OR.Array 0 r) -> ADVal d r
unScalar (D u u') = dD (OR.unScalar u) (dUnScalar0 u')

scalar :: ADModeAndNumTensor d r => ADVal d r -> ADVal d (OR.Array 0 r)
scalar (D u u') = dD (OR.scalar u) (dScalar1 u')

fromList :: (ADModeAndNumTensor d r, KnownNat n)
         => [ADVal d (OR.Array n r)]
         -> ADVal d (OR.Array (1 + n) r)
fromList lu =
  -- TODO: if lu is empty, crash if n =\ 0 or use List.NonEmpty.
  dD (tfromListR $ map (\(D u _) -> u) lu)
     (dFromList1 $ map (\(D _ u') -> u') lu)

fromVector :: (ADModeAndNumTensor d r, KnownNat n)
           => Data.Vector.Vector (ADVal d (OR.Array n r))
           -> ADVal d (OR.Array (1 + n) r)
fromVector lu =
  dD (tfromVectorR $ V.map (\(D u _) -> u) lu)
     (dFromVector1 $ V.map (\(D _ u') -> u') lu)

fromList0N :: (ADModeAndNumTensor d r, KnownNat n)
           => ShapeInt n -> [ADVal d r]
           -> ADVal d (OR.Array n r)
fromList0N sh l =
  dD (tfromList0NR sh $ map (\(D u _) -> u) l)  -- I hope this fuses
     (dFromList01 sh $ map (\(D _ u') -> u') l)

fromVector0N :: (ADModeAndNumTensor d r, KnownNat n)
             => ShapeInt n -> Data.Vector.Vector (ADVal d r)
             -> ADVal d (OR.Array n r)
fromVector0N sh l =
  dD (tfromVector0NR sh $ V.convert $ V.map (\(D u _) -> u) l)  -- hope it fuses
     (dFromVector01 sh $ V.map (\(D _ u') -> u') l)

konst :: (ADModeAndNumTensor d r, KnownNat n)
      => Int -> ADVal d (OR.Array n r) -> ADVal d (OR.Array (1 + n) r)
konst n (D u u') = dD (tkonstR n u) (dKonst1 n u')

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

reshape :: (ADModeAndNumTensor d r, KnownNat n, KnownNat m)
        => ShapeInt m -> ADVal d (OR.Array n r) -> ADVal d (OR.Array m r)
reshape sh (D u u') = dD (treshapeR sh u) (dReshape1 (tshapeR u) sh u')

-- The element-wise (POPL) version, but only one rank at a time.
build :: (ADModeAndNumTensor d r, KnownNat n)
      => Int -> (Int -> ADVal d (OR.Array n r))
      -> ADVal d (OR.Array (1 + n) r)
build n f = fromList $ map f [0 .. n - 1]

gatherClosure :: (ADModeAndNumTensor d r, KnownNat n, KnownNat m)
              => Int -> (Int -> IndexInt m)
              -> ADVal d (OR.Array (m + n) r) -> ADVal d (OR.Array (1 + n) r)
gatherClosure n f (D u u') = dD (tgatherR n f u) (dGather1 n f (tshapeR u) u')


-- * Interpretation of Ast in ADVal

type AstEnv (d :: ADMode) r = IM.IntMap (AstVar (ADVal d (OT.Array r)))

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

interpretLambdaPath
  :: ADModeAndNumTensor d r
  => AstEnv d r
  -> (AstVarName Int, AstIndex n r)
  -> Int -> IndexInt n
interpretLambdaPath env (AstVarName var, asts) =
  \i -> fmap (interpretAstInt (IM.insert var (AstVarI i) env)) asts

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
  AstOp opCode args ->
    interpretAstOp (interpretAst env) opCode args
  AstCond b a1 a2 -> if interpretAstBool env b
                     then interpretAst env a1
                     else interpretAst env a2
  AstConstInt i -> fromIntegral $ interpretAstInt env i
  AstConst a -> constant a
  AstConstant (AstPrimalPart1 a) -> constant $ interpretAstPrimal env a
  AstScale (AstPrimalPart1 r) d ->
    scale (interpretAstPrimal env r) (interpretAst env d)
  AstVar _sh (AstVarName var) -> case IM.lookup var env of
    Just (AstVarR d) -> fromX1 d
    Just AstVarI{} ->
      error $ "interpretAst: type mismatch for var " ++ show var
    Nothing -> error $ "interpretAst: unknown variable var " ++ show var

  AstIndex v i -> index (interpretAst env v) (interpretAstInt env i)
  AstIndexN v is -> indexN (interpretAst env v) (fmap (interpretAstInt env) is)
  AstSum v -> sum' (interpretAst env v)
  AstFromList l -> fromList (map (interpretAst env) l)
  AstFromVector l -> fromVector (V.map (interpretAst env) l)
  AstKonst n v -> konst n (interpretAst env v)
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
  AstBuildPair n (var, AstConstant r) ->
    constant
    $ OR.ravel . ORB.fromVector [n] . V.generate n
    $ \j -> let D v _ = interpretLambdaI env (var, AstConstant r) j
            in v
  AstBuildPair n (var, v) -> build n (interpretLambdaI env (var, v))
      -- fallback to POPL (memory blowup, but avoids functions on tape);
      -- an alternative is to use dBuild1 and store function on tape
  AstGatherPair n (var, is) v ->
    gatherClosure n (interpretLambdaPath env (var, is)) (interpretAst env v)
    -- TODO: currently we store the function on tape, because it doesn't
    -- cause recomputation of the gradient per-cell, unlike storing the build
    -- function on tape; for GPUs and libraries that don't understand Haskell
    -- closures, we cneck if the expressions involve tensor operations
    -- too hard for GPUs and, if not, we can store the AST expression
    -- on tape and translate it to whatever backend sooner or later;
    -- and if yes, fall back to POPL pre-computation that, unfortunately,
    -- leads to a tensor of deltas

  AstSum0 v -> scalar $ sum0 (interpretAst env v)
  AstDot0 x y -> scalar $ dot0 (interpretAst env x) (interpretAst env y)
  AstFromList0N sh l ->
    fromList0N sh $ map (unScalar . interpretAst env) l
  AstFromVector0N sh l ->
    fromVector0N sh $ V.map (unScalar . interpretAst env) l
  AstKonst0N sh r -> konst0N sh (unScalar $ interpretAst env r)
  AstBuildPair0N _sh (_vars, _r) -> undefined  -- TODO: type-level woes
    -- TODO: wait if vectorization forces us to generalize this to accept
    -- any rank and build it up according to @sh@ (which will then be
    -- only a partial shape, so should change its name)

  AstOMap (var, r) e ->  -- this only works on the primal part hence @constant@
    constant
    $ omap (\x -> let D u _ = interpretLambdaR env (var, r) (constant x)
                  in u)
           (interpretAstPrimal env e)

interpretAstInt :: ADModeAndNumTensor d r
                => AstEnv d r
                -> AstInt r -> Int
interpretAstInt env = \case
  AstIntOp opCodeInt args ->
    interpretAstIntOp (interpretAstInt env) opCodeInt args
  AstIntCond b a1 a2 -> if interpretAstBool env b
                        then interpretAstInt env a1
                        else interpretAstInt env a2
  AstIntConst a -> a
  AstIntVar (AstVarName var) -> case IM.lookup var env of
    Just AstVarR{} ->
      error $ "interpretAstInt: type mismatch for var " ++ show var
    Just (AstVarI i) -> i
    Nothing -> error $ "interpretAstInt: unknown variable var " ++ show var
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
    let f x = interpretAstPrimal env x
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
