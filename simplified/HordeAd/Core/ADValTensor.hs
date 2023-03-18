{-# LANGUAGE OverloadedLists, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Dual numbers and various operations on them, arithmetic and related
-- to tensors (vectors, matrices and others). This is a part of
-- the high-level API of the horde-ad library, defined using the mid-level
-- (and safely impure) API in "HordeAd.Core.DualClass". The other part
-- of the high-level API is in "HordeAd.Core.Engine".
module HordeAd.Core.ADValTensor
  ( InterpretAst(..), AstVar(..), funToAstR, funToAstD, simplifyAst, extendEnvR
  , resetVarCOunter
  ) where


import Prelude hiding ((<*))

import qualified Data.Array.DynamicS as OT
import qualified Data.Array.Ranked as ORB
import qualified Data.Array.RankedS as OR
import           Data.Boolean
import qualified Data.Strict.IntMap as IM
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, type (+))
import           Numeric.LinearAlgebra (Numeric, Vector)

import HordeAd.Core.Ast
import HordeAd.Core.AstSimplify
import HordeAd.Core.AstVectorize ()
import HordeAd.Core.DualClass
import HordeAd.Core.DualNumber hiding (build1)
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorClass
import HordeAd.Internal.SizedList
import HordeAd.Internal.TensorOps

instance (RealFloat r, Floating (Vector r), Numeric r, Show r, KnownNat n)
         => IfB (ADVal (Ast n r)) where
  ifB b v w = tindex (tfromList [v, w]) (singletonIndex $ ifB b 0 1)

instance (RealFloat r, Floating (Vector r), Numeric r, Show r)
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

instance HasPrimal (ADVal Double) where
  type ScalarOf (ADVal Double) = Double
  type Primal (ADVal Double) = Double
  type DualOf n (ADVal Double) = Dual (OR.Array n Double)
  tconst t = dD t dZero
  tconstant t = dD (toArray t) dZero
  tprimalPart (D u _) = fromArray u
  tdualPart (D _ u') = u'
  tD u = dD (toArray u)
  type DynamicTensor (ADVal Double) = ADVal (OT.Array Double)
  tdummyD = undefined  -- not used for dual numbers
  tisDummyD = undefined  -- not used for dual numbers
  taddD = (+)
  tshapeD (D u _) = OT.shapeL u
  tfromR = from1X
  tfromD = fromX1

instance HasPrimal (ADVal Float) where
  type ScalarOf (ADVal Float) = Float
  type Primal (ADVal Float) = Float
  type DualOf n (ADVal Float) = Dual (OR.Array n Float)
  tconst t = dD t dZero
  tconstant t = dD (toArray t) dZero
  tprimalPart (D u _) = fromArray u
  tdualPart (D _ u') = u'
  tD u = dD (toArray u)
  -- TODO: if ever used, define, if not, use an Error type
  type DynamicTensor (ADVal Float) = ADVal (OT.Array Float)
  tdummyD = undefined  -- not used for dual numbers
  tisDummyD = undefined  -- not used for dual numbers
  taddD = (+)
  tshapeD (D u _) = OT.shapeL u
  tfromR = from1X
  tfromD = fromX1

instance (ADTensor (Ast0 r), Numeric r, Show r)
         => HasPrimal (ADVal (Ast0 r)) where
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
  tfromR = from1X
  tfromD = fromX1


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

type AstEnv a = IM.IntMap (AstVar a)

data AstVar a =
    AstVarR (DynamicTensor a)
  | AstVarI (IntOf a)

deriving instance (Show (DynamicTensor a), Show (IntOf a)) => Show (AstVar a)

extendEnvR :: forall n a. (HasPrimal a, KnownNat n)
           => AstVarName (TensorOf n (ScalarOf a)) -> TensorOf n a
           -> AstEnv a -> AstEnv a
extendEnvR v@(AstVarName var) d =
  IM.insertWithKey (\_ _ _ -> error $ "extendEnvR: duplicate " ++ show v)
                   var (AstVarR $ tfromR d)

extendEnvI :: AstVarName Int -> IntOf a
           -> AstEnv a -> AstEnv a
extendEnvI v@(AstVarName var) i =
  IM.insertWithKey (\_ _ _ -> error $ "extendEnvI: duplicate " ++ show v)
                   var (AstVarI i)

extendEnvVars :: AstVarList m -> IndexOf m a
              -> AstEnv a -> AstEnv a
extendEnvVars vars ix env =
  let assocs = zip (sizedListToList vars) (indexToList ix)
  in foldr (uncurry extendEnvI) env assocs

interpretLambdaI
  :: (AstEnv c -> a -> b)
  -> AstEnv c -> (AstVarName Int, a) -> IntOf c
  -> b
{-# INLINE interpretLambdaI #-}
interpretLambdaI f env (var, ast) =
  \i -> f (extendEnvI var i env) ast

interpretLambdaIndexToIndex
  :: (AstEnv a -> AstInt q -> IntOf a)
  -> AstEnv a -> (AstVarList m, AstIndex p q) -> IndexOf m a
  -> IndexOf p a
{-# INLINE interpretLambdaIndexToIndex #-}
interpretLambdaIndexToIndex f env (vars, asts) =
  \ix -> fmap (f (extendEnvVars vars ix env)) asts

class InterpretAst a where
  interpretAst
    :: forall n. KnownNat n
    => AstEnv a -> Ast n (ScalarOf a) -> TensorOf n a
  interpretAstDynamic
    :: AstEnv a -> AstDynamic (ScalarOf a) -> DynamicTensor a

-- These are several copies of exactly the same code, past the instantiated
-- interpretAst signature. See if any workaround from
-- https://gitlab.haskell.org/ghc/ghc/-/issues/14860 and
-- https://gitlab.haskell.org/ghc/ghc/-/issues/16365 work here
-- (and elsewhere, where we copy code for similar reasons).
instance InterpretAst (ADVal Double) where
 interpretAst
   :: forall n0 a. (KnownNat n0, a ~ ADVal Double)
   => AstEnv a -> Ast n0 (ScalarOf a) -> TensorOf n0 a
 interpretAst = interpretAstRec
  where
-- We could duplicate interpretAst to save some time (sadly, we can't
-- interpret Ast uniformly in any Tensor and HasPrimal instance due to typing,
-- so we can't just use an instance of interpretation to OR.Array for that),
-- but it's not a huge saving, because all dual parts are gone before
-- we do any differentiation and they are mostly symbolic, so don't even
-- double the amount of tensor computation performed. The biggest problem is
-- allocation of tensors, but they are mostly shared with the primal part.
   interpretAstPrimal
     :: forall n. KnownNat n
     => AstEnv a
     -> AstPrimalPart n (ScalarOf a) -> TensorOf n (Primal a)
   interpretAstPrimal env (AstPrimalPart v) =
     toArray $ tprimalPart $ interpretAstRec env v

   interpretAstRec
     :: forall n. KnownNat n
     => AstEnv a
     -> Ast n (ScalarOf a) -> TensorOf n a
   interpretAstRec env = \case
     AstVar _sh (AstVarName var) -> case IM.lookup var env of
       Just (AstVarR d) -> tfromD d
       Just AstVarI{} ->
         error $ "interpretAstRec: type mismatch for Var" ++ show var
       Nothing -> error $ "interpretAstRec: unknown variable Var" ++ show var
     AstOp opCode args ->
       interpretAstOp (interpretAstRec env) opCode args
     AstConst a -> tconst a
     AstConstant a -> tconst $ interpretAstPrimal env a
     AstConstInt i -> tfromIndex0 $ interpretAstInt env i
     AstIndexZ v is -> tindex (interpretAstRec env v) (fmap (interpretAstInt env) is)
       -- if index is out of bounds, the operations returns with an undefined
       -- value of the correct rank and shape; this is needed, because
       -- vectorization can produce out of bound indexing from code where
       -- the indexing is guarded by conditionals
     AstSum v -> tsum (interpretAstRec env v)
       -- TODO: recognize when sum0 may be used instead, which is much cheaper
       -- or should I do that in Delta instead? no, because tsum0R is cheaper, too
       -- TODO: recognize dot0 patterns and speed up their evaluation
     AstScatter sh v (vars, ix) ->
       tscatter sh (interpretAstRec env v)
                   (interpretLambdaIndexToIndex interpretAstInt env (vars, ix))
     AstFromList l -> tfromList (map (interpretAstRec env) l)
     AstFromVector l -> tfromVector (V.map (interpretAstRec env) l)
     AstKonst k v -> tkonst k (interpretAstRec env v)
     AstAppend x y -> tappend (interpretAstRec env x) (interpretAstRec env y)
     AstSlice i k v -> tslice i k (interpretAstRec env v)
     AstReverse v -> treverse (interpretAstRec env v)
     AstTranspose perm v -> ttranspose perm $ interpretAstRec env v
     AstReshape sh v -> treshape sh (interpretAstRec env v)
     AstBuild1 k (var, AstConstant r) ->
       tconst
       $ OR.ravel . ORB.fromVector [k] . V.generate k
       $ toArray . interpretLambdaI interpretAstPrimal env (var, r)
     AstBuild1 k (var, v) -> tbuild1 k (interpretLambdaI interpretAstRec env (var, v))
       -- to be used only in tests
     AstGatherZ sh v (vars, ix) ->
       tgather sh (interpretAstRec env v)
                  (interpretLambdaIndexToIndex interpretAstInt env (vars, ix))
       -- the operation accept out of bounds indexes,
       -- for the same reason ordinary indexing does, see above
       -- TODO: currently we store the function on tape, because it doesn't
       -- cause recomputation of the gradient per-cell, unlike storing the build
       -- function on tape; for GPUs and libraries that don't understand Haskell
       -- closures, we cneck if the expressions involve tensor operations
       -- too hard for GPUs and, if not, we can store the AST expression
       -- on tape and translate it to whatever backend sooner or later;
       -- and if yes, fall back to POPL pre-computation that, unfortunately,
       -- leads to a tensor of deltas
     AstFromDynamic t -> tfromD $ interpretAstDynamic env t

   interpretAstInt :: AstEnv a
                   -> AstInt (ScalarOf a) -> IntOf (Primal a)
   interpretAstInt env = \case
     AstIntVar (AstVarName var) -> case IM.lookup var env of
       Just AstVarR{} ->
         error $ "interpretAstInt: type mismatch for Var" ++ show var
       Just (AstVarI i) -> i
       Nothing -> error $ "interpretAstInt: unknown variable Var" ++ show var
     AstIntOp opCodeInt args ->
       interpretAstIntOp (interpretAstInt env) opCodeInt args
     AstIntConst a -> a
     AstIntFloor v -> let u = interpretAstPrimal env (AstPrimalPart v)
                      in tfloor u
     AstIntCond b a1 a2 -> ifB (interpretAstBool env b)
                               (interpretAstInt env a1)
                               (interpretAstInt env a2)
     AstMinIndex1 v -> tminIndex0 $ interpretAstRec env v
     AstMaxIndex1 v -> tmaxIndex0 $ interpretAstRec env v

   interpretAstBool :: AstEnv a
                    -> AstBool (ScalarOf a) -> BooleanOf (Primal a)
   interpretAstBool env = \case
     AstBoolOp opCodeBool args ->
       interpretAstBoolOp (interpretAstBool env) opCodeBool args
     AstBoolConst a -> if a then true else false
     AstRel opCodeRel args ->
       let f v = interpretAstPrimal env (AstPrimalPart v)
       in interpretAstRelOp f opCodeRel args
     AstRelInt opCodeRel args ->
       let f = interpretAstInt env
       in interpretAstRelOp f opCodeRel args
 interpretAstDynamic
   :: forall a. a ~ ADVal Double
   => AstEnv a -> AstDynamic (ScalarOf a) -> DynamicTensor a
 interpretAstDynamic = interpretAstDynamicRec
  where
   interpretAstDynamicRec
     :: AstEnv a
     -> AstDynamic (ScalarOf a) -> DynamicTensor a
   interpretAstDynamicRec env = \case
     AstDynamicDummy -> error "interpretAstDynamic: AstDynamicDummy"
     AstDynamicPlus v u ->
       interpretAstDynamicRec env v `taddD` interpretAstDynamicRec env u
     AstDynamicFrom w -> tfromR $ interpretAst env w

instance InterpretAst (ADVal Float) where
 interpretAst
   :: forall n0 a. (KnownNat n0, a ~ ADVal Float)
   => AstEnv a -> Ast n0 (ScalarOf a) -> TensorOf n0 a
 interpretAst = interpretAstRec
  where
-- We could duplicate interpretAst to save some time (sadly, we can't
-- interpret Ast uniformly in any Tensor and HasPrimal instance due to typing,
-- so we can't just use an instance of interpretation to OR.Array for that),
-- but it's not a huge saving, because all dual parts are gone before
-- we do any differentiation and they are mostly symbolic, so don't even
-- double the amount of tensor computation performed. The biggest problem is
-- allocation of tensors, but they are mostly shared with the primal part.
   interpretAstPrimal
     :: forall n. KnownNat n
     => AstEnv a
     -> AstPrimalPart n (ScalarOf a) -> TensorOf n (Primal a)
   interpretAstPrimal env (AstPrimalPart v) =
     toArray $ tprimalPart $ interpretAstRec env v

   interpretAstRec
     :: forall n. KnownNat n
     => AstEnv a
     -> Ast n (ScalarOf a) -> TensorOf n a
   interpretAstRec env = \case
     AstVar _sh (AstVarName var) -> case IM.lookup var env of
       Just (AstVarR d) -> tfromD d
       Just AstVarI{} ->
         error $ "interpretAstRec: type mismatch for Var" ++ show var
       Nothing -> error $ "interpretAstRec: unknown variable Var" ++ show var
     AstOp opCode args ->
       interpretAstOp (interpretAstRec env) opCode args
     AstConst a -> tconst a
     AstConstant a -> tconst $ interpretAstPrimal env a
     AstConstInt i -> tfromIndex0 $ interpretAstInt env i
     AstIndexZ v is -> tindex (interpretAstRec env v) (fmap (interpretAstInt env) is)
       -- if index is out of bounds, the operations returns with an undefined
       -- value of the correct rank and shape; this is needed, because
       -- vectorization can produce out of bound indexing from code where
       -- the indexing is guarded by conditionals
     AstSum v -> tsum (interpretAstRec env v)
       -- TODO: recognize when sum0 may be used instead, which is much cheaper
       -- or should I do that in Delta instead? no, because tsum0R is cheaper, too
       -- TODO: recognize dot0 patterns and speed up their evaluation
     AstScatter sh v (vars, ix) ->
       tscatter sh (interpretAstRec env v)
                   (interpretLambdaIndexToIndex interpretAstInt env (vars, ix))
     AstFromList l -> tfromList (map (interpretAstRec env) l)
     AstFromVector l -> tfromVector (V.map (interpretAstRec env) l)
     AstKonst k v -> tkonst k (interpretAstRec env v)
     AstAppend x y -> tappend (interpretAstRec env x) (interpretAstRec env y)
     AstSlice i k v -> tslice i k (interpretAstRec env v)
     AstReverse v -> treverse (interpretAstRec env v)
     AstTranspose perm v -> ttranspose perm $ interpretAstRec env v
     AstReshape sh v -> treshape sh (interpretAstRec env v)
     AstBuild1 k (var, AstConstant r) ->
       tconst
       $ OR.ravel . ORB.fromVector [k] . V.generate k
       $ toArray . interpretLambdaI interpretAstPrimal env (var, r)
     AstBuild1 k (var, v) -> tbuild1 k (interpretLambdaI interpretAstRec env (var, v))
       -- to be used only in tests
     AstGatherZ sh v (vars, ix) ->
       tgather sh (interpretAstRec env v)
                  (interpretLambdaIndexToIndex interpretAstInt env (vars, ix))
       -- the operation accept out of bounds indexes,
       -- for the same reason ordinary indexing does, see above
       -- TODO: currently we store the function on tape, because it doesn't
       -- cause recomputation of the gradient per-cell, unlike storing the build
       -- function on tape; for GPUs and libraries that don't understand Haskell
       -- closures, we cneck if the expressions involve tensor operations
       -- too hard for GPUs and, if not, we can store the AST expression
       -- on tape and translate it to whatever backend sooner or later;
       -- and if yes, fall back to POPL pre-computation that, unfortunately,
       -- leads to a tensor of deltas
     AstFromDynamic t -> tfromD $ interpretAstDynamic env t

   interpretAstInt :: AstEnv a
                   -> AstInt (ScalarOf a) -> IntOf (Primal a)
   interpretAstInt env = \case
     AstIntVar (AstVarName var) -> case IM.lookup var env of
       Just AstVarR{} ->
         error $ "interpretAstInt: type mismatch for Var" ++ show var
       Just (AstVarI i) -> i
       Nothing -> error $ "interpretAstInt: unknown variable Var" ++ show var
     AstIntOp opCodeInt args ->
       interpretAstIntOp (interpretAstInt env) opCodeInt args
     AstIntConst a -> a
     AstIntFloor v -> let u = interpretAstPrimal env (AstPrimalPart v)
                      in tfloor u
     AstIntCond b a1 a2 -> ifB (interpretAstBool env b)
                               (interpretAstInt env a1)
                               (interpretAstInt env a2)
     AstMinIndex1 v -> tminIndex0 $ interpretAstRec env v
     AstMaxIndex1 v -> tmaxIndex0 $ interpretAstRec env v

   interpretAstBool :: AstEnv a
                    -> AstBool (ScalarOf a) -> BooleanOf (Primal a)
   interpretAstBool env = \case
     AstBoolOp opCodeBool args ->
       interpretAstBoolOp (interpretAstBool env) opCodeBool args
     AstBoolConst a -> if a then true else false
     AstRel opCodeRel args ->
       let f v = interpretAstPrimal env (AstPrimalPart v)
       in interpretAstRelOp f opCodeRel args
     AstRelInt opCodeRel args ->
       let f = interpretAstInt env
       in interpretAstRelOp f opCodeRel args
 interpretAstDynamic
   :: forall a. a ~ ADVal Float
   => AstEnv a -> AstDynamic (ScalarOf a) -> DynamicTensor a
 interpretAstDynamic = interpretAstDynamicRec
  where
   interpretAstDynamicRec
     :: AstEnv a
     -> AstDynamic (ScalarOf a) -> DynamicTensor a
   interpretAstDynamicRec env = \case
     AstDynamicDummy -> error "interpretAstDynamic: AstDynamicDummy"
     AstDynamicPlus v u ->
       interpretAstDynamicRec env v `taddD` interpretAstDynamicRec env u
     AstDynamicFrom w -> tfromR $ interpretAst env w

instance ( ADTensor (Ast0 q)
         , Numeric q, Show q, Floating (Vector q), RealFloat q )
         => InterpretAst (ADVal (Ast0 q)) where
 interpretAst
   :: forall n0 a. (KnownNat n0, a ~ ADVal (Ast0 q))
   => AstEnv a -> Ast n0 (ScalarOf a) -> TensorOf n0 a
 interpretAst = interpretAstRec
  where
-- We could duplicate interpretAst to save some time (sadly, we can't
-- interpret Ast uniformly in any Tensor and HasPrimal instance due to typing,
-- so we can't just use an instance of interpretation to OR.Array for that),
-- but it's not a huge saving, because all dual parts are gone before
-- we do any differentiation and they are mostly symbolic, so don't even
-- double the amount of tensor computation performed. The biggest problem is
-- allocation of tensors, but they are mostly shared with the primal part.
   interpretAstPrimal
     :: forall n. KnownNat n
     => AstEnv a
     -> AstPrimalPart n (ScalarOf a) -> TensorOf n (Primal a)
   interpretAstPrimal env (AstPrimalPart v) =
     tprimalPart $ interpretAstRec env v

   interpretAstRec
     :: forall n. KnownNat n
     => AstEnv a
     -> Ast n (ScalarOf a) -> TensorOf n a
   interpretAstRec env = \case
     AstVar _sh (AstVarName var) -> case IM.lookup var env of
       Just (AstVarR d) -> tfromD d
       Just AstVarI{} ->
         error $ "interpretAstRec: type mismatch for Var" ++ show var
       Nothing -> error $ "interpretAstRec: unknown variable Var" ++ show var
     AstOp opCode args ->
       interpretAstOp (interpretAstRec env) opCode args
     AstConst a -> tconst a
     AstConstant a -> tconstant $ interpretAstPrimal env a
     AstConstInt i -> tfromIndex0 $ interpretAstInt env i
     AstIndexZ v is -> tindex (interpretAstRec env v) (fmap (interpretAstInt env) is)
       -- if index is out of bounds, the operations returns with an undefined
       -- value of the correct rank and shape; this is needed, because
       -- vectorization can produce out of bound indexing from code where
       -- the indexing is guarded by conditionals
     AstSum v -> tsum (interpretAstRec env v)
       -- TODO: recognize when sum0 may be used instead, which is much cheaper
       -- or should I do that in Delta instead? no, because tsum0R is cheaper, too
       -- TODO: recognize dot0 patterns and speed up their evaluation
     AstScatter sh v (vars, ix) ->
       tscatter sh (interpretAstRec env v)
                   (interpretLambdaIndexToIndex interpretAstInt env (vars, ix))
     AstFromList l -> tfromList (map (interpretAstRec env) l)
     AstFromVector l -> tfromVector (V.map (interpretAstRec env) l)
     AstKonst k v -> tkonst k (interpretAstRec env v)
     AstAppend x y -> tappend (interpretAstRec env x) (interpretAstRec env y)
     AstSlice i k v -> tslice i k (interpretAstRec env v)
     AstReverse v -> treverse (interpretAstRec env v)
     AstTranspose perm v -> ttranspose perm $ interpretAstRec env v
     AstReshape sh v -> treshape sh (interpretAstRec env v)
     -- We can't partially evaluate this, because env maps variables to terms
     -- and so we don't know what floats to put into the resulting tensor.
     -- AstBuild1 k (var, AstConstant r) ->
     AstBuild1 k (var, v) ->
       tbuild1 k (interpretLambdaI interpretAstRec env (var, v))
       -- to be used only in tests
     AstGatherZ sh v (vars, ix) ->
       tgather sh (interpretAstRec env v)
                  (interpretLambdaIndexToIndex interpretAstInt env (vars, ix))
       -- the operation accept out of bounds indexes,
       -- for the same reason ordinary indexing does, see above
       -- TODO: currently we store the function on tape, because it doesn't
       -- cause recomputation of the gradient per-cell, unlike storing the build
       -- function on tape; for GPUs and libraries that don't understand Haskell
       -- closures, we cneck if the expressions involve tensor operations
       -- too hard for GPUs and, if not, we can store the AST expression
       -- on tape and translate it to whatever backend sooner or later;
       -- and if yes, fall back to POPL pre-computation that, unfortunately,
       -- leads to a tensor of deltas
     AstFromDynamic t -> tfromD $ interpretAstDynamic env t

   interpretAstInt :: AstEnv a
                   -> AstInt (ScalarOf a) -> IntOf (Primal a)
   interpretAstInt env = \case
     AstIntVar (AstVarName var) -> case IM.lookup var env of
       Just AstVarR{} ->
         error $ "interpretAstInt: type mismatch for Var" ++ show var
       Just (AstVarI i) -> i
       Nothing -> error $ "interpretAstInt: unknown variable Var" ++ show var
     AstIntOp opCodeInt args ->
       interpretAstIntOp (interpretAstInt env) opCodeInt args
     AstIntConst a -> fromIntegral a
     AstIntFloor v -> let u = interpretAstPrimal env (AstPrimalPart v)
                      in tfloor u
     AstIntCond b a1 a2 -> ifB (interpretAstBool env b)
                               (interpretAstInt env a1)
                               (interpretAstInt env a2)
     AstMinIndex1 v -> tminIndex0 $ interpretAstRec env v
     AstMaxIndex1 v -> tmaxIndex0 $ interpretAstRec env v

   interpretAstBool :: AstEnv a
                    -> AstBool (ScalarOf a) -> BooleanOf (Primal a)
   interpretAstBool env = \case
     AstBoolOp opCodeBool args ->
       interpretAstBoolOp (interpretAstBool env) opCodeBool args
     AstBoolConst a -> if a then true else false
     AstRel opCodeRel args ->
       let f v = interpretAstPrimal env (AstPrimalPart v)
       in interpretAstRelOp f opCodeRel args
     AstRelInt opCodeRel args ->
       let f = interpretAstInt env
       in interpretAstRelOp f opCodeRel args
 interpretAstDynamic
   :: forall a. a ~ ADVal (Ast0 q)
   => AstEnv a -> AstDynamic (ScalarOf a) -> DynamicTensor a
 interpretAstDynamic = interpretAstDynamicRec
  where
   interpretAstDynamicRec
     :: AstEnv a
     -> AstDynamic (ScalarOf a) -> DynamicTensor a
   interpretAstDynamicRec env = \case
     AstDynamicDummy -> error "interpretAstDynamic: AstDynamicDummy"
     AstDynamicPlus v u ->
       interpretAstDynamicRec env v `taddD` interpretAstDynamicRec env u
     AstDynamicFrom w -> tfromR $ interpretAst env w

instance InterpretAst Double where
 interpretAst
   :: forall n0 a. (KnownNat n0, a ~ Double)
   => AstEnv a -> Ast n0 (ScalarOf a) -> TensorOf n0 a
 interpretAst = interpretAstRec
  where
-- We could duplicate interpretAst to save some time (sadly, we can't
-- interpret Ast uniformly in any Tensor and HasPrimal instance due to typing,
-- so we can't just use an instance of interpretation to OR.Array for that),
-- but it's not a huge saving, because all dual parts are gone before
-- we do any differentiation and they are mostly symbolic, so don't even
-- double the amount of tensor computation performed. The biggest problem is
-- allocation of tensors, but they are mostly shared with the primal part.
   interpretAstPrimal
     :: forall n. KnownNat n
     => AstEnv a
     -> AstPrimalPart n (ScalarOf a) -> TensorOf n (Primal a)
   interpretAstPrimal env (AstPrimalPart v) =
     toArray $ tprimalPart $ interpretAstRec env v

   interpretAstRec
     :: forall n. KnownNat n
     => AstEnv a
     -> Ast n (ScalarOf a) -> TensorOf n a
   interpretAstRec env = \case
     AstVar _sh (AstVarName var) -> case IM.lookup var env of
       Just (AstVarR d) -> tfromD d
       Just AstVarI{} ->
         error $ "interpretAstRec: type mismatch for Var" ++ show var
       Nothing -> error $ "interpretAstRec: unknown variable Var" ++ show var
     AstOp opCode args ->
       interpretAstOp (interpretAstRec env) opCode args
     AstConst a -> tconst a
     AstConstant a -> tconst $ interpretAstPrimal env a
     AstConstInt i -> tfromIndex0 $ interpretAstInt env i
     AstIndexZ v is -> tindex (interpretAstRec env v) (fmap (interpretAstInt env) is)
       -- if index is out of bounds, the operations returns with an undefined
       -- value of the correct rank and shape; this is needed, because
       -- vectorization can produce out of bound indexing from code where
       -- the indexing is guarded by conditionals
     AstSum v -> tsum (interpretAstRec env v)
       -- TODO: recognize when sum0 may be used instead, which is much cheaper
       -- or should I do that in Delta instead? no, because tsum0R is cheaper, too
       -- TODO: recognize dot0 patterns and speed up their evaluation
     AstScatter sh v (vars, ix) ->
       tscatter sh (interpretAstRec env v)
                   (interpretLambdaIndexToIndex interpretAstInt env (vars, ix))
     AstFromList l -> tfromList (map (interpretAstRec env) l)
     AstFromVector l -> tfromVector (V.map (interpretAstRec env) l)
     AstKonst k v -> tkonst k (interpretAstRec env v)
     AstAppend x y -> tappend (interpretAstRec env x) (interpretAstRec env y)
     AstSlice i k v -> tslice i k (interpretAstRec env v)
     AstReverse v -> treverse (interpretAstRec env v)
     AstTranspose perm v -> ttranspose perm $ interpretAstRec env v
     AstReshape sh v -> treshape sh (interpretAstRec env v)
     AstBuild1 k (var, AstConstant r) ->
       tconst
       $ OR.ravel . ORB.fromVector [k] . V.generate k
       $ toArray . interpretLambdaI interpretAstPrimal env (var, r)
     AstBuild1 k (var, v) -> tbuild1 k (interpretLambdaI interpretAstRec env (var, v))
       -- to be used only in tests
     AstGatherZ sh v (vars, ix) ->
       tgather sh (interpretAstRec env v)
                  (interpretLambdaIndexToIndex interpretAstInt env (vars, ix))
       -- the operation accept out of bounds indexes,
       -- for the same reason ordinary indexing does, see above
       -- TODO: currently we store the function on tape, because it doesn't
       -- cause recomputation of the gradient per-cell, unlike storing the build
       -- function on tape; for GPUs and libraries that don't understand Haskell
       -- closures, we cneck if the expressions involve tensor operations
       -- too hard for GPUs and, if not, we can store the AST expression
       -- on tape and translate it to whatever backend sooner or later;
       -- and if yes, fall back to POPL pre-computation that, unfortunately,
       -- leads to a tensor of deltas
     AstFromDynamic t -> tfromD $ interpretAstDynamic env t

   interpretAstInt :: AstEnv a
                   -> AstInt (ScalarOf a) -> IntOf (Primal a)
   interpretAstInt env = \case
     AstIntVar (AstVarName var) -> case IM.lookup var env of
       Just AstVarR{} ->
         error $ "interpretAstInt: type mismatch for Var" ++ show var
       Just (AstVarI i) -> i
       Nothing -> error $ "interpretAstInt: unknown variable Var" ++ show var
     AstIntOp opCodeInt args ->
       interpretAstIntOp (interpretAstInt env) opCodeInt args
     AstIntConst a -> a
     AstIntFloor v -> let u = interpretAstPrimal env (AstPrimalPart v)
                      in tfloor u
     AstIntCond b a1 a2 -> ifB (interpretAstBool env b)
                               (interpretAstInt env a1)
                               (interpretAstInt env a2)
     AstMinIndex1 v -> tminIndex0 $ interpretAstRec env v
     AstMaxIndex1 v -> tmaxIndex0 $ interpretAstRec env v

   interpretAstBool :: AstEnv a
                    -> AstBool (ScalarOf a) -> BooleanOf (Primal a)
   interpretAstBool env = \case
     AstBoolOp opCodeBool args ->
       interpretAstBoolOp (interpretAstBool env) opCodeBool args
     AstBoolConst a -> if a then true else false
     AstRel opCodeRel args ->
       let f v = interpretAstPrimal env (AstPrimalPart v)
       in interpretAstRelOp f opCodeRel args
     AstRelInt opCodeRel args ->
       let f = interpretAstInt env
       in interpretAstRelOp f opCodeRel args
 interpretAstDynamic
   :: forall a. a ~ Double
   => AstEnv a -> AstDynamic (ScalarOf a) -> DynamicTensor a
 interpretAstDynamic = interpretAstDynamicRec
  where
   interpretAstDynamicRec
     :: AstEnv a
     -> AstDynamic (ScalarOf a) -> DynamicTensor a
   interpretAstDynamicRec env = \case
     AstDynamicDummy -> error "interpretAstDynamic: AstDynamicDummy"
     AstDynamicPlus v u ->
       interpretAstDynamicRec env v `taddD` interpretAstDynamicRec env u
     AstDynamicFrom w -> tfromR $ interpretAst env w

instance InterpretAst Float where
 interpretAst
   :: forall n0 a. (KnownNat n0, a ~ Float)
   => AstEnv a -> Ast n0 (ScalarOf a) -> TensorOf n0 a
 interpretAst = interpretAstRec
  where
-- We could duplicate interpretAst to save some time (sadly, we can't
-- interpret Ast uniformly in any Tensor and HasPrimal instance due to typing,
-- so we can't just use an instance of interpretation to OR.Array for that),
-- but it's not a huge saving, because all dual parts are gone before
-- we do any differentiation and they are mostly symbolic, so don't even
-- double the amount of tensor computation performed. The biggest problem is
-- allocation of tensors, but they are mostly shared with the primal part.
   interpretAstPrimal
     :: forall n. KnownNat n
     => AstEnv a
     -> AstPrimalPart n (ScalarOf a) -> TensorOf n (Primal a)
   interpretAstPrimal env (AstPrimalPart v) =
     toArray $ tprimalPart $ interpretAstRec env v

   interpretAstRec
     :: forall n. KnownNat n
     => AstEnv a
     -> Ast n (ScalarOf a) -> TensorOf n a
   interpretAstRec env = \case
     AstVar _sh (AstVarName var) -> case IM.lookup var env of
       Just (AstVarR d) -> tfromD d
       Just AstVarI{} ->
         error $ "interpretAstRec: type mismatch for Var" ++ show var
       Nothing -> error $ "interpretAstRec: unknown variable Var" ++ show var
     AstOp opCode args ->
       interpretAstOp (interpretAstRec env) opCode args
     AstConst a -> tconst a
     AstConstant a -> tconst $ interpretAstPrimal env a
     AstConstInt i -> tfromIndex0 $ interpretAstInt env i
     AstIndexZ v is -> tindex (interpretAstRec env v) (fmap (interpretAstInt env) is)
       -- if index is out of bounds, the operations returns with an undefined
       -- value of the correct rank and shape; this is needed, because
       -- vectorization can produce out of bound indexing from code where
       -- the indexing is guarded by conditionals
     AstSum v -> tsum (interpretAstRec env v)
       -- TODO: recognize when sum0 may be used instead, which is much cheaper
       -- or should I do that in Delta instead? no, because tsum0R is cheaper, too
       -- TODO: recognize dot0 patterns and speed up their evaluation
     AstScatter sh v (vars, ix) ->
       tscatter sh (interpretAstRec env v)
                   (interpretLambdaIndexToIndex interpretAstInt env (vars, ix))
     AstFromList l -> tfromList (map (interpretAstRec env) l)
     AstFromVector l -> tfromVector (V.map (interpretAstRec env) l)
     AstKonst k v -> tkonst k (interpretAstRec env v)
     AstAppend x y -> tappend (interpretAstRec env x) (interpretAstRec env y)
     AstSlice i k v -> tslice i k (interpretAstRec env v)
     AstReverse v -> treverse (interpretAstRec env v)
     AstTranspose perm v -> ttranspose perm $ interpretAstRec env v
     AstReshape sh v -> treshape sh (interpretAstRec env v)
     AstBuild1 k (var, AstConstant r) ->
       tconst
       $ OR.ravel . ORB.fromVector [k] . V.generate k
       $ toArray . interpretLambdaI interpretAstPrimal env (var, r)
     AstBuild1 k (var, v) -> tbuild1 k (interpretLambdaI interpretAstRec env (var, v))
       -- to be used only in tests
     AstGatherZ sh v (vars, ix) ->
       tgather sh (interpretAstRec env v)
                  (interpretLambdaIndexToIndex interpretAstInt env (vars, ix))
       -- the operation accept out of bounds indexes,
       -- for the same reason ordinary indexing does, see above
       -- TODO: currently we store the function on tape, because it doesn't
       -- cause recomputation of the gradient per-cell, unlike storing the build
       -- function on tape; for GPUs and libraries that don't understand Haskell
       -- closures, we cneck if the expressions involve tensor operations
       -- too hard for GPUs and, if not, we can store the AST expression
       -- on tape and translate it to whatever backend sooner or later;
       -- and if yes, fall back to POPL pre-computation that, unfortunately,
       -- leads to a tensor of deltas
     AstFromDynamic t -> tfromD $ interpretAstDynamic env t

   interpretAstInt :: AstEnv a
                   -> AstInt (ScalarOf a) -> IntOf (Primal a)
   interpretAstInt env = \case
     AstIntVar (AstVarName var) -> case IM.lookup var env of
       Just AstVarR{} ->
         error $ "interpretAstInt: type mismatch for Var" ++ show var
       Just (AstVarI i) -> i
       Nothing -> error $ "interpretAstInt: unknown variable Var" ++ show var
     AstIntOp opCodeInt args ->
       interpretAstIntOp (interpretAstInt env) opCodeInt args
     AstIntConst a -> a
     AstIntFloor v -> let u = interpretAstPrimal env (AstPrimalPart v)
                      in tfloor u
     AstIntCond b a1 a2 -> ifB (interpretAstBool env b)
                               (interpretAstInt env a1)
                               (interpretAstInt env a2)
     AstMinIndex1 v -> tminIndex0 $ interpretAstRec env v
     AstMaxIndex1 v -> tmaxIndex0 $ interpretAstRec env v

   interpretAstBool :: AstEnv a
                    -> AstBool (ScalarOf a) -> BooleanOf (Primal a)
   interpretAstBool env = \case
     AstBoolOp opCodeBool args ->
       interpretAstBoolOp (interpretAstBool env) opCodeBool args
     AstBoolConst a -> if a then true else false
     AstRel opCodeRel args ->
       let f v = interpretAstPrimal env (AstPrimalPart v)
       in interpretAstRelOp f opCodeRel args
     AstRelInt opCodeRel args ->
       let f = interpretAstInt env
       in interpretAstRelOp f opCodeRel args
 interpretAstDynamic
   :: forall a. a ~ Float
   => AstEnv a -> AstDynamic (ScalarOf a) -> DynamicTensor a
 interpretAstDynamic = interpretAstDynamicRec
  where
   interpretAstDynamicRec
     :: AstEnv a
     -> AstDynamic (ScalarOf a) -> DynamicTensor a
   interpretAstDynamicRec env = \case
     AstDynamicDummy -> error "interpretAstDynamic: AstDynamicDummy"
     AstDynamicPlus v u ->
       interpretAstDynamicRec env v `taddD` interpretAstDynamicRec env u
     AstDynamicFrom w -> tfromR $ interpretAst env w

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

interpretAstIntOp :: Integral b
                  => (c -> b) -> OpCodeInt -> [c] -> b
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
interpretAstIntOp _ opCodeInt args =
  error $ "interpretAstIntOp: wrong number of arguments"
          ++ show (opCodeInt, length args)

interpretAstBoolOp :: Boolean b
                   => (c -> b) -> OpCodeBool -> [c] -> b
{-# INLINE interpretAstBoolOp #-}
interpretAstBoolOp f NotOp [u] = notB $ f u
interpretAstBoolOp f AndOp [u, v] = f u &&* f v
interpretAstBoolOp f OrOp [u, v] = f u ||* f v
interpretAstBoolOp _ opCodeBool args =
  error $ "interpretAstBoolOp: wrong number of arguments"
          ++ show (opCodeBool, length args)

interpretAstRelOp :: (EqB b, OrdB b)
                  => (a -> b) -> OpCodeRel -> [a] -> BooleanOf b
{-# INLINE interpretAstRelOp #-}
interpretAstRelOp f EqOp [u, v] = f u ==* f v
interpretAstRelOp f NeqOp [u, v] = f u /=* f v
interpretAstRelOp f LeqOp [u, v] = f u <=* f v
interpretAstRelOp f GeqOp [u, v] = f u >=* f v
interpretAstRelOp f LsOp [u, v] = f u <* f v
interpretAstRelOp f GtOp [u, v] = f u >* f v
interpretAstRelOp _ opCodeRel args =
  error $ "interpretAstRelOp: wrong number of arguments"
          ++ show (opCodeRel, length args)
