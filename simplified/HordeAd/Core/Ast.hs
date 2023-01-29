{-# LANGUAGE CPP, ConstraintKinds, DataKinds, FlexibleInstances, GADTs,
             GeneralizedNewtypeDeriving, MultiParamTypeClasses, PolyKinds,
             QuantifiedConstraints, StandaloneDeriving, TypeFamilyDependencies,
             UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
-- | AST of the code to be differentiated. It's needed mostly for handling
-- higher order operations such as build and map, but can be used
-- for arbitrary code transformations at the cost of limiting
-- expressiveness of transformed fragments to what AST captures.
module HordeAd.Core.Ast
  ( AstShape, AstPath, AstPermutation
  , Ast(..), AstPrimalPart1(..)
  , AstVarName(..), AstVar(..)
  , AstInt(..), AstBool(..)
  , OpCode(..), OpCodeInt(..), OpCodeBool(..), OpCodeRel(..)
  , shapeAst, lenghtAst, substituteAst, substituteAstInt, substituteAstBool
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import qualified Data.Array.RankedS as OR
import           Data.IORef.Unboxed (Counter, atomicAddCounter_, newCounter)
import           Data.Kind (Type)
import           Data.MonoTraversable (Element, MonoFunctor (omap))
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Storable as VS
import           GHC.TypeLits (KnownNat, Nat, type (+))
import           Numeric.LinearAlgebra (Numeric)
import           System.IO.Unsafe (unsafePerformIO)
import           Text.Show.Functions ()

import HordeAd.Internal.OrthotopeOrphanInstances ()

-- * Definitions

-- @[AstInt r]@ gives more expressiveness, but leads to irregular tensors,
-- especially after vectorization, and prevents statically known shapes.
-- However, if we switched to @Data.Array.Shaped@ and moved most of the shapes
-- to the type level, we'd recover some of the expressiveness, while retaining
-- statically known (type-parameterized) shapes.
type AstShape r = [Int]

type AstPath r = [AstInt r]

type AstPermutation = [Int]

-- TODO: consider sharing Ast expressions, both within the primal part
-- and between primal and dual


-- | AST for a tensor of rank n and elements r that is meant
-- to be differentiated.
data Ast :: Nat -> Type -> Type where
  -- For the numeric classes:
  AstOp :: OpCode -> [Ast n r] -> Ast n r

  -- For HasPrimal class and the future Conditional/Boolean/Eq'/Ord' classes:
  AstCond :: AstBool r -> Ast n r -> Ast n r -> Ast n r
  AstSelect :: Int -> (AstVarName Int, AstBool r) -> Ast n r -> Ast n r
            -> Ast n r
    -- emerges from vectorizing AstCond
  AstConstInt :: AstInt r -> Ast n r
  AstConst :: OR.Array n r -> Ast n r
    -- sort of partially evaluated @AstConstant@
  AstConstant :: AstPrimalPart1 n r -> Ast n r
  AstScale :: AstPrimalPart1 n r -> Ast n r -> Ast n r

  -- For VectorLike and Tensor class:
  AstIndex :: Ast (1 + n) r -> AstInt r -> Ast n r
  AstIndexN :: KnownNat m
            => Ast (1 + m + n) r -> AstPath r -> Ast n r
    -- emerges from vectorizing AstIndex;
    -- first ix is for outermost dimension; @1 + m@ is the length of the list;
    -- empty list means identity
  AstSum :: Ast (1 + n) r -> Ast n r
  AstFromList :: [Ast n r] -> Ast (1 + n) r
  AstFromVector :: Data.Vector.Vector (Ast n r) -> Ast (1 + n) r
  AstKonst :: Int -> Ast n r -> Ast (1 + n) r
  AstAppend :: KnownNat n
            => Ast (1 + n) r -> Ast (1 + n) r -> Ast (1 + n) r
  AstSlice :: Int -> Int -> Ast (1 + n) r -> Ast (1 + n) r
  AstReverse :: KnownNat n
             => Ast n r -> Ast n r
  AstTranspose :: Ast n r -> Ast n r
  AstTransposeGeneral :: AstPermutation -> Ast n r -> Ast n r
    -- emerges from vectorizing AstTranspose
  AstFlatten :: KnownNat n
             => Ast n r -> Ast 1 r
  AstReshape :: KnownNat n
             => AstShape r -> Ast n r -> Ast m r
    -- emerges from vectorizing AstFlatten
  AstBuildPair :: Int -> (AstVarName Int, Ast n r) -> Ast (1 + n) r
  AstGatherPair :: KnownNat m
                => Int -> (AstVarName Int, AstPath r) -> Ast (m + n) r
                -> Ast (1 + n) r
    -- emerges from vectorizing AstIndexN applied to term with no build variable

  -- If we give the user access to tensors, not just vectors, these
  -- operations will be necessary.
  -- This is treated as syntactic sugar for now, but these have
  -- much more efficient non-sugar implementations
  -- (and possibly more efficient vectorizations).
  AstSum0 :: KnownNat n
          => Ast n r -> Ast 0 r
  AstDot0 :: KnownNat n
          => Ast n r -> Ast n r -> Ast 0 r
  AstFromList0N :: AstShape r -> [Ast 0 r] -> Ast n r
  AstFromVector0N :: AstShape r -> Data.Vector.Vector (Ast 0 r) -> Ast n r
  AstKonst0N :: AstShape r -> Ast 0 r -> Ast (1 + n) r
  AstBuildPair0N :: AstShape r -> ([AstVarName Int], Ast 0 r) -> Ast n r

  -- For MonoFunctor class, which is needed for a particularly
  -- fast implementation of relu and offer fast, primal-part only, mapping.
  -- TODO: this is really only needed in AstPrimalPart, but making
  -- AstPrimalPart data instead of a newtype would complicate a lot of code.
  AstOMap0 :: (AstVarName r, Ast 0 r) -> Ast 0 r -> Ast 0 r
  AstOMap1 :: (AstVarName r, Ast 0 r) -> Ast 1 r -> Ast 1 r
  -- Variables are only needed for AstOMap. They are also used in test glue
  -- code and may be used for sharing in the future.
  AstVar0 :: AstVarName r -> Ast 0 r
  AstVar1 :: Int -> AstVarName (OR.Array 1 r) -> Ast 1 r
deriving instance (Show r, Numeric r) => Show (Ast n r)

newtype AstPrimalPart1 n r = AstPrimalPart1 (Ast n r)
 deriving Show

newtype AstVarName t = AstVarName Int
 deriving (Show, Eq)

data AstVar a0 a1 =
    AstVarR0 a0
  | AstVarR1 a1
  | AstVarI Int
 deriving Show

-- In AstInt and AstBool, the Ast terms are morally AstPrimalPart,
-- since their derivative part is not used.
-- TODO: introduce AstPrimalPart explicitly when convenient, e.g.,
-- as soon as AstPrimalPart gets more constructors.

-- The argument is the underlying scalar.
data AstInt :: Type -> Type where
  AstIntOp :: OpCodeInt -> [AstInt r] -> AstInt r
  AstIntCond :: AstBool r -> AstInt r -> AstInt r -> AstInt r
  AstIntConst :: Int -> AstInt r
  AstIntVar :: AstVarName Int -> AstInt r

  AstMinIndex :: Ast 1 r -> AstInt r
  AstMaxIndex :: Ast 1 r -> AstInt r
deriving instance (Show r, Numeric r) => Show (AstInt r)

data AstBool :: Type -> Type where
  AstBoolOp :: OpCodeBool -> [AstBool r] -> AstBool r
  AstBoolConst :: Bool -> AstBool r
  AstRel :: OpCodeRel -> [Ast 0 r] -> AstBool r
  AstRelInt :: OpCodeRel -> [AstInt r] -> AstBool r
 deriving Show

-- Copied from the outlining mechanism deleted in
-- https://github.com/Mikolaj/horde-ad/commit/c59947e13082c319764ec35e54b8adf8bc01691f
data OpCode =
    PlusOp | MinusOp | TimesOp | NegateOp | AbsOp | SignumOp
  | DivideOp | RecipOp
  | ExpOp | LogOp | SqrtOp | PowerOp | LogBaseOp
  | SinOp | CosOp | TanOp | AsinOp | AcosOp | AtanOp
  | SinhOp | CoshOp | TanhOp | AsinhOp | AcoshOp | AtanhOp
  | Atan2Op
  | MaxOp | MinOp
 deriving Show

data OpCodeInt =
    PlusIntOp | MinusIntOp | TimesIntOp | NegateIntOp
  | AbsIntOp | SignumIntOp
  | MaxIntOp | MinIntOp
  | QuotIntOp | RemIntOp | DivIntOp | ModIntOp
 deriving Show

data OpCodeBool =
    NotOp | AndOp | OrOp | IffOp
 deriving Show

data OpCodeRel =
    EqOp | NeqOp
  | LeqOp| GeqOp | LsOp | GtOp
 deriving Show


-- * Unlawful instances of AST types; they are lawful modulo evaluation

-- See the comment about @Eq@ and @Ord@ in "DualNumber".
instance Eq (Ast n r) where
  _ == _ = error "Ast: can't evaluate terms for Eq"

instance Ord (OR.Array n r) => Ord (Ast n r) where
  max u v = AstOp MaxOp [u, v]
  min u v = AstOp MinOp [u, v]
  -- Unfortunately, the others can't be made to return @AstBool@.
  _ <= _ = error "Ast: can't evaluate terms for Ord"

instance Num (OR.Array n r) => Num (Ast n r) where
  u + v = AstOp PlusOp [u, v]
  u - v = AstOp MinusOp [u, v]
  u * v = AstOp TimesOp [u, v]
  negate u = AstOp NegateOp [u]
  abs v = AstOp AbsOp [v]
  signum v = AstOp SignumOp [v]
  fromInteger = AstConst . fromInteger

instance Real (OR.Array n r) => Real (Ast n r) where
  toRational = undefined  -- TODO?

instance Fractional (OR.Array n r) => Fractional (Ast n r) where
  u / v = AstOp DivideOp  [u, v]
  recip v = AstOp RecipOp [v]
  fromRational = AstConst . fromRational

instance Floating (OR.Array n r) => Floating (Ast n r) where
  pi = AstConst pi
  exp u = AstOp ExpOp [u]
  log u = AstOp LogOp [u]
  sqrt u = AstOp SqrtOp [u]
  u ** v = AstOp PowerOp [u, v]
  logBase u v = AstOp LogBaseOp [u, v]
  sin u = AstOp SinOp [u]
  cos u = AstOp CosOp [u]
  tan u = AstOp TanOp [u]
  asin u = AstOp AsinOp [u]
  acos u = AstOp AcosOp [u]
  atan u = AstOp AtanOp [u]
  sinh u = AstOp SinhOp [u]
  cosh u = AstOp CoshOp [u]
  tanh u = AstOp TanhOp [u]
  asinh u = AstOp AsinhOp [u]
  acosh u = AstOp AcoshOp [u]
  atanh u = AstOp AtanhOp [u]

instance RealFrac (OR.Array n r) => RealFrac (Ast n r) where
  properFraction = undefined
    -- TODO: others, but low priority, since these are extremely not continuous

instance RealFloat (OR.Array n r) => RealFloat (Ast n r) where
  atan2 u v = AstOp Atan2Op [u, v]
      -- we can be selective here and omit the other methods,
      -- most of which don't even have a differentiable codomain

instance Eq (AstPrimalPart1 n r) where
  _ == _ = error "AstPrimalPart1: can't evaluate terms for Eq"

instance Ord r => Ord (AstPrimalPart1 n r) where
  max (AstPrimalPart1 u) (AstPrimalPart1 v) =
    AstPrimalPart1 (AstOp MaxOp [u, v])
  min (AstPrimalPart1 u) (AstPrimalPart1 v) =
    AstPrimalPart1 (AstOp MinOp [u, v])
  _ <= _ = error "AstPrimalPart1: can't evaluate terms for Ord"

deriving instance Num (Ast n r) => Num (AstPrimalPart1 n r)
deriving instance (Real (Ast n r), Ord r) => Real (AstPrimalPart1 n r)
deriving instance Fractional (Ast n r) => Fractional (AstPrimalPart1 n r)
-- TODO: etc.

type instance Element (AstPrimalPart1 n r) = AstPrimalPart1 0 r


instance Eq (AstInt r) where
  _ == _ = error "AstInt: can't evaluate terms for Eq"

instance Ord (AstInt r) where
  max u v = AstIntOp MaxIntOp [u, v]
  min u v = AstIntOp MinIntOp [u, v]
  _ <= _ = error "AstInt: can't evaluate terms for Ord"

instance Num (AstInt r) where
  u + v = AstIntOp PlusIntOp [u, v]
  u - v = AstIntOp MinusIntOp [u, v]
  u * v = AstIntOp TimesIntOp [u, v]
  negate u = AstIntOp NegateIntOp [u]
  abs v = AstIntOp AbsIntOp [v]
  signum v = AstIntOp SignumIntOp [v]
  fromInteger = AstIntConst . fromInteger

instance Real (AstInt r) where
  toRational = undefined  -- TODO

instance Enum (AstInt r) where
  -- TODO

-- Warning: this class lacks toInteger, which also makes it impossible
-- to include AstInt in Ast via fromInteger nor fromIntegral, hence AstInt.
instance Integral (AstInt r) where
  quot u v = AstIntOp QuotIntOp [u, v]
  rem u v = AstIntOp RemIntOp [u, v]
  div u v = AstIntOp DivIntOp [u, v]
  mod u v = AstIntOp ModIntOp [u, v]
  quotRem u v = (AstIntOp QuotIntOp [u, v], AstIntOp RemIntOp [u, v])
  divMod u v = (AstIntOp DivIntOp [u, v], AstIntOp ModIntOp [u, v])
  toInteger = undefined  -- we can't evaluate uninstantiated variables, etc.

-- Impure but in the most trivial way (only ever incremented counter).
unsafeAstVarCounter :: Counter
{-# NOINLINE unsafeAstVarCounter #-}
unsafeAstVarCounter = unsafePerformIO (newCounter 0)

unsafeGetFreshAstVar :: IO (AstVarName a)
{-# INLINE unsafeGetFreshAstVar #-}
unsafeGetFreshAstVar = AstVarName <$> atomicAddCounter_ unsafeAstVarCounter 1

astOmap0 :: (Ast 0 r -> Ast 0 r) -> Ast 0 r -> Ast 0 r
{-# NOINLINE astOmap0 #-}
astOmap0 f e = unsafePerformIO $ do
  freshAstVar <- unsafeGetFreshAstVar
  return $! AstOMap0 (freshAstVar, f (AstVar0 freshAstVar)) e

astOmap1 :: (Ast 0 r -> Ast 0 r) -> Ast 1 r -> Ast 1 r
{-# NOINLINE astOmap1 #-}
astOmap1 f e = unsafePerformIO $ do
  freshAstVar <- unsafeGetFreshAstVar
  return $! AstOMap1 (freshAstVar, f (AstVar0 freshAstVar)) e

instance MonoFunctor (AstPrimalPart1 1 r) where
  omap f (AstPrimalPart1 x) =
    let g y = let AstPrimalPart1 z = f (AstPrimalPart1 y)
              in z
    in AstPrimalPart1 (astOmap1 g x)

instance MonoFunctor (AstPrimalPart1 0 Double) where
  omap f (AstPrimalPart1 x) =
    let g y = let AstPrimalPart1 z = f (AstPrimalPart1 y)
              in z
    in AstPrimalPart1 (astOmap0 g x)

instance MonoFunctor (AstPrimalPart1 0 Float) where
  omap f (AstPrimalPart1 x) =
    let g y = let AstPrimalPart1 z = f (AstPrimalPart1 y)
              in z
    in AstPrimalPart1 (astOmap0 g x)

-- This is cheap and dirty. We don't shape-check the terms and we don't
-- unify or produce (partial) results with variables. Instead, we investigate
-- only one path and fail if it doesn't contain enough information
-- to determine shape. If we don't switch to @Data.Array.Shaped@
-- or revert to fully dynamic shapes, we need to redo this with more rigour.
shapeAst :: (Show r, Numeric r) => Ast n r -> AstShape r
shapeAst v1 = case v1 of
  AstOp _opCode args -> case args of
    [] -> error "shapeAst: AstOp with no arguments"
    t : _ -> shapeAst t
  AstCond _b a1 _a2 -> shapeAst a1
  AstSelect n (_var, _b) a1 _a2 -> n : shapeAst a1
  AstConstInt _i -> []
  AstConst a -> OR.shapeL a
  AstConstant (AstPrimalPart1 a) -> shapeAst a
  AstScale (AstPrimalPart1 r) _d -> shapeAst r
  AstIndex v _i -> tail $ shapeAst v  -- types ensure this @tail@ is total
  AstIndexN v is ->
    let sh = shapeAst v
    in assert (length sh >= length is `blame` v1)
       $ drop (length is) sh
  AstSum v -> tail $ shapeAst v
  AstFromList l -> case l of
    [] -> error "shapeAst: AstFromList with no arguments"
    t : _ -> length l : shapeAst t
  AstFromVector l -> case V.toList l of
    [] -> error "shapeAst: AstFromVector with no arguments"
    t : _ -> V.length l : shapeAst t
  AstKonst n v -> n : shapeAst v
  AstAppend x y -> case shapeAst x of
    [] -> error "shapeAst: AstAppend applied to scalars"
    xi : xsh -> case shapeAst y of
      [] -> error "shapeAst: AstAppend applied to scalars"
      yi : _ -> xi + yi : xsh
  AstSlice _n k v -> k : tail (shapeAst v)
  AstReverse v -> shapeAst v
  AstTranspose v -> case shapeAst v of
    i : k : sh -> k : i : sh
    sh -> sh  -- the operation is an identity if rank too small
  AstTransposeGeneral perm v ->
    let permutePrefix :: AstPermutation -> AstShape r -> AstShape r
        permutePrefix p l = V.toList $ VS.fromList l V.// zip p l
        sh = shapeAst v
    in if length sh < length perm
       then sh  -- the operation is an identity if rank too small
       else permutePrefix perm sh
  AstFlatten v -> [product $ shapeAst v]
  AstReshape sh _v -> sh
  AstBuildPair n (_var, v) -> n : shapeAst v
  AstGatherPair n (_var, is) v ->
    let sh = shapeAst v
    in assert (length sh >= length is `blame` v1)
       $ n : drop (length is) sh
  AstSum0 _v -> []
  AstDot0 _x _y -> []
  AstFromList0N sh _l -> sh
  AstFromVector0N sh _l -> sh
  AstKonst0N sh _r -> sh
  AstBuildPair0N sh (_vars, _r) -> sh
  AstOMap0 (_var, _r) _e -> []
  AstOMap1 (_var, _r) e -> shapeAst e
  AstVar0 _var -> []
  AstVar1 n _var -> [n]

lenghtAst :: (Show r, Numeric r) => Ast (1 + n) r -> Int
lenghtAst v1 = case shapeAst v1 of
  [] -> error "lenghtAst: impossible rank 0 found"
  n : _ -> n

substituteAst :: (Show r, Numeric r)
              => AstInt r -> AstVarName Int -> Ast n r -> Ast n r
substituteAst i var v1 = case v1 of
  AstOp opCode args -> AstOp opCode $ map (substituteAst i var) args
  AstCond b a1 a2 -> AstCond (substituteAstBool i var b)
                             (substituteAst i var a1) (substituteAst i var a2)
  AstSelect n (_var, b) a1 a2 ->
    AstSelect n (_var, substituteAstBool i var b)
              (substituteAst i var a1) (substituteAst i var a2)
  AstConstInt i2 -> AstConstInt $ substituteAstInt i var i2
  AstConst _a -> v1
  AstConstant (AstPrimalPart1 a) ->
    AstConstant (AstPrimalPart1 $ substituteAst i var a)
  AstScale (AstPrimalPart1 r) d ->
    AstScale (AstPrimalPart1 $ substituteAst i var r) (substituteAst i var d)
  AstIndex v i2 -> AstIndex (substituteAst i var v) (substituteAstInt i var i2)
  AstIndexN v is ->
    AstIndexN (substituteAst i var v) (map (substituteAstInt i var) is)
  AstSum v -> AstSum (substituteAst i var v)
  AstFromList l -> AstFromList $ map (substituteAst i var) l
  AstFromVector l -> AstFromVector $ V.map (substituteAst i var) l
  AstKonst n v -> AstKonst n (substituteAst i var v)
  AstAppend x y -> AstAppend (substituteAst i var x) (substituteAst i var y)
  AstSlice n k v -> AstSlice n k (substituteAst i var v)
  AstReverse v -> AstReverse (substituteAst i var v)
  AstTranspose v -> AstTranspose (substituteAst i var v)
  AstTransposeGeneral perm v -> AstTransposeGeneral perm (substituteAst i var v)
  AstFlatten v -> AstFlatten (substituteAst i var v)
  AstReshape sh v -> AstReshape sh (substituteAst i var v)
  AstBuildPair n (var2, v) ->
    AstBuildPair n (var2, substituteAst i var v)
  AstGatherPair n (var2, is) v ->
    AstGatherPair n (var2, map (substituteAstInt i var) is)
                  (substituteAst i var v)
  AstSum0 v -> AstSum0 (substituteAst i var v)
  AstDot0 x y -> AstDot0 (substituteAst i var x) (substituteAst i var y)
  AstFromList0N sh l -> AstFromList0N sh $ map (substituteAst i var) l
  AstFromVector0N sh l -> AstFromVector0N sh $ V.map (substituteAst i var) l
  AstKonst0N sh r -> AstKonst0N sh (substituteAst i var r)
  AstBuildPair0N sh (vars, r) -> AstBuildPair0N sh (vars, substituteAst i var r)
  AstOMap0 (var2, r) e ->
    AstOMap0 (var2, substituteAst i var r) (substituteAst i var e)
  AstOMap1 (var2, r) e ->
    AstOMap1 (var2, substituteAst i var r) (substituteAst i var e)
  AstVar0 _var -> v1
  AstVar1 _n _var -> v1

substituteAstInt :: (Show r, Numeric r)
                 => AstInt r -> AstVarName Int -> AstInt r -> AstInt r
substituteAstInt i var i2 = case i2 of
  AstIntOp opCodeInt args ->
    AstIntOp opCodeInt $ map (substituteAstInt i var) args
  AstIntCond b a1 a2 ->
    AstIntCond (substituteAstBool i var b)
               (substituteAstInt i var a1) (substituteAstInt i var a2)
  AstIntConst _a -> i2
  AstIntVar var2 -> if var == var2 then i else i2
  AstMinIndex v -> AstMinIndex (substituteAst i var v)
  AstMaxIndex v -> AstMaxIndex (substituteAst i var v)

substituteAstBool :: (Show r, Numeric r)
                  => AstInt r -> AstVarName Int -> AstBool r -> AstBool r
substituteAstBool i var b1 = case b1 of
  AstBoolOp opCodeBool args ->
    AstBoolOp opCodeBool $ map (substituteAstBool i var) args
  AstBoolConst _a -> b1
  AstRel opCodeRel args ->
    AstRel opCodeRel $ map (substituteAst i var) args
  AstRelInt opCodeRel args ->
    AstRelInt opCodeRel $ map (substituteAstInt i var) args
