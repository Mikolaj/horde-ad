{-# LANGUAGE DataKinds, GADTs, GeneralizedNewtypeDeriving, StandaloneDeriving,
             TypeFamilies, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
-- | AST of the code to be differentiated. It's needed mostly for handling
-- higher order operations such as build and map, but can be used
-- for arbitrary code transformations at the cost of limiting
-- expressiveness of transformed fragments to what AST captures.
module HordeAd.Core.Ast
  ( AstIndex, AstVarList
  , Ast(..), AstPrimalPart1(..)
  , AstVarName(..), AstVar(..)
  , AstInt(..), AstBool(..)
  , OpCode(..), OpCodeInt(..), OpCodeBool(..), OpCodeRel(..)
  , shapeAst, lengthAst
  , intVarInAst, intVarInAstInt, intVarInAstBool
  , substituteAst, substituteAstInt, substituteAstBool
  , unsafeGetFreshAstVar
  ) where

import Prelude

import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import           Data.IORef.Unboxed (Counter, atomicAddCounter_, newCounter)
import           Data.Kind (Type)
import           Data.MonoTraversable (Element, MonoFunctor (omap))
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat, type (+))
import           Numeric.LinearAlgebra (Numeric)
import           System.IO.Unsafe (unsafePerformIO)

import HordeAd.Core.SizedIndex
import HordeAd.Internal.SizedList

-- * Ast definitions

type AstIndex n r = Index n (AstInt r)

type AstVarList n = SizedList n (AstVarName Int)

-- We use here @ShapeInt@ for simplicity. @Shape n (AstInt r)@ gives
-- more expressiveness, but leads to irregular tensors,
-- especially after vectorization, and prevents statically known shapes.
-- However, if we switched to @Data.Array.Shaped@ and moved most of the shapes
-- to the type level, we'd recover some of the expressiveness, while retaining
-- statically known (type-parameterized) shapes.

-- TODO: consider sharing Ast expressions, both within the primal part
-- and between primal and dual
-- | AST for a tensor of rank n and elements r that is meant
-- to be differentiated.
data Ast :: Nat -> Type -> Type where
  -- To permit defining objective functions in Ast, not just constants:
  AstVar :: ShapeInt n -> AstVarName (OR.Array n r) -> Ast n r

  -- For the numeric classes:
  AstOp :: OpCode -> [Ast n r] -> Ast n r

  -- For HasPrimal class and the future Conditional/Boolean/Eq'/Ord' classes:
  AstConst :: OR.Array n r -> Ast n r
  AstConstant :: AstPrimalPart1 n r -> Ast n r
  -- syntactic sugar:
  AstScale :: AstPrimalPart1 n r -> Ast n r -> Ast n r
  AstCond :: AstBool r -> Ast n r -> Ast n r -> Ast n r

  -- For VectorLike and Tensor class:
  AstConstInt :: AstInt r -> Ast 0 r
    -- needed, because toInteger and so fromIntegral is not defined for Ast
  AstIndexN :: forall m n r. KnownNat m
            => Ast (m + n) r -> AstIndex m r -> Ast n r
    -- first ix is for outermost dimension; empty index means identity;
    -- the name keeps the N to less confusion with AstIndex type
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
  AstTransposeGeneral :: Permutation -> Ast n r -> Ast n r
    -- emerges from vectorizing AstTranspose
  AstFlatten :: KnownNat n
             => Ast n r -> Ast 1 r
  AstReshape :: KnownNat n
             => ShapeInt m -> Ast n r -> Ast m r
    -- emerges from vectorizing AstFlatten
  AstBuild1 :: Int -> (AstVarName Int, Ast n r) -> Ast (1 + n) r
    -- indicates a failure in vectorization, but may be recoverable later on
  AstGather1 :: forall p n r. KnownNat p
             => (AstVarName Int, AstIndex p r) -> Ast (p + n) r
             -> Int -> Ast (1 + n) r
    -- emerges from vectorizing AstIndexN applied to term with no build variable
  AstGather :: forall m p n r. (KnownNat m, KnownNat p, KnownNat n)
            => (AstVarList m, AstIndex p r) -> Ast (p + n) r
            -> ShapeInt (m + n) -> Ast (m + n) r
    -- emerges from vectorizing AstGather1

  -- For MonoFunctor class, which is needed for a particularly
  -- fast implementation of relu and offers fast, primal-part only, mapping.
  -- TODO: this is really only needed in AstPrimalPart, but making
  -- AstPrimalPart data instead of a newtype would complicate a lot of code.
  AstOMap :: (AstVarName (OR.Array 0 r), Ast 0 r) -> Ast n r -> Ast n r

  -- Spurious, but can be re-enabled at any time:
--  AstBuild :: forall m n r.
--              ShapeInt (m + n) -> (AstVarList m, Ast n r) -> Ast (m + n) r
    -- not needed for anythihg, but an extra pass may join nested AstBuild1
    -- into these for better performance on some hardware

deriving instance (Show r, Numeric r) => Show (Ast n r)

newtype AstPrimalPart1 n r = AstPrimalPart1 (Ast n r)
 deriving Show

newtype AstVarName t = AstVarName Int
 deriving Eq

-- An unlawful instance to prevent spam when tracing and debugging.
instance Show (AstVarName t) where
  show (AstVarName n) = "Var" ++ show n

data AstVar a =
    AstVarR a
  | AstVarI Int
 deriving Show

-- In AstInt and AstBool, the Ast terms are morally AstPrimalPart,
-- since their derivative part is not used.
-- TODO: introduce AstPrimalPart explicitly when convenient, e.g.,
-- as soon as AstPrimalPart gets more constructors.

-- The argument is the underlying scalar.
data AstInt :: Type -> Type where
  AstIntVar :: AstVarName Int -> AstInt r
  AstIntOp :: OpCodeInt -> [AstInt r] -> AstInt r
  AstIntConst :: Int -> AstInt r
  AstIntCond :: AstBool r -> AstInt r -> AstInt r -> AstInt r
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
-- to include AstInt in Ast via fromIntegral, hence AstConstInt.
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
unsafeAstVarCounter = unsafePerformIO (newCounter 1)

unsafeGetFreshAstVar :: IO (AstVarName a)
{-# INLINE unsafeGetFreshAstVar #-}
unsafeGetFreshAstVar = AstVarName <$> atomicAddCounter_ unsafeAstVarCounter 1

astOmap :: (Ast 0 r -> Ast 0 r) -> Ast n r -> Ast n r
{-# NOINLINE astOmap #-}
astOmap f e = unsafePerformIO $ do
  freshAstVar <- unsafeGetFreshAstVar
  return $! AstOMap (freshAstVar, f (AstVar ZS freshAstVar)) e

instance MonoFunctor (AstPrimalPart1 n r) where
  omap f (AstPrimalPart1 x) =
    let g y = let AstPrimalPart1 z = f (AstPrimalPart1 y)
              in z
    in AstPrimalPart1 (astOmap g x)

-- This is cheap and dirty. We don't shape-check the terms and we don't
-- unify or produce (partial) results with variables. Instead, we investigate
-- only one path and fail if it doesn't contain enough information
-- to determine shape. If we don't switch to @Data.Array.Shaped@
-- or revert to fully dynamic shapes, we need to redo this with more rigour.
shapeAst :: forall n r. (KnownNat n, Show r, Numeric r)
         => Ast n r -> ShapeInt n
shapeAst v1 = case v1 of
  AstVar sh _var -> sh
  AstOp _opCode args -> case args of
    [] -> error "shapeAst: AstOp with no arguments"
    t : _ -> shapeAst t
  AstConst a -> listShapeToShape $ OR.shapeL a
  AstConstant (AstPrimalPart1 a) -> shapeAst a
  AstScale (AstPrimalPart1 r) _d -> shapeAst r
  AstCond _b a1 _a2 -> shapeAst a1
  AstConstInt _i -> ZS
  AstIndexN v (_is :: Index m (AstInt r)) -> dropShape @m (shapeAst v)
  AstSum v -> tailShape $ shapeAst v
  AstFromList l -> case l of
    [] -> error "shapeAst: AstFromList with no arguments"
    t : _ -> length l :$ shapeAst t
  AstFromVector l -> case V.toList l of
    [] -> error "shapeAst: AstFromVector with no arguments"
    t : _ -> V.length l :$ shapeAst t
  AstKonst s v -> s :$ shapeAst v
  AstAppend x y -> case shapeAst x of
    ZS -> error "shapeAst: impossible pattern needlessly required"
    xi :$ xsh -> case shapeAst y of
      ZS -> error "shapeAst: impossible pattern needlessly required"
      yi :$ _ -> xi + yi :$ xsh
  AstSlice _n k v -> k :$ tailShape (shapeAst v)
  AstReverse v -> shapeAst v
  AstTranspose v -> case shapeAst v of
    i :$ k :$ sh -> k :$ i :$ sh
    sh -> sh  -- the operation is identity if rank too small
  AstTransposeGeneral perm v ->
    if valueOf @n < length perm
    then shapeAst v  -- the operation is identity if rank too small
    else permutePrefixShape perm (shapeAst v)
  AstFlatten v -> flattenShape (shapeAst v)
  AstReshape sh _v -> sh
  AstBuild1 k (_var, v) -> k :$ shapeAst v
  AstGather1 (_var, _is :: Index p (AstInt r)) v k ->
    k :$ dropShape @p (shapeAst v)
  AstGather (_var, _is) _v sh -> sh
  AstOMap (_var, _r) e -> shapeAst e

-- Length of the outermost dimension.
lengthAst :: (KnownNat n, Show r, Numeric r) => Ast (1 + n) r -> Int
lengthAst v1 = case shapeAst v1 of
  ZS -> error "lengthAst: impossible pattern needlessly required"
  k :$ _ -> k

intVarInAst :: AstVarName Int -> Ast n r -> Bool
intVarInAst var = \case
  AstVar{} -> False  -- not an int variable
  AstOp _ l -> any (intVarInAst var) l
  AstConst{} -> False
  AstConstant (AstPrimalPart1 v) -> intVarInAst var v
  AstScale (AstPrimalPart1 v) u -> intVarInAst var v || intVarInAst var u
  AstCond b x y ->
    intVarInAstBool var b || intVarInAst var x || intVarInAst var y
  AstConstInt k -> intVarInAstInt var k
  AstIndexN v is -> intVarInAst var v || any (intVarInAstInt var) is
  AstSum v -> intVarInAst var v
  AstFromList l -> any (intVarInAst var) l  -- down from rank 1 to 0
  AstFromVector vl -> any (intVarInAst var) $ V.toList vl
  AstKonst _ v -> intVarInAst var v
  AstAppend v u -> intVarInAst var v || intVarInAst var u
  AstSlice _ _ v -> intVarInAst var v
  AstReverse v -> intVarInAst var v
  AstTranspose v -> intVarInAst var v
  AstTransposeGeneral _ v -> intVarInAst var v
  AstFlatten v -> intVarInAst var v
  AstReshape _ v -> intVarInAst var v
  AstBuild1 _ (_, v) -> intVarInAst var v
  AstGather1 (_, is) v _ -> any (intVarInAstInt var) is || intVarInAst var v
  AstGather (_, is) v _ -> any (intVarInAstInt var) is || intVarInAst var v
  AstOMap (_, v) u -> intVarInAst var v || intVarInAst var u
    -- the variable in binder position, so ignored (and should be distinct)

intVarInAstInt :: AstVarName Int -> AstInt r -> Bool
intVarInAstInt var = \case
  AstIntVar var2 -> var == var2  -- the only int variable not in binder position
  AstIntOp _ l -> any (intVarInAstInt var) l
  AstIntConst{} -> False
  AstIntCond b x y ->
    intVarInAstBool var b || intVarInAstInt var x || intVarInAstInt var y
  AstMinIndex v -> intVarInAst var v
  AstMaxIndex v -> intVarInAst var v

intVarInAstBool :: AstVarName Int -> AstBool r -> Bool
intVarInAstBool var = \case
  AstBoolOp _ l -> any (intVarInAstBool var) l
  AstBoolConst{} -> False
  AstRel _ l -> any (intVarInAst var) l
  AstRelInt _ l  -> any (intVarInAstInt var) l

substituteAst :: (Show r, Numeric r)
              => AstInt r -> AstVarName Int -> Ast n r -> Ast n r
substituteAst i var v1 = case v1 of
  AstVar _sh _var -> v1
  AstOp opCode args -> AstOp opCode $ map (substituteAst i var) args
  AstConst _a -> v1
  AstConstant (AstPrimalPart1 a) ->
    AstConstant (AstPrimalPart1 $ substituteAst i var a)
  AstScale (AstPrimalPart1 r) d ->
    AstScale (AstPrimalPart1 $ substituteAst i var r) (substituteAst i var d)
  AstCond b a1 a2 -> AstCond (substituteAstBool i var b)
                             (substituteAst i var a1) (substituteAst i var a2)
  AstConstInt i2 -> AstConstInt $ substituteAstInt i var i2
  AstIndexN v is ->
    AstIndexN (substituteAst i var v) (fmap (substituteAstInt i var) is)
  AstSum v -> AstSum (substituteAst i var v)
  AstFromList l -> AstFromList $ map (substituteAst i var) l
  AstFromVector l -> AstFromVector $ V.map (substituteAst i var) l
  AstKonst s v -> AstKonst s (substituteAst i var v)
  AstAppend x y -> AstAppend (substituteAst i var x) (substituteAst i var y)
  AstSlice k s v -> AstSlice k s (substituteAst i var v)
  AstReverse v -> AstReverse (substituteAst i var v)
  AstTranspose v -> AstTranspose (substituteAst i var v)
  AstTransposeGeneral perm v -> AstTransposeGeneral perm (substituteAst i var v)
  AstFlatten v -> AstFlatten (substituteAst i var v)
  AstReshape sh v -> AstReshape sh (substituteAst i var v)
  AstBuild1 k (var2, v) ->
    AstBuild1 k (var2, substituteAst i var v)
  AstGather1 (var2, is) v k ->
    AstGather1 (var2, fmap (substituteAstInt i var) is)
               (substituteAst i var v) k
  AstGather (vars, is) v sh ->
    AstGather (vars, fmap (substituteAstInt i var) is)
              (substituteAst i var v) sh
  AstOMap (var2, r) e ->
    AstOMap (var2, substituteAst i var r) (substituteAst i var e)

substituteAstInt :: (Show r, Numeric r)
                 => AstInt r -> AstVarName Int -> AstInt r -> AstInt r
substituteAstInt i var i2 = case i2 of
  AstIntVar var2 -> if var == var2 then i else i2
  AstIntOp opCodeInt args ->
    AstIntOp opCodeInt $ map (substituteAstInt i var) args
  AstIntConst _a -> i2
  AstIntCond b a1 a2 ->
    AstIntCond (substituteAstBool i var b)
               (substituteAstInt i var a1) (substituteAstInt i var a2)
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
