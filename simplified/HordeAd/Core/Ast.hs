{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | AST of the code to be differentiated. It's needed mostly for handling
-- higher order operations such as build and map, but can be used
-- for arbitrary code transformations at the cost of limiting
-- expressiveness of transformed fragments to what AST captures.
module HordeAd.Core.Ast
  ( AstIndex, AstVarList
  , AstVarName(..), AstDynamicVarName(..)
  , Ast(..), AstPrimalPart(..), AstDynamic(..), Ast0(..)
  , AstInt(..), AstBool(..)
  , OpCode(..), OpCodeInt(..), OpCodeBool(..), OpCodeRel(..)
  , astCond
  , shapeAst, lengthAst
  , intVarInAst, intVarInAstInt, intVarInAstBool, intVarInIndex
  , substitute1Ast, substitute1AstInt, substitute1AstBool
  ) where

import Prelude

import qualified Data.Array.RankedS as OR
import           Data.Boolean
import           Data.Kind (Type)
import           Data.MonoTraversable (Element)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality ((:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits
  (KnownNat, Nat, OrderingI (..), cmpNat, sameNat, type (+))
import           Numeric.LinearAlgebra (Numeric)

import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorClass
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
  AstVar :: ShapeInt n -> AstVarName (TensorOf n r) -> Ast n r

  -- For the numeric classes:
  AstOp :: OpCode -> [Ast n r] -> Ast n r

  -- For HasPrimal class:
  AstConst :: OR.Array n r -> Ast n r
  AstConstant :: AstPrimalPart n r -> Ast n r

  -- For Tensor class:
  AstIndexZ :: forall m n r. KnownNat m
            => Ast (m + n) r -> AstIndex m r -> Ast n r
    -- first ix is for outermost dimension; empty index means identity,
    -- if index is out of bounds, the result is defined and is 0;
    -- however, vectorization is permitted to change the value
  AstSum :: Ast (1 + n) r -> Ast n r
  AstConstInt :: AstInt r -> Ast 0 r
    -- needed, because toInteger and so fromIntegral is not defined for Ast
  AstScatter :: forall m n p r. (KnownNat m, KnownNat n, KnownNat p)
             => ShapeInt (p + n) -> Ast (m + n) r
             -> (AstVarList m, AstIndex p r)
             -> Ast (p + n) r

  AstFromList :: KnownNat n
              => [Ast n r] -> Ast (1 + n) r
  AstFromVector :: KnownNat n
                => Data.Vector.Vector (Ast n r) -> Ast (1 + n) r
  AstKonst :: KnownNat n
           => Int -> Ast n r -> Ast (1 + n) r
  AstAppend :: KnownNat n
            => Ast (1 + n) r -> Ast (1 + n) r -> Ast (1 + n) r
  AstSlice :: KnownNat n
           => Int -> Int -> Ast (1 + n) r -> Ast (1 + n) r
  AstReverse :: KnownNat n
             => Ast (1 + n) r -> Ast (1 + n) r
  AstTranspose :: Permutation -> Ast n r -> Ast n r
    -- emerges from vectorizing AstTr
  AstReshape :: KnownNat n
             => ShapeInt m -> Ast n r -> Ast m r
    -- emerges from vectorizing AstFlatten
  AstBuild1 :: KnownNat n
            => Int -> (AstVarName Int, Ast n r) -> Ast (1 + n) r
    -- indicates a failure in vectorization, but may be recoverable later on
  AstGatherZ :: forall m n p r. (KnownNat m, KnownNat n, KnownNat p)
             => ShapeInt (m + n) -> Ast (p + n) r
             -> (AstVarList m, AstIndex p r)
             -> Ast (m + n) r
    -- emerges from vectorizing AstIndexZ applied to a term with no build
    -- variable; out of bounds indexing is permitted
    -- the case with many variables emerges from vectorizing the simpler case;
    -- out of bounds indexing is permitted
  AstFromDynamic :: AstDynamic r -> Ast n r

  -- Spurious, but can be re-enabled at any time:
--  AstBuildN :: forall m n r.
--               ShapeInt (m + n) -> (AstVarList m, Ast n r) -> Ast (m + n) r
    -- not needed for anythihg, but an extra pass may join nested AstBuild1
    -- into these for better performance on some hardware

deriving instance (Show r, Numeric r) => Show (Ast n r)

newtype AstPrimalPart n r = AstPrimalPart {unAstPrimalPart :: Ast n r}
 deriving Show

data AstDynamic :: Type -> Type where
  AstDynamicDummy :: AstDynamic r
  AstDynamicPlus :: AstDynamic r -> AstDynamic r -> AstDynamic r
  AstDynamicFrom :: KnownNat n
                 => Ast n r -> AstDynamic r

deriving instance (Show r, Numeric r) => Show (AstDynamic r)

newtype Ast0 r = Ast0 {unAst0 :: Ast 0 r}
 deriving Show

type instance Element (Ast0 r) = Ast0 r
type instance Element (Ast n r) = Ast0 r

newtype AstVarName t = AstVarName Int
 deriving Eq

-- An unlawful instance to prevent spam when tracing and debugging.
instance Show (AstVarName t) where
  show (AstVarName n) = "Var" ++ show n

data AstDynamicVarName r =
  forall n. KnownNat n => AstDynamicVarName (AstVarName (TensorOf n r))

-- In AstInt and AstBool, the Ast terms are morally AstPrimalPart,
-- since their derivative part is not used.
-- TODO: introduce AstPrimalPart explicitly when convenient, e.g.,
-- as soon as AstPrimalPart gets more constructors.

-- The argument is the underlying scalar.
data AstInt :: Type -> Type where
  AstIntVar :: AstVarName Int -> AstInt r
  AstIntOp :: OpCodeInt -> [AstInt r] -> AstInt r
  AstIntConst :: Int -> AstInt r
  AstIntFloor :: Ast 0 r -> AstInt r
  AstIntCond :: AstBool r -> AstInt r -> AstInt r -> AstInt r
  AstMinIndex1 :: Ast 1 r -> AstInt r
  AstMaxIndex1 :: Ast 1 r -> AstInt r
deriving instance (Show r, Numeric r) => Show (AstInt r)

data AstBool :: Type -> Type where
  AstBoolOp :: OpCodeBool -> [AstBool r] -> AstBool r
  AstBoolConst :: Bool -> AstBool r
  AstRel :: KnownNat n
         => OpCodeRel -> [Ast n r] -> AstBool r
  AstRelInt :: OpCodeRel -> [AstInt r] -> AstBool r
deriving instance (Show r, Numeric r) => Show (AstBool r)

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
  | QuotIntOp | RemIntOp
 deriving Show

data OpCodeBool =
    NotOp | AndOp | OrOp
 deriving Show

data OpCodeRel =
    EqOp | NeqOp
  | LeqOp| GeqOp | LsOp | GtOp
 deriving Show


-- * Unlawful instances of AST types; they are lawful modulo evaluation

type instance BooleanOf (AstInt r) = AstBool r

instance IfB (AstInt r) where
  ifB = AstIntCond

instance EqB (AstInt r) where
  v ==* u = AstRelInt EqOp [v, u]
  v /=* u = AstRelInt NeqOp [v, u]

instance OrdB (AstInt r) where
  v <* u = AstRelInt LsOp [v, u]
  v <=* u = AstRelInt LeqOp [v, u]
  v >* u = AstRelInt GtOp [v, u]
  v >=* u = AstRelInt GeqOp [v, u]

type instance BooleanOf (Ast n r) = AstBool r

instance KnownNat n => IfB (Ast n r) where
  ifB = astCond

-- No simplification at this point, so constant boolean unlikely,
-- but it's a constant time simplification, so no harm done.
astCond :: KnownNat n
        => AstBool r -> Ast n r -> Ast n r -> Ast n r
astCond (AstBoolConst b) v w = if b then v else w
astCond b (AstConstant (AstPrimalPart v)) (AstConstant (AstPrimalPart w)) =
  AstConstant $ AstPrimalPart $ AstIndexZ (AstFromList [v, w])
                                          (singletonIndex $ AstIntCond b 0 1)
astCond b v w = AstIndexZ (AstFromList [v, w])
                          (singletonIndex $ AstIntCond b 0 1)

instance KnownNat n => EqB (Ast n r) where
  v ==* u = AstRel EqOp [v, u]
  v /=* u = AstRel NeqOp [v, u]

instance KnownNat n => OrdB (Ast n r) where
  v <* u = AstRel LsOp [v, u]
  v <=* u = AstRel LeqOp [v, u]
  v >* u = AstRel GtOp [v, u]
  v >=* u = AstRel GeqOp [v, u]

type instance BooleanOf (AstPrimalPart n r) = AstBool r

instance KnownNat n => IfB (AstPrimalPart n r) where
  ifB b v w = AstPrimalPart $ astCond b (unAstPrimalPart v) (unAstPrimalPart w)

instance KnownNat n => EqB (AstPrimalPart n r) where
  v ==* u = AstRel EqOp [unAstPrimalPart v, unAstPrimalPart u]
  v /=* u = AstRel NeqOp [unAstPrimalPart v, unAstPrimalPart u]

instance KnownNat n => OrdB (AstPrimalPart n r) where
  v <* u = AstRel LsOp [unAstPrimalPart v, unAstPrimalPart u]
  v <=* u = AstRel LeqOp [unAstPrimalPart v, unAstPrimalPart u]
  v >* u = AstRel GtOp [unAstPrimalPart v, unAstPrimalPart u]
  v >=* u = AstRel GeqOp [unAstPrimalPart v, unAstPrimalPart u]

type instance BooleanOf (Ast0 r) = AstBool r

instance IfB (Ast0 r) where
  ifB b v w = Ast0 $ astCond b (unAst0 v) (unAst0 w)

instance EqB (Ast0 r) where
  v ==* u = AstRel EqOp [unAst0 v, unAst0 u]
  v /=* u = AstRel NeqOp [unAst0 v, unAst0 u]

instance OrdB (Ast0 r) where
  v <* u = AstRel LsOp [unAst0 v, unAst0 u]
  v <=* u = AstRel LeqOp [unAst0 v, unAst0 u]
  v >* u = AstRel GtOp [unAst0 v, unAst0 u]
  v >=* u = AstRel GeqOp [unAst0 v, unAst0 u]

-- See the comment about @Eq@ and @Ord@ in "DualNumber".
instance Eq (Ast n r) where
  _ == _ = error "Ast: can't evaluate terms for Eq"

instance Ord (OR.Array n r) => Ord (Ast n r) where
  max u v = AstOp MaxOp [u, v]
  min u v = AstOp MinOp [u, v]
  -- Unfortunately, the others can't be made to return @AstBool@.
  _ <= _ = error "Ast: can't evaluate terms for Ord"

instance (Num (OR.Array n r), KnownNat n) => Num (Ast n r) where
  u + v = AstOp PlusOp [u, v]
  u - v = AstOp MinusOp [u, v]
  u * v = AstOp TimesOp [u, v]
  negate u = AstOp NegateOp [u]
  abs v = AstOp AbsOp [v]
  signum v = AstOp SignumOp [v]
  fromInteger = case cmpNat (Proxy @n) (Proxy @2) of
    LTI -> AstConstant . AstPrimalPart . AstConst . fromInteger
      -- there is hope that for rank 1 hmatrix copes with the wrong shape
      -- and that neither orthotope nor hode-ad crashes before that
    _ ->  error "fromInteger (Ast n r): ambiguous shape"

instance (Real (OR.Array n r), KnownNat n) => Real (Ast n r) where
  toRational = undefined
    -- very low priority, since these are all extremely not continuous

instance (Fractional (OR.Array n r), KnownNat n) => Fractional (Ast n r) where
  u / v = AstOp DivideOp  [u, v]
  recip v = AstOp RecipOp [v]
  fromRational = AstConstant . AstPrimalPart . AstConst . fromRational

instance (Floating (OR.Array n r), KnownNat n) => Floating (Ast n r) where
  pi = AstConstant $ AstPrimalPart $ AstConst pi
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

instance (RealFrac (OR.Array n r), KnownNat n) => RealFrac (Ast n r) where
  properFraction = undefined
    -- The integral type doesn't have a Storable constraint,
    -- so we can't implement this (nor RealFracB from Boolean package).

instance (RealFloat (OR.Array n r), KnownNat n) => RealFloat (Ast n r) where
  atan2 u v = AstOp Atan2Op [u, v]
  -- We can be selective here and omit the other methods,
  -- most of which don't even have a differentiable codomain.
  floatRadix = undefined
  floatDigits = undefined
  floatRange = undefined
  decodeFloat = undefined
  encodeFloat = undefined
  isNaN = undefined
  isInfinite = undefined
  isDenormalized = undefined
  isNegativeZero = undefined
  isIEEE = undefined

instance Eq (AstPrimalPart n r) where
  _ == _ = error "AstPrimalPart: can't evaluate terms for Eq"

instance Ord (Ast n r) => Ord (AstPrimalPart n r) where
  max (AstPrimalPart u) (AstPrimalPart v) =
    AstPrimalPart (AstOp MaxOp [u, v])
  min (AstPrimalPart u) (AstPrimalPart v) =
    AstPrimalPart (AstOp MinOp [u, v])
  _ <= _ = error "AstPrimalPart: can't evaluate terms for Ord"

deriving instance Num (Ast n r) => Num (AstPrimalPart n r)
deriving instance Real (Ast n r) => Real (AstPrimalPart n r)
deriving instance Fractional (Ast n r) => Fractional (AstPrimalPart n r)
deriving instance Floating (Ast n r) => Floating (AstPrimalPart n r)
deriving instance RealFrac (Ast n r) => RealFrac (AstPrimalPart n r)
deriving instance RealFloat (Ast n r) => RealFloat (AstPrimalPart n r)

instance Eq (Ast0 r) where
  _ == _ = error "Ast0: can't evaluate terms for Eq"

instance Ord (Ast 0 r) => Ord (Ast0 r) where
  max (Ast0 u) (Ast0 v) =
    Ast0 (AstOp MaxOp [u, v])
  min (Ast0 u) (Ast0 v) =
    Ast0 (AstOp MinOp [u, v])
  _ <= _ = error "Ast0: can't evaluate terms for Ord"

deriving instance Num (Ast 0 r) => Num (Ast0 r)
deriving instance Real (Ast 0 r) => Real (Ast0 r)
deriving instance Fractional (Ast 0 r) => Fractional (Ast0 r)
deriving instance Floating (Ast 0 r) => Floating (Ast0 r)
deriving instance RealFrac (Ast 0 r) => RealFrac (Ast0 r)
deriving instance RealFloat (Ast 0 r) => RealFloat (Ast0 r)

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
  toRational = undefined
    -- very low priority, since these are all extremely not continuous

instance Enum (AstInt r) where
  toEnum = AstIntConst
  fromEnum = undefined  -- do we need to define out own Enum for this?

-- Warning: this class lacks toInteger, which also makes it impossible
-- to include AstInt in Ast via fromIntegral, hence AstConstInt.
-- Warning: div and mod operations are very costly (simplifying them
-- requires constructing conditionals, etc). If this error is removed,
-- they are going to work, but slowly.
instance Integral (AstInt r) where
  quot u v = AstIntOp QuotIntOp [u, v]
  rem u v = AstIntOp RemIntOp [u, v]
  quotRem u v = (AstIntOp QuotIntOp [u, v], AstIntOp RemIntOp [u, v])
  divMod _ _ = error "divMod: disabled; much less efficient than quot and rem"
  toInteger = undefined  -- we can't evaluate uninstantiated variables, etc.

instance Boolean (AstBool r) where
  true = AstBoolConst True
  false = AstBoolConst False
  notB b = AstBoolOp NotOp [b]
  b &&* c = AstBoolOp AndOp [b, c]
  b ||* c = AstBoolOp OrOp [b, c]


-- * Shape calculation

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
  AstConstant (AstPrimalPart a) -> shapeAst a
  AstIndexZ v (_is :: Index m (AstInt r)) -> dropShape @m (shapeAst v)
  AstSum v -> tailShape $ shapeAst v
  AstConstInt _i -> ZS
  AstScatter sh _ _ -> sh
  AstFromList l -> case l of
    [] -> case sameNat (Proxy @n) (Proxy @1) of
      Just Refl -> singletonShape 0  -- the only case where we can guess sh
      _ -> error "shapeAst: AstFromList with no arguments"
    t : _ -> length l :$ shapeAst t
  AstFromVector l -> case V.toList l of
    [] -> case sameNat (Proxy @n) (Proxy @1) of
      Just Refl -> singletonShape 0
      _ ->  error "shapeAst: AstFromVector with no arguments"
    t : _ -> V.length l :$ shapeAst t
  AstKonst s v -> s :$ shapeAst v
  AstAppend x y -> case shapeAst x of
    ZS -> error "shapeAst: impossible pattern needlessly required"
    xi :$ xsh -> case shapeAst y of
      ZS -> error "shapeAst: impossible pattern needlessly required"
      yi :$ _ -> xi + yi :$ xsh
  AstSlice _n k v -> k :$ tailShape (shapeAst v)
  AstReverse v -> shapeAst v
  AstTranspose perm v -> permutePrefixShape perm (shapeAst v)
  AstReshape sh _v -> sh
  AstBuild1 k (_var, v) -> k :$ shapeAst v
  AstGatherZ sh _v (_vars, _ix) -> sh
  AstFromDynamic v -> listShapeToShape $ shapeAstDynamic v

shapeAstDynamic :: (Show r, Numeric r)
                => AstDynamic r -> [Int]
shapeAstDynamic v1 = case v1 of
  AstDynamicDummy -> []
  AstDynamicPlus v _u -> shapeAstDynamic v
  AstDynamicFrom w -> shapeToList $ shapeAst w

-- Length of the outermost dimension.
lengthAst :: (KnownNat n, Show r, Numeric r) => Ast (1 + n) r -> Int
lengthAst v1 = case shapeAst v1 of
  ZS -> error "lengthAst: impossible pattern needlessly required"
  k :$ _ -> k


-- * Variable occurence detection

intVarInAst :: AstVarName Int -> Ast n r -> Bool
intVarInAst var = \case
  AstVar{} -> False  -- not an int variable
  AstOp _ l -> any (intVarInAst var) l
  AstConst{} -> False
  AstConstant (AstPrimalPart v) -> intVarInAst var v
  AstIndexZ v ix -> intVarInAst var v || intVarInIndex var ix
  AstSum v -> intVarInAst var v
  AstConstInt k -> intVarInAstInt var k
  AstFromList l -> any (intVarInAst var) l  -- down from rank 1 to 0
  AstScatter _ v (vars, ix) -> all (var /=) vars && intVarInIndex var ix
                               || intVarInAst var v
  AstFromVector vl -> any (intVarInAst var) $ V.toList vl
  AstKonst _ v -> intVarInAst var v
  AstAppend v u -> intVarInAst var v || intVarInAst var u
  AstSlice _ _ v -> intVarInAst var v
  AstReverse v -> intVarInAst var v
  AstTranspose _ v -> intVarInAst var v
  AstReshape _ v -> intVarInAst var v
  AstBuild1 _ (var2, v) -> var /= var2 && intVarInAst var v
  AstGatherZ _ v (vars, ix) -> all (var /=) vars && intVarInIndex var ix
                               || intVarInAst var v
  AstFromDynamic v -> intVarInAstDynamic var v

intVarInAstDynamic :: AstVarName Int -> AstDynamic r -> Bool
intVarInAstDynamic var = \case
  AstDynamicDummy -> False
  AstDynamicPlus v u -> intVarInAstDynamic var v || intVarInAstDynamic var u
  AstDynamicFrom w -> intVarInAst var w

intVarInAstInt :: AstVarName Int -> AstInt r -> Bool
intVarInAstInt var = \case
  AstIntVar var2 -> var == var2  -- the only int variable not in binder position
  AstIntOp _ l -> any (intVarInAstInt var) l
  AstIntConst{} -> False
  AstIntFloor v -> intVarInAst var v
  AstIntCond b x y ->
    intVarInAstBool var b || intVarInAstInt var x || intVarInAstInt var y
  AstMinIndex1 v -> intVarInAst var v
  AstMaxIndex1 v -> intVarInAst var v

intVarInAstBool :: AstVarName Int -> AstBool r -> Bool
intVarInAstBool var = \case
  AstBoolOp _ l -> any (intVarInAstBool var) l
  AstBoolConst{} -> False
  AstRel _ l -> any (intVarInAst var) l
  AstRelInt _ l  -> any (intVarInAstInt var) l

intVarInIndex :: AstVarName Int -> AstIndex n r -> Bool
intVarInIndex var = any (intVarInAstInt var)


-- * Substitution

substitute1Ast :: (Show r, Numeric r)
               => AstInt r -> AstVarName Int -> Ast n r -> Ast n r
substitute1Ast i var v1 = case v1 of
  AstVar _sh _var -> v1
  AstOp opCode args -> AstOp opCode $ map (substitute1Ast i var) args
  AstConst _a -> v1
  AstConstant (AstPrimalPart a) ->
    AstConstant (AstPrimalPart $ substitute1Ast i var a)
  AstIndexZ v is ->
    AstIndexZ (substitute1Ast i var v) (fmap (substitute1AstInt i var) is)
  AstSum v -> AstSum (substitute1Ast i var v)
  AstConstInt i2 -> AstConstInt $ substitute1AstInt i var i2
  AstScatter sh v (vars, ix) ->
    if any (== var) vars
    then AstScatter sh (substitute1Ast i var v) (vars, ix)
    else AstScatter sh (substitute1Ast i var v)
                       (vars, fmap (substitute1AstInt i var) ix)
  AstFromList l -> AstFromList $ map (substitute1Ast i var) l
  AstFromVector l -> AstFromVector $ V.map (substitute1Ast i var) l
  AstKonst s v -> AstKonst s (substitute1Ast i var v)
  AstAppend x y -> AstAppend (substitute1Ast i var x) (substitute1Ast i var y)
  AstSlice k s v -> AstSlice k s (substitute1Ast i var v)
  AstReverse v -> AstReverse (substitute1Ast i var v)
  AstTranspose perm v -> AstTranspose perm (substitute1Ast i var v)
  AstReshape sh v -> AstReshape sh (substitute1Ast i var v)
  AstBuild1 k (var2, v) ->
    if var == var2
    then v1
    else AstBuild1 k (var2, substitute1Ast i var v)
  AstGatherZ sh v (vars, ix) ->
    if any (== var) vars
    then AstGatherZ sh (substitute1Ast i var v) (vars, ix)
    else AstGatherZ sh (substitute1Ast i var v)
                       (vars, fmap (substitute1AstInt i var) ix)
  AstFromDynamic v -> AstFromDynamic $ substitute1AstDynamic i var v

substitute1AstDynamic
  :: (Show r, Numeric r)
  => AstInt r -> AstVarName Int -> AstDynamic r -> AstDynamic r
substitute1AstDynamic i var v1 = case v1 of
  AstDynamicDummy -> v1
  AstDynamicPlus v u -> AstDynamicPlus (substitute1AstDynamic i var v)
                                       (substitute1AstDynamic i var u)
  AstDynamicFrom w -> AstDynamicFrom $ substitute1Ast i var w

substitute1AstInt :: (Show r, Numeric r)
                  => AstInt r -> AstVarName Int -> AstInt r -> AstInt r
substitute1AstInt i var i2 = case i2 of
  AstIntVar var2 -> if var == var2 then i else i2
  AstIntOp opCodeInt args ->
    AstIntOp opCodeInt $ map (substitute1AstInt i var) args
  AstIntConst _a -> i2
  AstIntFloor v -> AstIntFloor $ substitute1Ast i var v
  AstIntCond b a1 a2 ->
    AstIntCond (substitute1AstBool i var b)
               (substitute1AstInt i var a1) (substitute1AstInt i var a2)
  AstMinIndex1 v -> AstMinIndex1 (substitute1Ast i var v)
  AstMaxIndex1 v -> AstMaxIndex1 (substitute1Ast i var v)

substitute1AstBool :: (Show r, Numeric r)
                   => AstInt r -> AstVarName Int -> AstBool r -> AstBool r
substitute1AstBool i var b1 = case b1 of
  AstBoolOp opCodeBool args ->
    AstBoolOp opCodeBool $ map (substitute1AstBool i var) args
  AstBoolConst _a -> b1
  AstRel opCodeRel args ->
    AstRel opCodeRel $ map (substitute1Ast i var) args
  AstRelInt opCodeRel args ->
    AstRelInt opCodeRel $ map (substitute1AstInt i var) args
