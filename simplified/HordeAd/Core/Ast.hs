{-# LANGUAGE DerivingStrategies, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | AST of the code to be differentiated. It's needed mostly for handling
-- higher order operations such as build and map and for producing reusable
-- gradients, but can be used for arbitrary code transformations
-- at the cost of limiting expressiveness of transformed fragments
-- to what AST captures.
module HordeAd.Core.Ast
  ( ShowAst, AstIndex, AstVarList, NodeId(..)
  , Ast(..), AstNoVectorize(..), AstPrimalPart(..), AstDualPart(..)
  , AstDynamic(..), AstDomains(..), unwrapAstDomains, Ast0(..)
  , AstVarId, intToAstVarId, AstVarName(..), AstDynamicVarName(..)
  , AstInt(..), AstBool(..)
  , OpCode(..), OpCodeInt(..), OpCodeBool(..), OpCodeRel(..)
  , shapeAst, lengthAst
  , intVarInAst, intVarInAstInt, intVarInAstBool, intVarInIndex
  , substitute1Ast, substitute1AstDomains
  , substitute1AstInt, substitute1AstBool
  , printAstVar, printAstIntVar
  , printAstSimple, printAstDebug, printAstDomainsSimple, printAstDomainsDebug
  , astCond  -- only for tests
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import qualified Data.Array.RankedS as OR
import           Data.Boolean
import           Data.Either (fromLeft, fromRight)
import           Data.Kind (Type)
import           Data.MonoTraversable (Element)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality ((:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat, sameNat, type (+))
import           Numeric.LinearAlgebra (Numeric)

import HordeAd.Core.SizedIndex
import HordeAd.Internal.SizedList

-- * Ast definitions

type ShowAst r = (Show r, Numeric r)

type AstIndex n r = Index n (AstInt r)

type AstVarList n = SizedList n AstVarId

newtype NodeId = NodeId {fromNodeId :: Int}
 deriving newtype (Show, Enum)
   -- No Eq instance to limit hacks.

-- We use here @ShapeInt@ for simplicity. @Shape n (AstInt r)@ gives
-- more expressiveness, but leads to irregular tensors,
-- especially after vectorization, and prevents statically known shapes.

-- | AST for a tensor of rank n and elements r that is meant
-- to be differentiated.
data Ast :: Nat -> Type -> Type where
  -- To permit defining objective functions in Ast, not just constants:
  AstVar :: ShapeInt n -> AstVarId -> Ast n r
  AstLet :: KnownNat n
         => AstVarId -> Ast n r -> Ast m r -> Ast m r
  AstLetGlobal :: NodeId -> Ast m r -> Ast m r

  -- For the numeric classes:
  AstOp :: OpCode -> [Ast n r] -> Ast n r
  AstSumOfList :: [Ast n r] -> Ast n r
  AstIota :: Ast 1 r
    -- needed, because toInteger and so fromIntegral is not defined for Ast

  -- For the Tensor class:
  AstIndexZ :: forall m n r. KnownNat m
            => Ast (m + n) r -> AstIndex m r -> Ast n r
    -- first ix is for outermost dimension; empty index means identity,
    -- if index is out of bounds, the result is defined and is 0,
    -- but vectorization is permitted to change the value
  AstSum :: Ast (1 + n) r -> Ast n r
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
  AstReshape :: KnownNat n
             => ShapeInt m -> Ast n r -> Ast m r
  AstBuild1 :: KnownNat n
            => Int -> (AstVarId, Ast n r) -> Ast (1 + n) r
  AstGatherZ :: forall m n p r. (KnownNat m, KnownNat n, KnownNat p)
             => ShapeInt (m + n) -> Ast (p + n) r
             -> (AstVarList m, AstIndex p r)
             -> Ast (m + n) r
    -- out of bounds indexing is permitted

  -- For the forbidden half of the Tensor class:
  AstConst :: OR.Array n r -> Ast n r
  AstConstant :: AstPrimalPart n r -> Ast n r
  AstD :: AstPrimalPart n r -> AstDualPart n r -> Ast n r
  AstLetDomains :: Data.Vector.Vector AstVarId -> AstDomains r -> Ast m r
                -> Ast m r
deriving instance ShowAst r => Show (Ast n r)

newtype AstNoVectorize n r = AstNoVectorize {unAstNoVectorize :: Ast n r}
 deriving Show

newtype AstPrimalPart n r = AstPrimalPart {unAstPrimalPart :: Ast n r}
 deriving Show

newtype AstDualPart n r = AstDualPart {unAstDualPart :: Ast n r}
 deriving Show

data AstDynamic :: Type -> Type where
  AstDynamic :: KnownNat n
             => Ast n r -> AstDynamic r
deriving instance ShowAst r => Show (AstDynamic r)

data AstDomains :: Type -> Type where
  AstDomains :: Data.Vector.Vector (AstDynamic r) -> AstDomains r
  AstDomainsLet :: KnownNat n
                => AstVarId -> Ast n r -> AstDomains r -> AstDomains r
deriving instance ShowAst r => Show (AstDomains r)

unwrapAstDomains :: AstDomains r -> Data.Vector.Vector (AstDynamic r)
unwrapAstDomains = \case
  AstDomains l -> l
  AstDomainsLet _ _ v -> unwrapAstDomains v

newtype Ast0 r = Ast0 {unAst0 :: Ast 0 r}
 deriving Show

type instance Element (Ast0 r) = Ast0 r
type instance Element (Ast n r) = Ast0 r

-- We avoid adding a phantom type denoting the underlying scalar,
-- because the type families over tensor ranks make quanitified constraints
-- impossible and so the phantom type leads to passing explicit (and implicit)
-- type equality proofs around.
newtype AstVarId = AstVarId Int
 deriving (Eq, Show, Enum)

intToAstVarId :: Int -> AstVarId
intToAstVarId = AstVarId

newtype AstVarName t = AstVarName AstVarId
 deriving (Eq, Show)

data AstDynamicVarName :: Type -> Type where
  AstDynamicVarName :: KnownNat n
                    => AstVarName (OR.Array n r) -> AstDynamicVarName r

-- The argument is the underlying scalar.
data AstInt :: Type -> Type where
  AstIntVar :: AstVarId -> AstInt r
  AstIntOp :: OpCodeInt -> [AstInt r] -> AstInt r
  AstIntConst :: Int -> AstInt r
  AstIntFloor :: AstPrimalPart 0 r -> AstInt r
  AstIntCond :: AstBool r -> AstInt r -> AstInt r -> AstInt r
  AstMinIndex1 :: AstPrimalPart 1 r -> AstInt r
  AstMaxIndex1 :: AstPrimalPart 1 r -> AstInt r
deriving instance ShowAst r => Show (AstInt r)

data AstBool :: Type -> Type where
  AstBoolOp :: OpCodeBool -> [AstBool r] -> AstBool r
  AstBoolConst :: Bool -> AstBool r
  AstRel :: KnownNat n
         => OpCodeRel -> [AstPrimalPart n r] -> AstBool r
  AstRelInt :: OpCodeRel -> [AstInt r] -> AstBool r
deriving instance ShowAst r => Show (AstBool r)

-- Copied from the outlining mechanism deleted in
-- https://github.com/Mikolaj/horde-ad/commit/c59947e13082c319764ec35e54b8adf8bc01691f
data OpCode =
    MinusOp | TimesOp | NegateOp | AbsOp | SignumOp
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


-- * Unlawful boolean package instances of AST types; they are lawful modulo evaluation

type instance BooleanOf (Ast n r) = AstBool r

instance KnownNat n => IfB (Ast n r) where
  ifB = astCond

-- No simplification yet done at this point, so constant boolean unlikely,
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
  v ==* u = AstRel EqOp [AstPrimalPart v, AstPrimalPart u]
  v /=* u = AstRel NeqOp [AstPrimalPart v, AstPrimalPart u]

instance KnownNat n => OrdB (Ast n r) where
  v <* u = AstRel LsOp [AstPrimalPart v, AstPrimalPart u]
  v <=* u = AstRel LeqOp [AstPrimalPart v, AstPrimalPart u]
  v >* u = AstRel GtOp [AstPrimalPart v, AstPrimalPart u]
  v >=* u = AstRel GeqOp [AstPrimalPart v, AstPrimalPart u]

type instance BooleanOf (AstNoVectorize n r) = AstBool r

instance KnownNat n => IfB (AstNoVectorize n r) where
  ifB b v w = AstNoVectorize $ astCond b (unAstNoVectorize v)
                                         (unAstNoVectorize w)

instance KnownNat n => EqB (AstNoVectorize n r) where
  v ==* u = AstRel EqOp [ AstPrimalPart $ unAstNoVectorize v
                        , AstPrimalPart $ unAstNoVectorize u ]
  v /=* u = AstRel NeqOp [ AstPrimalPart $ unAstNoVectorize v
                         , AstPrimalPart $ unAstNoVectorize u ]

instance KnownNat n => OrdB (AstNoVectorize n r) where
  v <* u = AstRel LsOp [ AstPrimalPart $ unAstNoVectorize v
                       , AstPrimalPart $ unAstNoVectorize u ]
  v <=* u = AstRel LeqOp [ AstPrimalPart $ unAstNoVectorize v
                         , AstPrimalPart $ unAstNoVectorize u ]
  v >* u = AstRel GtOp [ AstPrimalPart $ unAstNoVectorize v
                       , AstPrimalPart $ unAstNoVectorize u ]
  v >=* u = AstRel GeqOp [ AstPrimalPart $ unAstNoVectorize v
                         , AstPrimalPart $ unAstNoVectorize u ]

type instance BooleanOf (AstPrimalPart n r) = AstBool r

instance KnownNat n => IfB (AstPrimalPart n r) where
  ifB b v w = AstPrimalPart $ astCond b (unAstPrimalPart v) (unAstPrimalPart w)

instance KnownNat n => EqB (AstPrimalPart n r) where
  v ==* u = AstRel EqOp [v, u]
  v /=* u = AstRel NeqOp [v, u]

instance KnownNat n => OrdB (AstPrimalPart n r) where
  v <* u = AstRel LsOp [v, u]
  v <=* u = AstRel LeqOp [v, u]
  v >* u = AstRel GtOp [v, u]
  v >=* u = AstRel GeqOp [v, u]

type instance BooleanOf (Ast0 r) = AstBool r

instance IfB (Ast0 r) where
  ifB b v w = Ast0 $ astCond b (unAst0 v) (unAst0 w)

instance EqB (Ast0 r) where
  v ==* u = AstRel EqOp [AstPrimalPart $ unAst0 v, AstPrimalPart $ unAst0 u]
  v /=* u = AstRel NeqOp [AstPrimalPart $ unAst0 v, AstPrimalPart $ unAst0 u]

instance OrdB (Ast0 r) where
  v <* u = AstRel LsOp [AstPrimalPart $ unAst0 v, AstPrimalPart $ unAst0 u]
  v <=* u = AstRel LeqOp [AstPrimalPart $ unAst0 v, AstPrimalPart $ unAst0 u]
  v >* u = AstRel GtOp [AstPrimalPart $ unAst0 v, AstPrimalPart $ unAst0 u]
  v >=* u = AstRel GeqOp [AstPrimalPart $ unAst0 v, AstPrimalPart $ unAst0 u]

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


-- * Unlawful numeric instances of AST types; they are lawful modulo evaluation

-- See the comment about @Eq@ and @Ord@ in "DualNumber".
instance Eq (Ast n r) where
  _ == _ = error "Ast: can't evaluate terms for Eq"

instance Ord (OR.Array n r) => Ord (Ast n r) where
  max u v = AstOp MaxOp [u, v]
  min u v = AstOp MinOp [u, v]
  -- Unfortunately, the others can't be made to return @AstBool@.
  _ <= _ = error "Ast: can't evaluate terms for Ord"

instance Num (OR.Array n r) => Num (Ast n r) where
  AstSumOfList lu + AstSumOfList lv = AstSumOfList (lu ++ lv)
  u + AstSumOfList l = AstSumOfList (u : l)
  AstSumOfList l + u = AstSumOfList (u : l)
  u + v = AstSumOfList [u, v]
  u - v = AstOp MinusOp [u, v]
  u * v = AstOp TimesOp [u, v]
    -- no hacks like for AstSumOfList, because when tscaleByScalar
    -- is reconstructed, it looks for the binary form
  negate u = AstOp NegateOp [u]
  abs v = AstOp AbsOp [v]
  signum v = AstOp SignumOp [v]
  fromInteger = AstConstant . AstPrimalPart . AstConst . fromInteger

instance Real (OR.Array n r) => Real (Ast n r) where
  toRational = undefined
    -- very low priority, since these are all extremely not continuous

instance Fractional (OR.Array n r) => Fractional (Ast n r) where
  u / v = AstOp DivideOp  [u, v]
  recip v = AstOp RecipOp [v]
  fromRational = AstConstant . AstPrimalPart . AstConst . fromRational

instance (Floating (OR.Array n r)) => Floating (Ast n r) where
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

instance RealFrac (OR.Array n r) => RealFrac (Ast n r) where
  properFraction = undefined
    -- The integral type doesn't have a Storable constraint,
    -- so we can't implement this (nor RealFracB from Boolean package).

instance RealFloat (OR.Array n r) => RealFloat (Ast n r) where
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

instance Eq (AstNoVectorize n r) where
  _ == _ = error "AstNoVectorize: can't evaluate terms for Eq"

instance Ord (Ast n r) => Ord (AstNoVectorize n r) where
  max (AstNoVectorize u) (AstNoVectorize v) =
    AstNoVectorize (AstOp MaxOp [u, v])
  min (AstNoVectorize u) (AstNoVectorize v) =
    AstNoVectorize (AstOp MinOp [u, v])
  _ <= _ = error "AstNoVectorize: can't evaluate terms for Ord"

deriving instance Num (Ast n r) => Num (AstNoVectorize n r)
deriving instance Real (Ast n r) => Real (AstNoVectorize n r)
deriving instance Fractional (Ast n r) => Fractional (AstNoVectorize n r)
deriving instance Floating (Ast n r) => Floating (AstNoVectorize n r)
deriving instance RealFrac (Ast n r) => RealFrac (AstNoVectorize n r)
deriving instance RealFloat (Ast n r) => RealFloat (AstNoVectorize n r)

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
  u + v = AstIntOp PlusIntOp [u, v]  -- simplification relies on binary form
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
  fromEnum = undefined  -- do we need to define our own Enum for this?

-- Warning: this class lacks toInteger, which also makes it impossible
-- to include AstInt in Ast via fromIntegral, hence AstIota.
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
shapeAst :: forall n r. (KnownNat n, ShowAst r)
         => Ast n r -> ShapeInt n
shapeAst v1 = case v1 of
  AstVar sh _var -> sh
  AstLet _ _ v -> shapeAst v
  AstLetGlobal _ v -> shapeAst v
  AstOp _opCode args -> case args of
    [] -> error "shapeAst: AstOp with no arguments"
    t : _ -> shapeAst t
  AstSumOfList args -> case args of
    [] -> error "shapeAst: AstSumOfList with no arguments"
    t : _ -> shapeAst t
  AstIota -> singletonShape (maxBound :: Int)  -- ought to be enough
  AstIndexZ v (_is :: Index m (AstInt r)) -> dropShape @m (shapeAst v)
  AstSum v -> tailShape $ shapeAst v
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
  AstTranspose perm v -> backpermutePrefixShape perm (shapeAst v)
  AstReshape sh _v -> sh
  AstBuild1 k (_var, v) -> k :$ shapeAst v
  AstGatherZ sh _v (_vars, _ix) -> sh
  AstConst a -> listShapeToShape $ OR.shapeL a
  AstConstant (AstPrimalPart a) -> shapeAst a
  AstD (AstPrimalPart u) _ -> shapeAst u
  AstLetDomains _ _ v -> shapeAst v

-- Length of the outermost dimension.
lengthAst :: (KnownNat n, ShowAst r) => Ast (1 + n) r -> Int
lengthAst v1 = case shapeAst v1 of
  ZS -> error "lengthAst: impossible pattern needlessly required"
  k :$ _ -> k


-- * Variable occurence detection

intVarInAst :: AstVarId -> Ast n r -> Bool
intVarInAst var = \case
  AstVar{} -> False  -- not an int variable
  AstLet var2 u v -> intVarInAst var u || var /= var2 && intVarInAst var v
  AstLetGlobal _ v -> intVarInAst var v
  AstOp _ l -> any (intVarInAst var) l
  AstSumOfList l -> any (intVarInAst var) l
  AstIota -> False
  AstIndexZ v ix -> intVarInAst var v || intVarInIndex var ix
  AstSum v -> intVarInAst var v
  AstScatter _ v (vars, ix) -> notElem var vars && intVarInIndex var ix
                               || intVarInAst var v
  AstFromList l -> any (intVarInAst var) l  -- down from rank 1 to 0
  AstFromVector vl -> any (intVarInAst var) $ V.toList vl
  AstKonst _ v -> intVarInAst var v
  AstAppend v u -> intVarInAst var v || intVarInAst var u
  AstSlice _ _ v -> intVarInAst var v
  AstReverse v -> intVarInAst var v
  AstTranspose _ v -> intVarInAst var v
  AstReshape _ v -> intVarInAst var v
  AstBuild1 _ (var2, v) -> var /= var2 && intVarInAst var v
  AstGatherZ _ v (vars, ix) -> notElem var vars && intVarInIndex var ix
                               || intVarInAst var v
  AstConst{} -> False
  AstConstant (AstPrimalPart v) -> intVarInAst var v
  AstD (AstPrimalPart u) (AstDualPart u') ->
    intVarInAst var u || intVarInAst var u'
  AstLetDomains vars l v ->
    intVarInAstDomains var l || notElem var vars && intVarInAst var v

intVarInAstDomains :: AstVarId -> AstDomains r -> Bool
intVarInAstDomains var = \case
  AstDomains l -> any (\(AstDynamic t) -> intVarInAst var t) l
  AstDomainsLet var2 u v ->
    intVarInAst var u || var /= var2 && intVarInAstDomains var v

intVarInAstInt :: AstVarId -> AstInt r -> Bool
intVarInAstInt var = \case
  AstIntVar var2 -> var == var2  -- the only int variable not in binder position
  AstIntOp _ l -> any (intVarInAstInt var) l
  AstIntConst{} -> False
  AstIntFloor (AstPrimalPart v) -> intVarInAst var v
  AstIntCond b x y ->
    intVarInAstBool var b || intVarInAstInt var x || intVarInAstInt var y
  AstMinIndex1 (AstPrimalPart v) -> intVarInAst var v
  AstMaxIndex1 (AstPrimalPart v) -> intVarInAst var v

intVarInAstBool :: AstVarId -> AstBool r -> Bool
intVarInAstBool var = \case
  AstBoolOp _ l -> any (intVarInAstBool var) l
  AstBoolConst{} -> False
  AstRel _ l -> any (intVarInAst var . unAstPrimalPart) l
  AstRelInt _ l  -> any (intVarInAstInt var) l

intVarInIndex :: AstVarId -> AstIndex n r -> Bool
intVarInIndex var = any (intVarInAstInt var)


-- * Substitution

-- The Either is a hack until we merge Ast and AstInt.
substitute1Ast :: forall m n r. (ShowAst r, KnownNat m, KnownNat n)
               => Either (Ast m r) (AstInt r) -> AstVarId -> Ast n r
               -> Ast n r
substitute1Ast i var v1 = case v1 of
  AstVar sh var2 ->
    if var == var2
    then case sameNat (Proxy @m) (Proxy @n) of
      Just Refl -> let t = fromLeft (error "substitute1Ast: Var") i
                   in assert (shapeAst t == sh) t
      _ -> error "substitute1Ast: n"
    else v1
  AstLet var2 u v ->
    if var == var2
    then AstLet var2 (substitute1Ast i var u) v
    else AstLet var2 (substitute1Ast i var u) (substitute1Ast i var v)
  AstLetGlobal _ v -> substitute1Ast i var v
    -- substitution breaks global sharing
    -- TODO: here and in all term transformations (but not in interpretAst)
    -- start by building a graph and replacing all AstLetGlobal with AstLet
  AstOp opCode args -> AstOp opCode $ map (substitute1Ast i var) args
  AstSumOfList args -> AstSumOfList $ map (substitute1Ast i var) args
  AstIota -> v1
  AstIndexZ v is ->
    AstIndexZ (substitute1Ast i var v) (fmap (substitute1AstInt i var) is)
  AstSum v -> AstSum (substitute1Ast i var v)
  AstScatter sh v (vars, ix) ->
    if elem var vars
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
    if elem var vars
    then AstGatherZ sh (substitute1Ast i var v) (vars, ix)
    else AstGatherZ sh (substitute1Ast i var v)
                       (vars, fmap (substitute1AstInt i var) ix)
  AstConst _a -> v1
  AstConstant (AstPrimalPart a) ->
    AstConstant (AstPrimalPart $ substitute1Ast i var a)
  AstD (AstPrimalPart u) (AstDualPart u') ->
    AstD (AstPrimalPart $ substitute1Ast i var u)
         (AstDualPart $ substitute1Ast i var u')
  AstLetDomains vars l v ->
    if elem var vars
    then AstLetDomains vars (substitute1AstDomains i var l) v
    else AstLetDomains vars (substitute1AstDomains i var l)
                            (substitute1Ast i var v)

substitute1AstDynamic
  :: (ShowAst r, KnownNat m)
  => Either (Ast m r) (AstInt r) -> AstVarId -> AstDynamic r
  -> AstDynamic r
substitute1AstDynamic i var (AstDynamic t) = AstDynamic $ substitute1Ast i var t

substitute1AstDomains
  :: (ShowAst r, KnownNat m)
  => Either (Ast m r) (AstInt r) -> AstVarId -> AstDomains r
  -> AstDomains r
substitute1AstDomains i var v1 = case v1 of
  AstDomains l -> AstDomains $ V.map (substitute1AstDynamic i var) l
  AstDomainsLet var2 u v ->
    if var == var2
    then AstDomainsLet var2 (substitute1Ast i var u) v
    else AstDomainsLet var2 (substitute1Ast i var u)
                            (substitute1AstDomains i var v)

substitute1AstInt :: forall m r. (ShowAst r, KnownNat m)
                  => Either (Ast m r) (AstInt r) -> AstVarId -> AstInt r
                  -> AstInt r
substitute1AstInt i var i2 = case i2 of
  AstIntVar var2 -> if var == var2
                    then fromRight (error "substitute1AstInt: Var") i
                    else i2
  AstIntOp opCodeInt args ->
    AstIntOp opCodeInt $ map (substitute1AstInt i var) args
  AstIntConst _a -> i2
  AstIntFloor (AstPrimalPart v) ->
    AstIntFloor $ AstPrimalPart $ substitute1Ast i var v
  AstIntCond b a1 a2 ->
    AstIntCond (substitute1AstBool i var b)
               (substitute1AstInt i var a1) (substitute1AstInt i var a2)
  AstMinIndex1 (AstPrimalPart v) ->
    AstMinIndex1 $ AstPrimalPart $ substitute1Ast i var v
  AstMaxIndex1 (AstPrimalPart v) ->
    AstMaxIndex1 $ AstPrimalPart $ substitute1Ast i var v

substitute1AstBool :: forall m r. (ShowAst r, KnownNat m)
                   => Either (Ast m r) (AstInt r) -> AstVarId -> AstBool r
                   -> AstBool r
substitute1AstBool i var b1 = case b1 of
  AstBoolOp opCodeBool args ->
    AstBoolOp opCodeBool $ map (substitute1AstBool i var) args
  AstBoolConst _a -> b1
  AstRel opCodeRel args ->
    AstRel opCodeRel
    $ map (AstPrimalPart . substitute1Ast i var . unAstPrimalPart) args
  AstRelInt opCodeRel args ->
    AstRelInt opCodeRel $ map (substitute1AstInt i var) args


-- * Pretty-printing

-- Modeled after https://github.com/VMatthijs/CHAD/blob/755fc47e1f8d1c3d91455f123338f44a353fc265/src/TargetLanguage.hs#L335.

printAstVarId :: String -> AstVarId -> ShowS
printAstVarId prefix var =
  showString $ prefix ++ show (fromEnum var - 100000000)

printAstVar :: AstVarId -> ShowS
printAstVar = printAstVarId "x"

printAstIntVar :: AstVarId -> ShowS
printAstIntVar = printAstVarId "i"

printAstSimple :: ShowAst r => Ast n r -> String
printAstSimple t = printAst False 0 t ""

printAstDebug :: ShowAst r => Ast n r -> String
printAstDebug t = printAst True 0 t ""

-- Precedences used are as in Haskell.
--
-- If @global@ is off, typing this in should result
-- in a program with the same semantics (though GHC may require
-- some extra type applications), but no global sharing.
-- If @global@ is on, this won't parse.
printAst :: ShowAst r => Bool -> Int -> Ast n r -> ShowS
printAst global d = \case
  AstVar _sh var -> printAstVar var
  AstLet var u v ->
    showParen (d > 10)
    $ showString "tlet "
      . printAst global 11 u
      . showString " "
      . (showParen True
         $ showString "\\"
           . printAstVar var
           . showString " -> "
           . printAst global 0 v)
  AstLetGlobal n v ->
    if global
    then printPrefixOp printAst global d
                       ("tletR<" ++ show (fromEnum n - 100000000) ++ ">") [v]
           -- this won't parse anyway, so we don't add parens
    else printAst global d v
  AstOp opCode args -> printAstOp global d opCode args
  AstSumOfList [] -> error "printAst: empty AstSumOfList"
  AstSumOfList (left : args) ->
    let rs = map (\arg -> showString " + " . printAst global 7 arg) args
    in showParen (d > 6)
       $ printAst global 7 left
         . foldr (.) id rs
  AstIota -> showString "tiota"  -- TODO: no surface syntax, so no roundtrip
  AstIndexZ AstIota (i :. ZI) ->
    printPrefixOp printAstInt global d "tfromIndex0" [i]
  AstIndexZ v ix ->
    showParen (d > 9)
    $ printAst global 10 v
      . showString " ! "
      . showListWith (printAstInt global 0) (indexToList ix)
  AstSum v -> printPrefixOp printAst global d "tsum" [v]
  AstScatter sh v (vars, ix) ->
    showParen (d > 10)
    $ showString ("tscatter " ++ show sh ++ " ")
      . printAst global 11 v
      . showString " "
      . (showParen True
         $ showString "\\"
           . showListWith printAstIntVar (sizedListToList vars)
           . showString " -> "
           . showListWith (printAstInt global 0) (indexToList ix))
  AstFromList l ->
    showParen (d > 10)
    $ showString "tfromList "
      . showListWith (printAst global 0) l
  AstFromVector l ->
    showParen (d > 10)
    $ showString "tfromVector "
      . (showParen True
         $ showString "fromList "
           . showListWith (printAst global 0) (V.toList l))
  AstKonst k v -> printPrefixOp printAst global d ("tkonst " ++ show k) [v]
  AstAppend x y -> printPrefixOp printAst global d "tappend" [x, y]
  AstSlice i k v -> printPrefixOp printAst global d
                                  ("tslice " ++ show i ++ " " ++ show k) [v]
  AstReverse v -> printPrefixOp printAst global d "treverse" [v]
  AstTranspose perm v ->
    printPrefixOp printAst global d ("ttranspose " ++ show perm) [v]
  AstReshape sh v ->
    printPrefixOp printAst global d ("treshape " ++ show sh) [v]
  AstBuild1 k (var, v) ->
    showParen (d > 10)
    $ showString "tbuild1 "
      . shows k
      . showString " "
      . (showParen True
         $ showString "\\"
           . printAstVar var
           . showString " -> "
           . printAst global 0 v)
  AstGatherZ sh v (vars, ix) ->
    showParen (d > 10)
    $ showString ("tgather " ++ show sh ++ " ")
      . printAst global 11 v
      . showString " "
      . (showParen True
         $ showString "\\"
           . showListWith printAstIntVar (sizedListToList vars)
           . showString " -> "
           . showListWith (printAstInt global 0) (indexToList ix))
  AstConst a ->
    showParen (d > 10)
    $ showString "tconst "
      . if null (OR.shapeL a)
        then shows $ head $ OR.toList a
        else showParen True
             $ shows a
  AstConstant (AstPrimalPart (AstConst a)) -> printAst global d (AstConst a)
  AstConstant (AstPrimalPart a) ->
    printPrefixOp printAst global d "tconstant" [a]
  AstD (AstPrimalPart u) (AstDualPart u') ->
    printPrefixOp printAst global d "tD" [u, u']
  AstLetDomains vars l v ->
    showParen (d > 10)
    $ showString "tletDomains "
      . printAstDomains global 11 l
      . showString " "
      . (showParen True
         $ showString "\\"
           . showListWith printAstVar (V.toList vars)
           . showString " -> "
           . printAst global 0 v)
      -- TODO: this does not roundtrip yet

-- Differs from standard only in the space after comma.
showListWith :: (a -> ShowS) -> [a] -> ShowS
showListWith _     []     s = "[]" ++ s
showListWith showx (x:xs) s = '[' : showx x (showl xs)
 where
  showl []     = ']' : s
  showl (y:ys) = ", " ++ showx y (showl ys)

printAstDynamic :: ShowAst r => Bool -> Int -> AstDynamic r -> ShowS
printAstDynamic global d (AstDynamic v) =
  printPrefixOp printAst global d "dfromR" [v]

printAstDomainsSimple :: ShowAst r => AstDomains r -> String
printAstDomainsSimple t = printAstDomains False 0 t ""

printAstDomainsDebug :: ShowAst r => AstDomains r -> String
printAstDomainsDebug t = printAstDomains True 0 t ""

printAstDomains :: ShowAst r
                => Bool -> Int -> AstDomains r -> ShowS
printAstDomains global d = \case
  AstDomains l ->
    showParen (d > 10)
    $ showString "dmkDomains "
      . (showParen True
         $ showString "fromList "
           . showListWith (printAstDynamic global 0) (V.toList l))
  AstDomainsLet var u v ->
    showParen (d > 10)
    $ showString "dlet "
      . printAst global 11 u
      . showString " "
      . (showParen True
         $ showString "\\"
           . printAstVar var
           . showString " -> "
           . printAstDomains global 0 v)

printAstInt :: ShowAst r => Bool -> Int -> AstInt r -> ShowS
printAstInt global d = \case
  AstIntVar var -> printAstIntVar var
  AstIntOp opCode args -> printAstIntOp global d opCode args
  AstIntConst a -> shows a
  AstIntFloor (AstPrimalPart v) -> printPrefixOp printAst global d "floor" [v]
  AstIntCond b a1 a2 ->
    showParen (d > 10)
    $ showString "ifB "
      . printAstBool global 11 b
      . showString " "
      . printAstInt global 11 a1
      . showString " "
      . printAstInt global 11 a2
  AstMinIndex1 (AstPrimalPart v) ->
    printPrefixOp printAst global d "tminIndex0" [v]
  AstMaxIndex1 (AstPrimalPart v) ->
    printPrefixOp printAst global d "tmaxIndex0" [v]

printAstBool :: ShowAst r => Bool -> Int -> AstBool r -> ShowS
printAstBool global d = \case
  AstBoolOp opCode args -> printAstBoolOp global d opCode args
  AstBoolConst a -> shows a
  AstRel opCode args -> printAstRelOp printAst global d opCode
                        $ map unAstPrimalPart args
  AstRelInt opCode args -> printAstRelOp printAstInt global d opCode args

printAstOp :: ShowAst r => Bool -> Int -> OpCode -> [Ast n r] -> ShowS
printAstOp global d opCode args = case (opCode, args) of
  (MinusOp, [u, v]) -> printBinaryOp printAst global d u (6, " - ") v
  (TimesOp, [u, v]) -> printBinaryOp printAst global d u (7, " * ") v
  (NegateOp, [u]) -> printPrefixOp printAst global d "negate" [u]
  (AbsOp, [u]) -> printPrefixOp printAst global d "abs" [u]
  (SignumOp, [u]) -> printPrefixOp printAst global d "signum" [u]
  (DivideOp, [u, v]) -> printBinaryOp printAst global d u (7, " / ") v
  (RecipOp, [u]) -> printPrefixOp printAst global d "recip" [u]
  (ExpOp, [u]) -> printPrefixOp printAst global d "exp" [u]
  (LogOp, [u]) -> printPrefixOp printAst global d "log" [u]
  (SqrtOp, [u]) -> printPrefixOp printAst global d "sqrt" [u]
  (PowerOp, [u, v]) -> printBinaryOp printAst global d u (8, " ** ") v
  (LogBaseOp, [u, v]) -> printPrefixOp printAst global d "logBase" [u, v]
  (SinOp, [u]) -> printPrefixOp printAst global d "sin" [u]
  (CosOp, [u]) -> printPrefixOp printAst global d "cos" [u]
  (TanOp, [u]) -> printPrefixOp printAst global d "tan" [u]
  (AsinOp, [u]) -> printPrefixOp printAst global d "asin" [u]
  (AcosOp, [u]) -> printPrefixOp printAst global d "acos" [u]
  (AtanOp, [u]) -> printPrefixOp printAst global d "atan" [u]
  (SinhOp, [u]) -> printPrefixOp printAst global d "sinh" [u]
  (CoshOp, [u]) -> printPrefixOp printAst global d "cosh" [u]
  (TanhOp, [u]) -> printPrefixOp printAst global d "tanh" [u]
  (AsinhOp, [u]) -> printPrefixOp printAst global d "asinh" [u]
  (AcoshOp, [u]) -> printPrefixOp printAst global d "acosh" [u]
  (AtanhOp, [u]) -> printPrefixOp printAst global d "atanh" [u]
  (Atan2Op, [u, v]) -> printPrefixOp printAst global d "atan2" [u, v]
  (MaxOp, [u, v]) -> printPrefixOp printAst global d "max" [u, v]
  (MinOp, [u, v]) -> printPrefixOp printAst global d "min" [u, v]
  _ -> error $ "printAstOp: wrong number of arguments"
               ++ show (opCode, length args)

printPrefixOp :: (Bool -> Int -> a -> ShowS)
              -> Bool -> Int -> String -> [a]
              -> ShowS
{-# INLINE printPrefixOp #-}
printPrefixOp pr global d funcname args =
  let rs = map (\arg -> showString " " . pr global 11 arg) args
  in showParen (d > 10)
     $ showString funcname
       . foldr (.) id rs

printBinaryOp :: (Bool -> Int -> a -> ShowS)
              -> Bool -> Int -> a -> (Int, String) -> a
              -> ShowS
{-# INLINE printBinaryOp #-}
printBinaryOp pr global d left (prec, opstr) right =
  showParen (d > prec)
  $ pr global (prec + 1) left
    . showString opstr
    . pr global (prec + 1) right

printAstIntOp :: ShowAst r => Bool -> Int -> OpCodeInt -> [AstInt r] -> ShowS
printAstIntOp global d opCode args = case (opCode, args) of
  (PlusIntOp, [u, v]) -> printBinaryOp printAstInt global d u (6, " + ") v
  (MinusIntOp, [u, v]) -> printBinaryOp printAstInt global d u (6, " - ") v
  (TimesIntOp, [u, v]) -> printBinaryOp printAstInt global d u (7, " * ") v
  (NegateIntOp, [u]) -> printPrefixOp printAstInt global d "negate" [u]
  (AbsIntOp, [u]) -> printPrefixOp printAstInt global d "abs" [u]
  (SignumIntOp, [u]) -> printPrefixOp printAstInt global d "signum" [u]
  (MaxIntOp, [u, v]) -> printPrefixOp printAstInt global d "max" [u, v]
  (MinIntOp, [u, v]) -> printPrefixOp printAstInt global d "min" [u, v]
  (QuotIntOp, [u, v]) -> printPrefixOp printAstInt global d "quot" [u, v]
  (RemIntOp, [u, v]) -> printPrefixOp printAstInt global d "rem" [u, v]
  _ -> error $ "printAstIntOp: wrong number of arguments"
               ++ show (opCode, length args)

printAstBoolOp
  :: ShowAst r => Bool -> Int -> OpCodeBool -> [AstBool r] -> ShowS
printAstBoolOp global d opCode args = case (opCode, args) of
  (NotOp, [u]) -> printPrefixOp printAstBool global d "not" [u]
  (AndOp, [u, v]) -> printBinaryOp printAstBool global d u (3, " && ") v
  (OrOp, [u, v]) -> printBinaryOp printAstBool global d u (2, " || ") v
  _ -> error $ "printAstBoolOp: wrong number of arguments"
               ++ show (opCode, length args)

printAstRelOp :: (Bool -> Int -> a -> ShowS)
              -> Bool -> Int -> OpCodeRel -> [a]
              -> ShowS
{-# INLINE printAstRelOp #-}
printAstRelOp pr global d opCode args = case (opCode, args) of
  (EqOp, [u, v]) -> printBinaryOp pr global d u (4, " ==* ") v
  (NeqOp, [u, v]) -> printBinaryOp pr global d u (4, " /=* ") v
  (LeqOp, [u, v]) -> printBinaryOp pr global d u (4, " <=* ") v
  (GeqOp, [u, v]) -> printBinaryOp pr global d u (4, " >=* ") v
  (LsOp, [u, v]) -> printBinaryOp pr global d u (4, " <* ") v
  (GtOp, [u, v]) -> printBinaryOp pr global d u (4, " >* ") v
  _ -> error $ "printAstRelOp: wrong number of arguments"
               ++ show (opCode, length args)
