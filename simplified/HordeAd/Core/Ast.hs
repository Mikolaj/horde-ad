{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | AST of the code to be differentiated. It's needed mostly for handling
-- higher order operations such as build and map and for producing reusable
-- gradients, but can be used for arbitrary code transformations
-- at the cost of limiting expressiveness of transformed fragments
-- to what AST captures.
module HordeAd.Core.Ast
  ( AstVarId, intToAstVarId
  , ADAstVarNames, ADAstArtifact6, ShowAst, AstIndex, AstVarList
  , AstRanked(..), AstNoVectorize(..), AstNoSimplify(..)
  , AstPrimalPart(..), AstDualPart(..), AstShaped(..)
  , AstDynamic(..), AstDomains(..)
  , unwrapAstDomains, bindsToLet, bindsToDomainsLet
  , AstVarName(..), AstDynamicVarName(..), AstInt(..), AstBool(..)
  , OpCode(..), OpCodeInt(..), OpCodeBool(..), OpCodeRel(..)
  , astCond  -- exposed only for tests
  , ADShare
  , emptyADShare, insertADShare, mergeADShare, subtractADShare
  , flattenADShare, assocsADShare
  ) where

import Prelude

import qualified Data.Array.RankedS as OR
import           Data.Boolean
import           Data.IORef.Unboxed (Counter, atomicAddCounter_, newCounter)
import           Data.Kind (Type)
import           Data.List (foldl')
import           Data.Maybe (fromMaybe)
import qualified Data.Strict.Vector as Data.Vector
import           GHC.TypeLits (KnownNat, Nat, type (+))
import           Numeric.LinearAlgebra (Numeric)
import           System.IO.Unsafe (unsafePerformIO)

import HordeAd.Core.SizedIndex
import HordeAd.Internal.SizedList

-- * Ast definitions

-- We avoid adding a phantom type denoting the underlying scalar,
-- because the type families over tensor ranks make quanitified constraints
-- impossible and so the phantom type leads to passing explicit (and implicit)
-- type equality proofs around.
newtype AstVarId = AstVarId Int
 deriving (Eq, Ord, Show, Enum)

intToAstVarId :: Int -> AstVarId
intToAstVarId = AstVarId

type ADAstVarNames n r = (AstVarName (OR.Array n r), [AstDynamicVarName r])

-- The artifact from step 6) of our full pipeline.
type ADAstArtifact6 n r = (ADAstVarNames n r, AstDomains r, AstRanked r n)

type ShowAst r = (Show r, Numeric r)

type AstIndex n r = Index n (AstInt r)

type AstVarList n = SizedList n AstVarId

-- We use here @ShapeInt@ for simplicity. @Shape n (AstInt r)@ gives
-- more expressiveness, but leads to irregular tensors,
-- especially after vectorization, and prevents statically known shapes.

-- | AST for a tensor of rank n and elements r that is meant
-- to be differentiated.
data AstRanked :: Type -> Nat -> Type where
  -- To permit defining objective functions in Ast, not just constants:
  AstVar :: ShapeInt n -> AstVarId -> AstRanked r n
  AstLet :: (KnownNat n, KnownNat m)
         => AstVarId -> AstRanked r n -> AstRanked r m -> AstRanked r m
  AstLetADShare :: ADShare r -> AstRanked r m -> AstRanked r m
   -- there are mixed local/global lets, because they can be identical
   -- to the lets stored in the D constructor and so should not be inlined
   -- even in trivial cases until the transpose pass eliminates D

  -- For the numeric classes:
  AstOp :: OpCode -> [AstRanked r n] -> AstRanked r n
  AstSumOfList :: [AstRanked r n] -> AstRanked r n
  AstIota :: AstRanked r 1
    -- needed, because toInteger and so fromIntegral is not defined for Ast

  -- For the Tensor class:
  AstIndexZ :: forall m n r. KnownNat m
            => AstRanked r (m + n) -> AstIndex m r -> AstRanked r n
    -- first ix is for outermost dimension; empty index means identity,
    -- if index is out of bounds, the result is defined and is 0,
    -- but vectorization is permitted to change the value
  AstSum :: AstRanked r (1 + n) -> AstRanked r n
  AstScatter :: forall m n p r. (KnownNat m, KnownNat n, KnownNat p)
             => ShapeInt (p + n) -> AstRanked r (m + n)
             -> (AstVarList m, AstIndex p r)
             -> AstRanked r (p + n)

  AstFromList :: KnownNat n
              => [AstRanked r n] -> AstRanked r (1 + n)
  AstFromVector :: KnownNat n
                => Data.Vector.Vector (AstRanked r n) -> AstRanked r (1 + n)
  AstReplicate :: KnownNat n
           => Int -> AstRanked r n -> AstRanked r (1 + n)
  AstAppend :: KnownNat n
            => AstRanked r (1 + n) -> AstRanked r (1 + n) -> AstRanked r (1 + n)
  AstSlice :: KnownNat n
           => Int -> Int -> AstRanked r (1 + n) -> AstRanked r (1 + n)
  AstReverse :: KnownNat n
             => AstRanked r (1 + n) -> AstRanked r (1 + n)
  AstTranspose :: Permutation -> AstRanked r n -> AstRanked r n
  AstReshape :: KnownNat n
             => ShapeInt m -> AstRanked r n -> AstRanked r m
  AstBuild1 :: KnownNat n
            => Int -> (AstVarId, AstRanked r n) -> AstRanked r (1 + n)
  AstGatherZ :: forall m n p r. (KnownNat m, KnownNat n, KnownNat p)
             => ShapeInt (m + n) -> AstRanked r (p + n)
             -> (AstVarList m, AstIndex p r)
             -> AstRanked r (m + n)
    -- out of bounds indexing is permitted

  -- For the forbidden half of the Tensor class:
  AstConst :: OR.Array n r -> AstRanked r n
  AstConstant :: AstPrimalPart r n -> AstRanked r n
  AstD :: AstPrimalPart r n -> AstDualPart r n -> AstRanked r n
  AstLetDomains :: Data.Vector.Vector AstVarId -> AstDomains r -> AstRanked r m
                -> AstRanked r m
deriving instance ShowAst r => Show (AstRanked r n)

newtype AstNoVectorize r n = AstNoVectorize {unAstNoVectorize :: AstRanked r n}
deriving instance ShowAst r => Show (AstNoVectorize r n)

newtype AstNoSimplify r n = AstNoSimplify {unAstNoSimplify :: AstRanked r n}
deriving instance ShowAst r => Show (AstNoSimplify r n)

newtype AstPrimalPart r n = AstPrimalPart {unAstPrimalPart :: AstRanked r n}
deriving instance ShowAst r => Show (AstPrimalPart r n)

newtype AstDualPart r n = AstDualPart {unAstDualPart :: AstRanked r n}
deriving instance ShowAst r => Show (AstDualPart r n)

data AstShaped r (sh :: [Nat])  -- TODO

data AstDynamic :: Type -> Type where
  AstDynamic :: KnownNat n
             => AstRanked r n -> AstDynamic r
deriving instance ShowAst r => Show (AstDynamic r)

data AstDomains :: Type -> Type where
  AstDomains :: Data.Vector.Vector (AstDynamic r) -> AstDomains r
  AstDomainsLet :: KnownNat n
                => AstVarId -> AstRanked r n -> AstDomains r -> AstDomains r
deriving instance ShowAst r => Show (AstDomains r)

unwrapAstDomains :: AstDomains r -> Data.Vector.Vector (AstDynamic r)
unwrapAstDomains = \case
  AstDomains l -> l
  AstDomainsLet _ _ v -> unwrapAstDomains v

bindsToLet :: KnownNat n => AstRanked r n -> [(AstVarId, AstDynamic r)] -> AstRanked r n
{-# INLINE bindsToLet #-}  -- help list fusion
bindsToLet = foldl' bindToLet
 where
  bindToLet u (var, AstDynamic w) = AstLet var w u

bindsToDomainsLet :: AstDomains r -> [(AstVarId, AstDynamic r)] -> AstDomains r
{-# INLINE bindsToDomainsLet #-}   -- help list fusion
bindsToDomainsLet = foldl' bindToDomainsLet
 where
  bindToDomainsLet u (var, AstDynamic w) = AstDomainsLet var w u

newtype AstVarName t = AstVarName AstVarId
 deriving (Eq, Show)

data AstDynamicVarName :: Type -> Type where
  AstDynamicVarName :: KnownNat n
                    => AstVarName (OR.Array n r) -> AstDynamicVarName r
deriving instance ShowAst r => Show (AstDynamicVarName r)

-- The argument is the underlying scalar.
data AstInt :: Type -> Type where
  AstIntVar :: AstVarId -> AstInt r
  AstIntOp :: OpCodeInt -> [AstInt r] -> AstInt r
  AstIntConst :: Int -> AstInt r
  AstIntFloor :: AstPrimalPart r 0 -> AstInt r
  AstIntCond :: AstBool r -> AstInt r -> AstInt r -> AstInt r
  AstMinIndex1 :: AstPrimalPart r 1 -> AstInt r
  AstMaxIndex1 :: AstPrimalPart r 1 -> AstInt r
deriving instance ShowAst r => Show (AstInt r)

data AstBool :: Type -> Type where
  AstBoolOp :: OpCodeBool -> [AstBool r] -> AstBool r
  AstBoolConst :: Bool -> AstBool r
  AstRel :: KnownNat n
         => OpCodeRel -> [AstPrimalPart r n] -> AstBool r
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

type instance BooleanOf (AstRanked r n) = AstBool r

instance KnownNat n => IfB (AstRanked r n) where
  ifB = astCond

-- No simplification yet done at this point, so constant boolean unlikely,
-- but it's a constant time simplification, so no harm done.
astCond :: KnownNat n
        => AstBool r -> AstRanked r n -> AstRanked r n -> AstRanked r n
astCond (AstBoolConst b) v w = if b then v else w
astCond b (AstConstant (AstPrimalPart v)) (AstConstant (AstPrimalPart w)) =
  AstConstant $ AstPrimalPart $ AstIndexZ (AstFromList [v, w])
                                          (singletonIndex $ AstIntCond b 0 1)
astCond b v w = AstIndexZ (AstFromList [v, w])
                          (singletonIndex $ AstIntCond b 0 1)

instance KnownNat n => EqB (AstRanked r n) where
  v ==* u = AstRel EqOp [AstPrimalPart v, AstPrimalPart u]
  v /=* u = AstRel NeqOp [AstPrimalPart v, AstPrimalPart u]

instance KnownNat n => OrdB (AstRanked r n) where
  v <* u = AstRel LsOp [AstPrimalPart v, AstPrimalPart u]
  v <=* u = AstRel LeqOp [AstPrimalPart v, AstPrimalPart u]
  v >* u = AstRel GtOp [AstPrimalPart v, AstPrimalPart u]
  v >=* u = AstRel GeqOp [AstPrimalPart v, AstPrimalPart u]

type instance BooleanOf (AstNoVectorize r n) = AstBool r

instance KnownNat n => IfB (AstNoVectorize r n) where
  ifB b v w = AstNoVectorize $ astCond b (unAstNoVectorize v)
                                         (unAstNoVectorize w)

instance KnownNat n => EqB (AstNoVectorize r n) where
  v ==* u = AstRel EqOp [ AstPrimalPart $ unAstNoVectorize v
                        , AstPrimalPart $ unAstNoVectorize u ]
  v /=* u = AstRel NeqOp [ AstPrimalPart $ unAstNoVectorize v
                         , AstPrimalPart $ unAstNoVectorize u ]

instance KnownNat n => OrdB (AstNoVectorize r n) where
  v <* u = AstRel LsOp [ AstPrimalPart $ unAstNoVectorize v
                       , AstPrimalPart $ unAstNoVectorize u ]
  v <=* u = AstRel LeqOp [ AstPrimalPart $ unAstNoVectorize v
                         , AstPrimalPart $ unAstNoVectorize u ]
  v >* u = AstRel GtOp [ AstPrimalPart $ unAstNoVectorize v
                       , AstPrimalPart $ unAstNoVectorize u ]
  v >=* u = AstRel GeqOp [ AstPrimalPart $ unAstNoVectorize v
                         , AstPrimalPart $ unAstNoVectorize u ]

type instance BooleanOf (AstNoSimplify r n) = AstBool r

instance KnownNat n => IfB (AstNoSimplify r n) where
  ifB b v w = AstNoSimplify $ astCond b (unAstNoSimplify v)
                                         (unAstNoSimplify w)

instance KnownNat n => EqB (AstNoSimplify r n) where
  v ==* u = AstRel EqOp [ AstPrimalPart $ unAstNoSimplify v
                        , AstPrimalPart $ unAstNoSimplify u ]
  v /=* u = AstRel NeqOp [ AstPrimalPart $ unAstNoSimplify v
                         , AstPrimalPart $ unAstNoSimplify u ]

instance KnownNat n => OrdB (AstNoSimplify r n) where
  v <* u = AstRel LsOp [ AstPrimalPart $ unAstNoSimplify v
                       , AstPrimalPart $ unAstNoSimplify u ]
  v <=* u = AstRel LeqOp [ AstPrimalPart $ unAstNoSimplify v
                         , AstPrimalPart $ unAstNoSimplify u ]
  v >* u = AstRel GtOp [ AstPrimalPart $ unAstNoSimplify v
                       , AstPrimalPart $ unAstNoSimplify u ]
  v >=* u = AstRel GeqOp [ AstPrimalPart $ unAstNoSimplify v
                         , AstPrimalPart $ unAstNoSimplify u ]

type instance BooleanOf (AstPrimalPart r n) = AstBool r

instance KnownNat n => IfB (AstPrimalPart r n) where
  ifB b v w = AstPrimalPart $ astCond b (unAstPrimalPart v) (unAstPrimalPart w)

instance KnownNat n => EqB (AstPrimalPart r n) where
  v ==* u = AstRel EqOp [v, u]
  v /=* u = AstRel NeqOp [v, u]

instance KnownNat n => OrdB (AstPrimalPart r n) where
  v <* u = AstRel LsOp [v, u]
  v <=* u = AstRel LeqOp [v, u]
  v >* u = AstRel GtOp [v, u]
  v >=* u = AstRel GeqOp [v, u]

type instance BooleanOf (AstInt r) = AstBool r

instance IfB (AstInt r) where
  ifB (AstBoolConst b) v w = if b then v else w  -- common in indexing
  ifB b v w = AstIntCond b v w

instance EqB (AstInt r) where
  v ==* u = AstRelInt EqOp [v, u]
  v /=* u = AstRelInt NeqOp [v, u]

instance OrdB (AstInt r) where
  AstIntConst u <* AstIntConst v = AstBoolConst $ u < v  -- common in indexing
  v <* u = AstRelInt LsOp [v, u]
  AstIntConst u <=* AstIntConst v = AstBoolConst $ u <= v  -- common in indexing
  v <=* u = AstRelInt LeqOp [v, u]
  AstIntConst u >* AstIntConst v = AstBoolConst $ u > v  -- common in indexing
  v >* u = AstRelInt GtOp [v, u]
  AstIntConst u >=* AstIntConst v = AstBoolConst $ u >= v  -- common in indexing
  v >=* u = AstRelInt GeqOp [v, u]


-- * Unlawful numeric instances of AST types; they are lawful modulo evaluation

-- See the comment about @Eq@ and @Ord@ in "DualNumber".
instance Eq (AstRanked r n) where
  _ == _ = error "Ast: can't evaluate terms for Eq"

instance Ord (OR.Array n r) => Ord (AstRanked r n) where
  max u v = AstOp MaxOp [u, v]
  min u v = AstOp MinOp [u, v]
  -- Unfortunately, the others can't be made to return @AstBool@.
  _ <= _ = error "Ast: can't evaluate terms for Ord"

instance Num (OR.Array n r) => Num (AstRanked r n) where
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

instance Real (OR.Array n r) => Real (AstRanked r n) where
  toRational = undefined
    -- very low priority, since these are all extremely not continuous

instance Fractional (OR.Array n r) => Fractional (AstRanked r n) where
  u / v = AstOp DivideOp  [u, v]
  recip v = AstOp RecipOp [v]
  fromRational = AstConstant . AstPrimalPart . AstConst . fromRational

instance (Floating (OR.Array n r)) => Floating (AstRanked r n) where
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

instance RealFrac (OR.Array n r) => RealFrac (AstRanked r n) where
  properFraction = undefined
    -- The integral type doesn't have a Storable constraint,
    -- so we can't implement this (nor RealFracB from Boolean package).

instance RealFloat (OR.Array n r) => RealFloat (AstRanked r n) where
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

instance Eq (AstNoVectorize r n) where
  _ == _ = error "AstNoVectorize: can't evaluate terms for Eq"

instance Ord (AstRanked r n) => Ord (AstNoVectorize r n) where
  max (AstNoVectorize u) (AstNoVectorize v) =
    AstNoVectorize (AstOp MaxOp [u, v])
  min (AstNoVectorize u) (AstNoVectorize v) =
    AstNoVectorize (AstOp MinOp [u, v])
  _ <= _ = error "AstNoVectorize: can't evaluate terms for Ord"

deriving instance Num (AstRanked r n) => Num (AstNoVectorize r n)
deriving instance Real (AstRanked r n) => Real (AstNoVectorize r n)
deriving instance Fractional (AstRanked r n) => Fractional (AstNoVectorize r n)
deriving instance Floating (AstRanked r n) => Floating (AstNoVectorize r n)
deriving instance RealFrac (AstRanked r n) => RealFrac (AstNoVectorize r n)
deriving instance RealFloat (AstRanked r n) => RealFloat (AstNoVectorize r n)

instance Eq (AstNoSimplify r n) where
  _ == _ = error "AstNoSimplify: can't evaluate terms for Eq"

instance Ord (AstRanked r n) => Ord (AstNoSimplify r n) where
  max (AstNoSimplify u) (AstNoSimplify v) =
    AstNoSimplify (AstOp MaxOp [u, v])
  min (AstNoSimplify u) (AstNoSimplify v) =
    AstNoSimplify (AstOp MinOp [u, v])
  _ <= _ = error "AstNoSimplify: can't evaluate terms for Ord"

deriving instance Num (AstRanked r n) => Num (AstNoSimplify r n)
deriving instance Real (AstRanked r n) => Real (AstNoSimplify r n)
deriving instance Fractional (AstRanked r n) => Fractional (AstNoSimplify r n)
deriving instance Floating (AstRanked r n) => Floating (AstNoSimplify r n)
deriving instance RealFrac (AstRanked r n) => RealFrac (AstNoSimplify r n)
deriving instance RealFloat (AstRanked r n) => RealFloat (AstNoSimplify r n)

instance Eq (AstPrimalPart r n) where
  _ == _ = error "AstPrimalPart: can't evaluate terms for Eq"

instance Ord (AstRanked r n) => Ord (AstPrimalPart r n) where
  max (AstPrimalPart u) (AstPrimalPart v) =
    AstPrimalPart (AstOp MaxOp [u, v])
  min (AstPrimalPart u) (AstPrimalPart v) =
    AstPrimalPart (AstOp MinOp [u, v])
  _ <= _ = error "AstPrimalPart: can't evaluate terms for Ord"

deriving instance Num (AstRanked r n) => Num (AstPrimalPart r n)
deriving instance Real (AstRanked r n) => Real (AstPrimalPart r n)
deriving instance Fractional (AstRanked r n) => Fractional (AstPrimalPart r n)
deriving instance Floating (AstRanked r n) => Floating (AstPrimalPart r n)
deriving instance RealFrac (AstRanked r n) => RealFrac (AstPrimalPart r n)
deriving instance RealFloat (AstRanked r n) => RealFloat (AstPrimalPart r n)

instance Eq (AstInt r) where
  _ == _ = error "AstInt: can't evaluate terms for Eq"

instance Ord (AstInt r) where
  max u v = AstIntOp MaxIntOp [u, v]
  min u v = AstIntOp MinIntOp [u, v]
  _ <= _ = error "AstInt: can't evaluate terms for Ord"

instance Num (AstInt r) where
  AstIntConst u + AstIntConst v = AstIntConst $ u + v  -- common in indexing
  u + v = AstIntOp PlusIntOp [u, v]  -- simplification relies on binary form
  AstIntConst u - AstIntConst v = AstIntConst $ u - v  -- common in indexing
  u - v = AstIntOp MinusIntOp [u, v]
  AstIntConst u * AstIntConst v = AstIntConst $ u * v  -- common in indexing
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
  AstBoolConst b &&* AstBoolConst c = AstBoolConst $ b && c
                                        -- common in indexing
  b &&* c = AstBoolOp AndOp [b, c]
  b ||* c = AstBoolOp OrOp [b, c]


-- * ADShare definition

unsafeGlobalCounter :: Counter
{-# NOINLINE unsafeGlobalCounter #-}
unsafeGlobalCounter = unsafePerformIO (newCounter 0)

unsafeGetFreshId :: IO Int
{-# INLINE unsafeGetFreshId #-}
unsafeGetFreshId = atomicAddCounter_ unsafeGlobalCounter 1

-- Data invariant: the list is reverse-sorted wrt keys.
-- This permits not inspecting too long a prefix of the list, usually,
-- which is crucial for performance. The strictness is crucial for correctness
-- in the presence of impurity for generating fresh variables.
-- The first integer field permits something akin to pointer equality
-- but with less false negatives, because it's stable.
data ADShare r = ADShareNil
               | ADShareCons Int AstVarId (AstDynamic r) (ADShare r)
deriving instance ShowAst r => Show (ADShare r)

emptyADShare :: ADShare r
emptyADShare = ADShareNil

insertADShare :: forall r. AstVarId -> AstDynamic r -> ADShare r -> ADShare r
insertADShare !key !t !s =
  -- The Maybe over-engineering ensures that we never refresh an id
  -- unnecessarily. In theory, when merging alternating equal lists
  -- with different ids, this improves runtime from quadratic to linear,
  -- but we apparently don't have such tests or they are too small,
  -- so this causes a couple percent overhead instead.
  let insertAD :: ADShare r -> Maybe (ADShare r)
      insertAD ADShareNil = Just $ ADShareCons (- fromEnum key) key t ADShareNil
      insertAD l2@(ADShareCons _id2 key2 t2 rest2) =
        case compare key key2 of
          EQ -> Nothing
                  -- the lists only ever grow and only in fresh/unique way,
                  -- so identical key means identical payload
          LT -> case insertAD rest2 of
            Nothing -> Nothing
            Just l3 -> Just $ freshInsertADShare key2 t2 l3
          GT -> Just $ freshInsertADShare key t l2
  in fromMaybe s (insertAD s)

freshInsertADShare :: AstVarId -> AstDynamic r -> ADShare r -> ADShare r
{-# NOINLINE freshInsertADShare #-}
freshInsertADShare !key !t !s = unsafePerformIO $ do
  id0 <- unsafeGetFreshId
  return $! ADShareCons id0 key t s

mergeADShare :: forall r. ADShare r -> ADShare r -> ADShare r
mergeADShare !s1 !s2 =
  let mergeAD :: ADShare r -> ADShare r -> Maybe (ADShare r)
      mergeAD ADShareNil ADShareNil = Nothing
      mergeAD !l ADShareNil = Just l
      mergeAD ADShareNil !l = Just l
      mergeAD l1@(ADShareCons id1 key1 t1 rest1)
              l2@(ADShareCons id2 key2 t2 rest2) =
        if id1 == id2
        then -- This assert is quadratic, so can only be enabled when debugging:
             -- assert (_lengthADShare l1 == _lengthADShare l2) $
             Nothing
               -- the lists only ever grow and only in fresh/unique way,
               -- so an identical id means the rest is the same
        else case compare key1 key2 of
          EQ -> case mergeAD rest1 rest2 of
             Nothing -> Nothing
             Just l3 -> Just $ freshInsertADShare key2 t2 l3
          LT -> case mergeAD l1 rest2 of
             Nothing -> Just l2
             Just l3 -> Just $ freshInsertADShare key2 t2 l3
          GT -> case mergeAD rest1 l2 of
             Nothing -> Just l1
             Just l3 -> Just $ freshInsertADShare key1 t1 l3
  in fromMaybe s1 (mergeAD s1 s2)

-- The result type is not as expected. The result is as if assocsADShare
-- was applied to the expected one.
subtractADShare :: forall r.
                   ADShare r -> ADShare r -> [(AstVarId, AstDynamic r)]
{-# INLINE subtractADShare #-}  -- help list fusion
subtractADShare !s1 !s2 =
  let subAD :: ADShare r -> ADShare r -> [(AstVarId, AstDynamic r)]
      subAD !l ADShareNil = assocsADShare l
      subAD ADShareNil _ = []
      subAD l1@(ADShareCons id1 key1 t1 rest1)
            l2@(ADShareCons id2 key2 _ rest2) =
        if id1 == id2
        then []
               -- the lists only ever grow and only in fresh/unique way,
               -- so an identical id means the rest is the same
        else case compare key1 key2 of
          EQ -> subAD rest1 rest2
          LT -> subAD l1 rest2
          GT -> (key1, t1) : subAD rest1 l2
  in subAD s1 s2

flattenADShare :: [ADShare r] -> ADShare r
flattenADShare = foldl' mergeADShare emptyADShare

assocsADShare :: ADShare r -> [(AstVarId, AstDynamic r)]
{-# INLINE assocsADShare #-}  -- help list fusion
assocsADShare ADShareNil = []
assocsADShare (ADShareCons _ key t rest) = (key, t) : assocsADShare rest

_lengthADShare :: Int -> ADShare r -> Int
_lengthADShare acc ADShareNil = acc
_lengthADShare acc (ADShareCons _ _ _ rest) = _lengthADShare (acc + 1) rest
