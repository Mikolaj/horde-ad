{-# LANGUAGE AllowAmbiguousTypes, QuantifiedConstraints,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | AST of the code to be differentiated. It's needed mostly for handling
-- higher order operations such as build and map and for producing reusable
-- gradients, but can be used for arbitrary code transformations
-- at the cost of limiting expressiveness of transformed fragments
-- to what AST captures.
module HordeAd.Core.Ast
  ( AstOf, AstVarId, intToAstVarId, ADAstArtifact6
  , AstIndex, AstVarList, AstIndexS, AstVarListS
  , AstRanked(..), AstNoVectorize(..), AstNoSimplify(..)
  , AstPrimalPart(..), AstDualPart(..)
  , AstShaped(..), AstPrimalPartS(..), AstDualPartS(..)
  , AstDynamic(..), AstDomains(..)
  , AstVarName(..), AstDynamicVarName(..), AstInt(..), AstBool(..)
  , OpCode(..), OpCodeNum(..), OpCodeIntegral(..)
  , OpCodeInt(..), OpCodeBool(..), OpCodeRel(..)
  , ADShare
  , emptyADShare, insertADShare, mergeADShare, subtractADShare
  , flattenADShare, assocsADShare, nullADShare
  , astPrimalPart, astPrimalPartS
  ) where

import Prelude

import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as OS
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Clown
import           Data.Bifunctor.Flip
import           Data.Boolean
import           Data.Int (Int64)
import           Data.IORef.Unboxed (Counter, atomicAddCounter_, newCounter)
import           Data.Kind (Type)
import           Data.List (foldl')
import           Data.Maybe (fromMaybe)
import qualified Data.Strict.Vector as Data.Vector
import           GHC.TypeLits (KnownNat, type (+), type (<=))
import           System.IO.Unsafe (unsafePerformIO)

import HordeAd.Core.ShapedList (ShapedList (..))
import HordeAd.Core.SizedIndex
import HordeAd.Core.SizedList
import HordeAd.Core.Types

-- * Basic type family instances

type instance RankedOf (Clown AstDynamic) = AstRanked
type instance ShapedOf (Clown AstDynamic) = AstShaped
type instance RankedOf AstRanked = AstRanked
type instance ShapedOf AstRanked = AstShaped
type instance PrimalOf AstRanked = AstPrimalPart
type instance DualOf AstRanked = AstDualPart
type instance RankedOf AstPrimalPart = AstPrimalPart
type instance ShapedOf AstPrimalPart = AstPrimalPartS
type instance PrimalOf AstPrimalPart = AstPrimalPart
type instance DualOf AstPrimalPart = DummyDual
type instance RankedOf AstNoVectorize = AstNoVectorize
type instance ShapedOf AstNoVectorize = AstShaped
type instance PrimalOf AstNoVectorize = AstPrimalPart
type instance DualOf AstNoVectorize = AstDualPart
type instance RankedOf AstNoSimplify = AstNoSimplify
type instance ShapedOf AstNoSimplify = AstShaped
type instance PrimalOf AstNoSimplify = AstPrimalPart
type instance DualOf AstNoSimplify = AstDualPart
type instance RankedOf AstShaped = AstRanked
type instance ShapedOf AstShaped = AstShaped
type instance PrimalOf AstShaped = AstPrimalPartS
type instance DualOf AstShaped = AstDualPartS
type instance RankedOf AstPrimalPartS = AstPrimalPart
type instance ShapedOf AstPrimalPartS = AstPrimalPartS
type instance PrimalOf AstPrimalPartS = AstPrimalPartS
type instance DualOf AstPrimalPartS = DummyDual


-- * Ast and related definitions

-- | The type family that to a concrete tensor type assigns its
-- corresponding AST type.
type AstOf :: forall k. TensorKind k -> TensorKind k
type family AstOf f = result | result -> f where
  AstOf (Clown OD.Array) = Clown AstDynamic
  AstOf (Flip OR.Array) = AstRanked
  AstOf (Flip OS.Array) = AstShaped

-- We avoid adding a phantom type denoting the underlying scalar,
-- because the type families over tensor ranks make quanitified constraints
-- impossible and so the phantom type leads to passing explicit (and implicit)
-- type equality proofs around.
newtype AstVarId = AstVarId Int
 deriving (Eq, Ord, Show, Enum)

intToAstVarId :: Int -> AstVarId
intToAstVarId = AstVarId

newtype AstVarName t = AstVarName AstVarId
 deriving (Eq, Show)

data AstDynamicVarName where
  AstDynamicVarName :: (OS.Shape sh, GoodScalar r)
                    => AstVarId -> AstDynamicVarName
deriving instance Show AstDynamicVarName

-- The artifact from step 6) of our full pipeline.
type ADAstArtifact6 f r y =
  ( (AstVarName (f r y), [AstDynamicVarName]), AstDomains
  , PrimalOf (AstOf f) r y )

type AstIndex n = Index n AstInt

type AstVarList n = SizedList n AstVarId

type AstIndexS sh = ShapedList sh AstInt

type AstVarListS sh = ShapedList sh AstVarId

-- We use here @ShapeInt@ for simplicity. @Shape n AstInt@ gives
-- more expressiveness, but leads to irregular tensors,
-- especially after vectorization, and prevents statically known shapes.

-- | AST for a tensor of rank n and elements r that is meant
-- to be differentiated.
data AstRanked :: RankedTensorKind where
  -- To permit defining objective functions in Ast, not just constants:
  AstVar :: ShapeInt n -> AstVarId -> AstRanked r n
  AstLet :: (KnownNat n, KnownNat m, GoodScalar r)
         => AstVarId -> AstRanked r n -> AstRanked r2 m -> AstRanked r2 m
  AstLetADShare :: ADShare -> AstRanked r n -> AstRanked r n
   -- there are mixed local/global lets, because they can be identical
   -- to the lets stored in the D constructor and so should not be inlined
   -- even in trivial cases until the transpose pass eliminates D

  -- For the numeric classes:
  AstNm :: OpCodeNum -> [AstRanked r n] -> AstRanked r n
             -- name of the same length as AstOp for tests
  AstOp :: OpCode -> [AstRanked r n] -> AstRanked r n
  AstOpIntegral :: OpCodeIntegral -> [AstRanked Int64 n] -> AstRanked Int64 n
  AstSumOfList :: [AstRanked r n] -> AstRanked r n
  AstIota :: AstRanked r 1
    -- needed, because toInteger and so fromIntegral is not defined for Ast

  -- For the Tensor class:
  AstIndex :: forall m n r. KnownNat m
           => AstRanked r (m + n) -> AstIndex m -> AstRanked r n
    -- first ix is for outermost dimension; empty index means identity,
    -- if index is out of bounds, the result is defined and is 0,
    -- but vectorization is permitted to change the value
  AstSum :: AstRanked r (1 + n) -> AstRanked r n
  AstScatter :: forall m n p r. (KnownNat m, KnownNat n, KnownNat p)
             => ShapeInt (p + n)
             -> AstRanked r (m + n) -> (AstVarList m, AstIndex p)
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
  AstGather :: forall m n p r. (KnownNat m, KnownNat n, KnownNat p)
            => ShapeInt (m + n)
            -> AstRanked r (p + n) -> (AstVarList m, AstIndex p)
            -> AstRanked r (m + n)
    -- out of bounds indexing is permitted
  AstCast :: GoodScalar r1
          => AstRanked r1 n -> AstRanked r2 n

  AstSToR :: OS.Shape sh
          => AstShaped r sh -> AstRanked r (OS.Rank sh)

  -- For the forbidden half of the Tensor class:
  AstConst :: OR.Array n r -> AstRanked r n
  AstConstant :: AstPrimalPart r n -> AstRanked r n
  AstD :: AstPrimalPart r n -> AstDualPart r n -> AstRanked r n
  AstLetDomains :: Data.Vector.Vector AstVarId -> AstDomains
                -> AstRanked r n
                -> AstRanked r n

  AstFloor :: GoodScalar r
           => AstPrimalPart r n -> AstRanked Int64 n
  AstCond :: AstBool
          -> AstRanked r n -> AstRanked r n -> AstRanked r n
  AstMinIndex :: GoodScalar r
              => AstPrimalPart r (1 + n) -> AstRanked Int64 n
  AstMaxIndex :: GoodScalar r
              => AstPrimalPart r (1 + n) -> AstRanked Int64 n

deriving instance GoodScalar r => Show (AstRanked r n)

newtype AstNoVectorize r n = AstNoVectorize {unAstNoVectorize :: AstRanked r n}
deriving instance GoodScalar r => Show (AstNoVectorize r n)

newtype AstNoSimplify r n = AstNoSimplify {unAstNoSimplify :: AstRanked r n}
deriving instance GoodScalar r => Show (AstNoSimplify r n)

newtype AstPrimalPart r n = AstPrimalPart {unAstPrimalPart :: AstRanked r n}
deriving instance GoodScalar r => Show (AstPrimalPart r n)

newtype AstDualPart r n = AstDualPart {unAstDualPart :: AstRanked r n}
deriving instance GoodScalar r => Show (AstDualPart r n)

data AstShaped :: ShapedTensorKind where
  -- To permit defining objective functions in Ast, not just constants:
  AstVarS :: forall sh r. AstVarId -> AstShaped r sh
  AstLetS :: (OS.Shape sh, OS.Shape sh2, GoodScalar r)
          => AstVarId -> AstShaped r sh -> AstShaped r2 sh2 -> AstShaped r2 sh2
  AstLetADShareS :: ADShare -> AstShaped r sh -> AstShaped r sh
   -- there are mixed local/global lets, because they can be identical
   -- to the lets stored in the D constructor and so should not be inlined
   -- even in trivial cases until the transpose pass eliminates D

  -- For the numeric classes:
  AstNmS :: OpCodeNum -> [AstShaped r sh] -> AstShaped r sh
  AstOpS :: OpCode -> [AstShaped r sh] -> AstShaped r sh
  AstOpIntegralS :: OpCodeIntegral -> [AstShaped Int64 sh] -> AstShaped Int64 sh
  AstSumOfListS :: [AstShaped r sh] -> AstShaped r sh
  AstIotaS :: forall n r. KnownNat n => AstShaped r '[n]
    -- needed, because toInteger and so fromIntegral is not defined for Ast

  -- For the Tensor class:
  AstIndexS :: forall sh1 sh2 r.
               (OS.Shape sh1, OS.Shape sh2, OS.Shape (sh1 OS.++ sh2))
            => AstShaped r (sh1 OS.++ sh2) -> AstIndexS sh1
            -> AstShaped r sh2
    -- first ix is for outermost dimension; empty index means identity,
    -- if index is out of bounds, the result is defined and is 0,
    -- but vectorization is permitted to change the value
  AstSumS :: KnownNat n
          => AstShaped r (n ': sh) -> AstShaped r sh
  AstScatterS :: forall sh2 p sh r.
                 ( OS.Shape sh2, OS.Shape sh
                 , OS.Shape (OS.Take p sh), OS.Shape (OS.Drop p sh)
                 , OS.Shape (sh2 OS.++ OS.Drop p sh) )
              => AstShaped r (sh2 OS.++ OS.Drop p sh)
              -> (AstVarListS sh2, AstIndexS (OS.Take p sh))
              -> AstShaped r sh

  AstFromListS :: (KnownNat n, OS.Shape sh)
               => [AstShaped r sh] -> AstShaped r (n ': sh)
  AstFromVectorS :: (KnownNat n, OS.Shape sh)
                 => Data.Vector.Vector (AstShaped r sh) -> AstShaped r (n ': sh)
  AstReplicateS :: (KnownNat n, OS.Shape sh)
                => AstShaped r sh -> AstShaped r (n ': sh)
  AstAppendS :: (KnownNat n, KnownNat m, OS.Shape sh)
             => AstShaped r (m ': sh) -> AstShaped r (n ': sh)
             -> AstShaped r ((m + n) ': sh)
  AstSliceS :: (KnownNat i, KnownNat k, KnownNat n, OS.Shape sh)
            => AstShaped r (i + n + k ': sh) -> AstShaped r (n ': sh)
  AstReverseS :: (KnownNat n, OS.Shape sh)
              => AstShaped r (n ': sh) -> AstShaped r (n ': sh)
  AstTransposeS :: forall perm sh r.
                   ( OS.Permutation perm, OS.Shape perm, OS.Shape sh
                   , KnownNat (OS.Rank sh), OS.Rank perm <= OS.Rank sh )
                => AstShaped r sh -> AstShaped r (OS.Permute perm sh)
  AstReshapeS :: (OS.Shape sh, OS.Size sh ~ OS.Size sh2)
              => AstShaped r sh -> AstShaped r sh2
    -- beware that the order of type arguments is different than in orthotope
    -- and than the order of value arguments in the ranked version
  AstBuild1S :: (KnownNat n, OS.Shape sh)
             => (AstVarId, AstShaped r sh) -> AstShaped r (n ': sh)
  AstGatherS :: forall sh2 p sh r.
                ( OS.Shape sh, OS.Shape sh2
                , OS.Shape (OS.Take p sh), OS.Shape (OS.Drop p sh) )
             => AstShaped r sh
             -> (AstVarListS sh2, AstIndexS (OS.Take p sh))
             -> AstShaped r (sh2 OS.++ OS.Drop p sh)
    -- out of bounds indexing is permitted
  AstCastS :: GoodScalar r1
           => AstShaped r1 sh -> AstShaped r2 sh

  AstRToS :: (OS.Shape sh, KnownNat (OS.Rank sh))
          => AstRanked r (OS.Rank sh) -> AstShaped r sh

  -- For the forbidden half of the Tensor class:
  AstConstS :: OS.Array sh r -> AstShaped r sh
  AstConstantS :: AstPrimalPartS r sh -> AstShaped r sh
  AstDS :: AstPrimalPartS r sh -> AstDualPartS r sh -> AstShaped r sh
  AstLetDomainsS :: Data.Vector.Vector AstVarId -> AstDomains
                 -> AstShaped r sh
                 -> AstShaped r sh

  AstFloorS :: GoodScalar r
            => AstPrimalPartS r sh -> AstShaped Int64 sh
  AstCondS :: AstBool
           -> AstShaped r sh -> AstShaped r sh -> AstShaped r sh
  AstMinIndexS :: (OS.Shape sh, KnownNat n, GoodScalar r)
               => AstPrimalPartS r (n ': sh)
               -> AstShaped Int64 (OS.Init (n ': sh))
  AstMaxIndexS :: (OS.Shape sh, KnownNat n, GoodScalar r)
               => AstPrimalPartS r (n ': sh)
               -> AstShaped Int64 (OS.Init (n ': sh))

deriving instance (GoodScalar r, OS.Shape sh) => Show (AstShaped r sh)

newtype AstPrimalPartS r sh =
  AstPrimalPartS {unAstPrimalPartS :: AstShaped r sh}
deriving instance (GoodScalar r, OS.Shape sh) => Show (AstPrimalPartS r sh)

newtype AstDualPartS r sh = AstDualPartS {unAstDualPartS :: AstShaped r sh}
deriving instance (GoodScalar r, OS.Shape sh) => Show (AstDualPartS r sh)

data AstDynamic :: Type -> Type where
  AstRToD :: KnownNat n
          => AstRanked r n -> AstDynamic r
  AstSToD :: OS.Shape sh
          => AstShaped r sh -> AstDynamic r
deriving instance GoodScalar r => Show (AstDynamic r)

data AstDomains where
  AstDomains :: Data.Vector.Vector (DynamicExists AstDynamic) -> AstDomains
  AstDomainsLet :: (KnownNat n, GoodScalar r)
                => AstVarId -> AstRanked r n -> AstDomains -> AstDomains
  AstDomainsLetS :: (OS.Shape sh, GoodScalar r)
                 => AstVarId -> AstShaped r sh -> AstDomains -> AstDomains
deriving instance Show AstDomains

-- The argument is the underlying scalar.
data AstInt where
  AstIntVar :: AstVarId -> AstInt
  AstIntOp :: OpCodeInt -> [AstInt] -> AstInt
  AstIntConst :: Int -> AstInt
  AstIntFloor :: GoodScalar r
              => AstPrimalPart r 0 -> AstInt
  AstIntFloorS :: GoodScalar r
               => AstPrimalPartS r '[] -> AstInt
  AstIntCond :: AstBool -> AstInt -> AstInt -> AstInt
  AstMinIndex1 :: GoodScalar r
               => AstPrimalPart r 1 -> AstInt
  AstMaxIndex1 :: GoodScalar r
               => AstPrimalPart r 1 -> AstInt
  AstMinIndex1S :: (KnownNat n, GoodScalar r)
                => AstPrimalPartS r '[n] -> AstInt
  AstMaxIndex1S :: (KnownNat n, GoodScalar r)
                => AstPrimalPartS r '[n] -> AstInt
deriving instance Show AstInt

data AstBool where
  AstBoolOp :: OpCodeBool -> [AstBool] -> AstBool
  AstBoolConst :: Bool -> AstBool
  AstRel :: (KnownNat n, GoodScalar r)
         => OpCodeRel -> [AstPrimalPart r n] -> AstBool
  AstRelS :: (OS.Shape sh, GoodScalar r)
          => OpCodeRel -> [AstPrimalPartS r sh] -> AstBool
  AstRelInt :: OpCodeRel -> [AstInt] -> AstBool
deriving instance Show AstBool

data OpCodeNum =
    MinusOp | TimesOp | NegateOp | AbsOp | SignumOp
  | MaxOp | MinOp
 deriving Show

data OpCode =
    DivideOp | RecipOp
  | ExpOp | LogOp | SqrtOp | PowerOp | LogBaseOp
  | SinOp | CosOp | TanOp | AsinOp | AcosOp | AtanOp
  | SinhOp | CoshOp | TanhOp | AsinhOp | AcoshOp | AtanhOp
  | Atan2Op
 deriving Show

data OpCodeIntegral =
  QuotOp | RemOp
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


-- * Unlawful instances of AST int and bool; they are lawful modulo evaluation

type instance BooleanOf AstInt = AstBool

instance IfB AstInt where
  ifB (AstBoolConst b) v w = if b then v else w  -- common in indexing
  ifB b v w = AstIntCond b v w

instance EqB AstInt where
  v ==* u = AstRelInt EqOp [v, u]
  v /=* u = AstRelInt NeqOp [v, u]

instance OrdB AstInt where
  AstIntConst u <* AstIntConst v = AstBoolConst $ u < v  -- common in indexing
  v <* u = AstRelInt LsOp [v, u]
  AstIntConst u <=* AstIntConst v = AstBoolConst $ u <= v  -- common in indexing
  v <=* u = AstRelInt LeqOp [v, u]
  AstIntConst u >* AstIntConst v = AstBoolConst $ u > v  -- common in indexing
  v >* u = AstRelInt GtOp [v, u]
  AstIntConst u >=* AstIntConst v = AstBoolConst $ u >= v  -- common in indexing
  v >=* u = AstRelInt GeqOp [v, u]

instance Eq AstInt where
  _ == _ = error "AstInt: can't evaluate terms for Eq"

instance Ord AstInt where
  max u v = AstIntOp MaxIntOp [u, v]
  min u v = AstIntOp MinIntOp [u, v]
  _ <= _ = error "AstInt: can't evaluate terms for Ord"

instance Num AstInt where
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

instance Real AstInt where
  toRational = undefined
    -- very low priority, since these are all extremely not continuous

instance Enum AstInt where
  toEnum = AstIntConst
  fromEnum = undefined  -- do we need to define our own Enum for this?

-- Warning: this class lacks toInteger, which also makes it impossible
-- to include AstInt in Ast via fromIntegral, hence AstIota.
-- Warning: div and mod operations are very costly (simplifying them
-- requires constructing conditionals, etc). If this error is removed,
-- they are going to work, but slowly.
instance Integral AstInt where
  quot u v = AstIntOp QuotIntOp [u, v]
  rem u v = AstIntOp RemIntOp [u, v]
  quotRem u v = (AstIntOp QuotIntOp [u, v], AstIntOp RemIntOp [u, v])
  divMod _ _ = error "divMod: disabled; much less efficient than quot and rem"
  toInteger = undefined  -- we can't evaluate uninstantiated variables, etc.

instance Boolean AstBool where
  true = AstBoolConst True
  false = AstBoolConst False
  notB b = AstBoolOp NotOp [b]
  AstBoolConst b &&* AstBoolConst c = AstBoolConst $ b && c
                                        -- common in indexing
  b &&* c = AstBoolOp AndOp [b, c]
  b ||* c = AstBoolOp OrOp [b, c]


-- * Unlawful boolean instances of ranked AST; they are lawful modulo evaluation

type instance BooleanOf (AstRanked r n) = AstBool

instance IfB (AstRanked r n) where
  ifB = astCond

-- No simplification yet done at this point, so AstBoolConst unlikely,
-- but it's a constant time simplification, so no harm done.
-- The AstConstant is more helpful, making Delta expressions smaller.
-- A stronger version of this function is in AstSimplify.
astCond :: AstBool -> AstRanked r n -> AstRanked r n -> AstRanked r n
astCond (AstBoolConst b) v w = if b then v else w
astCond b (AstConstant (AstPrimalPart v))
          (AstConstant (AstPrimalPart w)) =
  AstConstant $ astPrimalPart $ AstCond b v w
astCond b v w = AstCond b v w

astPrimalPart :: AstRanked r n -> AstPrimalPart r n
astPrimalPart (AstConstant t) = t
astPrimalPart t = AstPrimalPart t

instance (KnownNat n, GoodScalar r) => EqB (AstRanked r n) where
  v ==* u = AstRel EqOp [astPrimalPart v, astPrimalPart u]
  v /=* u = AstRel NeqOp [astPrimalPart v, astPrimalPart u]

instance (KnownNat n, GoodScalar r) => OrdB (AstRanked r n) where
  v <* u = AstRel LsOp [astPrimalPart v, astPrimalPart u]
  v <=* u = AstRel LeqOp [astPrimalPart v, astPrimalPart u]
  v >* u = AstRel GtOp [astPrimalPart v, astPrimalPart u]
  v >=* u = AstRel GeqOp [astPrimalPart v, astPrimalPart u]

type instance BooleanOf (AstNoVectorize r n) = AstBool

instance IfB (AstNoVectorize r n) where
  ifB b v w = AstNoVectorize $ astCond b (unAstNoVectorize v)
                                         (unAstNoVectorize w)

instance (KnownNat n, GoodScalar r) => EqB (AstNoVectorize r n) where
  v ==* u = AstRel EqOp [ astPrimalPart $ unAstNoVectorize v
                        , astPrimalPart $ unAstNoVectorize u ]
  v /=* u = AstRel NeqOp [ astPrimalPart $ unAstNoVectorize v
                         , astPrimalPart $ unAstNoVectorize u ]

instance (KnownNat n, GoodScalar r) => OrdB (AstNoVectorize r n) where
  v <* u = AstRel LsOp [ astPrimalPart $ unAstNoVectorize v
                       , astPrimalPart $ unAstNoVectorize u ]
  v <=* u = AstRel LeqOp [ astPrimalPart $ unAstNoVectorize v
                         , astPrimalPart $ unAstNoVectorize u ]
  v >* u = AstRel GtOp [ astPrimalPart $ unAstNoVectorize v
                       , astPrimalPart $ unAstNoVectorize u ]
  v >=* u = AstRel GeqOp [ astPrimalPart $ unAstNoVectorize v
                         , astPrimalPart $ unAstNoVectorize u ]

type instance BooleanOf (AstNoSimplify r n) = AstBool

instance IfB (AstNoSimplify r n) where
  ifB b v w = AstNoSimplify $ astCond b (unAstNoSimplify v)
                                        (unAstNoSimplify w)

instance (KnownNat n, GoodScalar r) => EqB (AstNoSimplify r n) where
  v ==* u = AstRel EqOp [ astPrimalPart $ unAstNoSimplify v
                        , astPrimalPart $ unAstNoSimplify u ]
  v /=* u = AstRel NeqOp [ astPrimalPart $ unAstNoSimplify v
                         , astPrimalPart $ unAstNoSimplify u ]

instance (KnownNat n, GoodScalar r) => OrdB (AstNoSimplify r n) where
  v <* u = AstRel LsOp [ astPrimalPart $ unAstNoSimplify v
                       , astPrimalPart $ unAstNoSimplify u ]
  v <=* u = AstRel LeqOp [ astPrimalPart $ unAstNoSimplify v
                         , astPrimalPart $ unAstNoSimplify u ]
  v >* u = AstRel GtOp [ astPrimalPart $ unAstNoSimplify v
                       , astPrimalPart $ unAstNoSimplify u ]
  v >=* u = AstRel GeqOp [ astPrimalPart $ unAstNoSimplify v
                         , astPrimalPart $ unAstNoSimplify u ]

type instance BooleanOf (AstPrimalPart r n) = AstBool

instance IfB (AstPrimalPart r n) where
  ifB b v w = astPrimalPart $ astCond b (unAstPrimalPart v) (unAstPrimalPart w)

instance (KnownNat n, GoodScalar r) => EqB (AstPrimalPart r n) where
  v ==* u = AstRel EqOp [v, u]
  v /=* u = AstRel NeqOp [v, u]

instance (KnownNat n, GoodScalar r) => OrdB (AstPrimalPart r n) where
  v <* u = AstRel LsOp [v, u]
  v <=* u = AstRel LeqOp [v, u]
  v >* u = AstRel GtOp [v, u]
  v >=* u = AstRel GeqOp [v, u]


-- * Unlawful numeric instances of ranked AST; they are lawful modulo evaluation

-- See the comment about @Eq@ and @Ord@ in "DualNumber".
instance Eq (AstRanked r n) where
  _ == _ = error "Ast: can't evaluate terms for Eq"

instance (Ord r, Num r, Ord (OR.Array n r)) => Ord (AstRanked r n) where
  _ <= _ = error "Ast: can't evaluate terms for Ord"

instance (Num (OR.Array n r)) => Num (AstRanked r n) where
  AstSumOfList lu + AstSumOfList lv = AstSumOfList (lu ++ lv)
  u + AstSumOfList l = AstSumOfList (u : l)
  AstSumOfList l + u = AstSumOfList (u : l)
  u + v = AstSumOfList [u, v]
  u - v = AstNm MinusOp [u, v]
  u * v = AstNm TimesOp [u, v]
    -- no hacks like for AstSumOfList, because when tscaleByScalar
    -- is reconstructed, it looks for the binary form
  negate u = AstNm NegateOp [u]
  abs v = AstNm AbsOp [v]
  signum v = AstNm SignumOp [v]
  fromInteger = AstConstant . AstPrimalPart . AstConst . fromInteger

instance Enum (AstRanked Int64 n) where
  toEnum = undefined  -- AstConst . OR.scalar . toEnum
  fromEnum = undefined  -- do we need to define our own Enum for this?

-- Warning: this class lacks toInteger, which also makes it impossible
-- to include AstInt in Ast via fromIntegral, hence AstIota.
-- Warning: div and mod operations are very costly (simplifying them
-- requires constructing conditionals, etc). If this error is removed,
-- they are going to work, but slowly.
instance Integral (OR.Array n Int64) => Integral (AstRanked Int64 n) where
  quot u v = AstOpIntegral QuotOp [u, v]
  rem u v = AstOpIntegral RemOp [u, v]
  quotRem u v = (AstOpIntegral QuotOp [u, v], AstOpIntegral RemOp [u, v])
  divMod _ _ = error "divMod: disabled; much less efficient than quot and rem"
  toInteger = undefined  -- we can't evaluate uninstantiated variables, etc.

instance (Real r, Real (OR.Array n r))
         => Real (AstRanked r n) where
  toRational = undefined
    -- very low priority, since these are all extremely not continuous

instance Fractional (OR.Array n r)
         => Fractional (AstRanked r n) where
  u / v = AstOp DivideOp  [u, v]
  recip v = AstOp RecipOp [v]
  fromRational = AstConstant . AstPrimalPart . AstConst . fromRational

instance (RealFloat r, Floating (OR.Array n r))
         => Floating (AstRanked r n) where
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

instance (RealFloat r, RealFrac (OR.Array n r))
         => RealFrac (AstRanked r n) where
  properFraction = undefined
    -- The integral type doesn't have a Storable constraint,
    -- so we can't implement this (nor RealFracB from Boolean package).

instance (RealFloat r,  RealFloat (OR.Array n r))
         => RealFloat (AstRanked r n) where
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

instance (Ord r, Num r, Ord (AstRanked r n)) => Ord (AstNoVectorize r n) where
  _ <= _ = error "AstNoVectorize: can't evaluate terms for Ord"

deriving instance Num (AstRanked r n) => Num (AstNoVectorize r n)
deriving instance (Real r, Real (AstRanked r n))
                   => Real (AstNoVectorize r n)
deriving instance Enum (AstRanked r n) => Enum (AstNoVectorize r n)
deriving instance (Real r, Integral (AstRanked r n))
                  => Integral (AstNoVectorize r n)
deriving instance Fractional (AstRanked r n) => Fractional (AstNoVectorize r n)
deriving instance Floating (AstRanked r n) => Floating (AstNoVectorize r n)
deriving instance (RealFloat r, RealFrac (AstRanked r n))
                  => RealFrac (AstNoVectorize r n)
deriving instance (RealFloat r, RealFloat (AstRanked r n))
                  => RealFloat (AstNoVectorize r n)

instance Eq (AstNoSimplify r n) where
  _ == _ = error "AstNoSimplify: can't evaluate terms for Eq"

instance (Ord r, Num r, Ord (AstRanked r n)) => Ord (AstNoSimplify r n) where
  _ <= _ = error "AstNoSimplify: can't evaluate terms for Ord"

deriving instance Num (AstRanked r n) => Num (AstNoSimplify r n)
deriving instance (Real r, Real (AstRanked r n))
                  => Real (AstNoSimplify r n)
deriving instance Enum (AstRanked r n) => Enum (AstNoSimplify r n)
deriving instance (Real r, Integral (AstRanked r n))
                  => Integral (AstNoSimplify r n)
deriving instance Fractional (AstRanked r n) => Fractional (AstNoSimplify r n)
deriving instance Floating (AstRanked r n) => Floating (AstNoSimplify r n)
deriving instance (RealFloat r, RealFrac (AstRanked r n))
                  => RealFrac (AstNoSimplify r n)
deriving instance (RealFloat r, RealFloat (AstRanked r n))
                  => RealFloat (AstNoSimplify r n)

instance Eq (AstPrimalPart r n) where
  _ == _ = error "AstPrimalPart: can't evaluate terms for Eq"

instance (Ord r, Num r, Ord (AstRanked r n)) => Ord (AstPrimalPart r n) where
  max (AstPrimalPart u) (AstPrimalPart v) =
    AstPrimalPart (AstNm MaxOp [u, v])
      -- these are only correct when the dual part is empty, as it's here
  min (AstPrimalPart u) (AstPrimalPart v) =
    AstPrimalPart (AstNm MinOp [u, v])
  _ <= _ = error "AstPrimalPart: can't evaluate terms for Ord"

deriving instance Num (AstRanked r n) => Num (AstPrimalPart r n)
deriving instance (Real r, Real (AstRanked r n))
                  => Real (AstPrimalPart r n)
deriving instance Enum (AstRanked r n) => Enum (AstPrimalPart r n)
deriving instance (Real r, Integral (AstRanked r n))
                  => Integral (AstPrimalPart r n)
deriving instance Fractional (AstRanked r n) => Fractional (AstPrimalPart r n)
deriving instance Floating (AstRanked r n) => Floating (AstPrimalPart r n)
deriving instance (RealFloat r, RealFrac (AstRanked r n))
                  => RealFrac (AstPrimalPart r n)
deriving instance (RealFloat r,  RealFloat (AstRanked r n))
                  => RealFloat (AstPrimalPart r n)


-- * Unlawful boolean instances of shaped AST; they are lawful modulo evaluation

type instance BooleanOf (AstShaped r sh) = AstBool

instance IfB (AstShaped r sh) where
  ifB = astCondS

-- No simplification yet done at this point, so AstBoolConst unlikely,
-- but it's a constant time simplification, so no harm done.
-- The AstConstant is more helpful, making Delta expressions smaller.
-- A stronger version of this function is in AstSimplify.
astCondS :: AstBool -> AstShaped r sh -> AstShaped r sh -> AstShaped r sh
astCondS (AstBoolConst b) v w = if b then v else w
astCondS b (AstConstantS (AstPrimalPartS v))
           (AstConstantS (AstPrimalPartS w)) =
  AstConstantS $ astPrimalPartS $ AstCondS b v w
astCondS b v w = AstCondS b v w

astPrimalPartS :: AstShaped r n -> AstPrimalPartS r n
astPrimalPartS (AstConstantS t) = t
astPrimalPartS t = AstPrimalPartS t

instance (OS.Shape sh, GoodScalar r) => EqB (AstShaped r sh) where
  v ==* u = AstRelS EqOp [astPrimalPartS v, astPrimalPartS u]
  v /=* u = AstRelS NeqOp [astPrimalPartS v, astPrimalPartS u]

instance (OS.Shape sh, GoodScalar r) => OrdB (AstShaped r sh) where
  v <* u = AstRelS LsOp [astPrimalPartS v, astPrimalPartS u]
  v <=* u = AstRelS LeqOp [astPrimalPartS v, astPrimalPartS u]
  v >* u = AstRelS GtOp [astPrimalPartS v, astPrimalPartS u]
  v >=* u = AstRelS GeqOp [astPrimalPartS v, astPrimalPartS u]

type instance BooleanOf (AstPrimalPartS r sh) = AstBool

instance IfB (AstPrimalPartS r sh) where
  ifB b v w = astPrimalPartS $ astCondS b (unAstPrimalPartS v)
                                          (unAstPrimalPartS w)

instance (OS.Shape sh, GoodScalar r) => EqB (AstPrimalPartS r sh) where
  v ==* u = AstRelS EqOp [v, u]
  v /=* u = AstRelS NeqOp [v, u]

instance (OS.Shape sh, GoodScalar r) => OrdB (AstPrimalPartS r sh) where
  v <* u = AstRelS LsOp [v, u]
  v <=* u = AstRelS LeqOp [v, u]
  v >* u = AstRelS GtOp [v, u]
  v >=* u = AstRelS GeqOp [v, u]


-- * Unlawful numeric instances of shaped AST; they are lawful modulo evaluation

-- See the comment about @Eq@ and @Ord@ in "DualNumber".
instance Eq (AstShaped r sh) where
  _ == _ = error "Ast: can't evaluate terms for Eq"

instance (Ord r, Num r, Ord (OS.Array sh r)) => Ord (AstShaped r sh) where
  -- Unfortunately, the others can't be made to return @AstBool@.
  _ <= _ = error "Ast: can't evaluate terms for Ord"

instance (Num (OS.Array sh r)) => Num (AstShaped r sh) where
  AstSumOfListS lu + AstSumOfListS lv = AstSumOfListS (lu ++ lv)
  u + AstSumOfListS l = AstSumOfListS (u : l)
  AstSumOfListS l + u = AstSumOfListS (u : l)
  u + v = AstSumOfListS [u, v]
  u - v = AstNmS MinusOp [u, v]
  u * v = AstNmS TimesOp [u, v]
    -- no hacks like for AstSumOfListS, because when tscaleByScalar
    -- is reconstructed, it looks for the binary form
  negate u = AstNmS NegateOp [u]
  abs v = AstNmS AbsOp [v]
  signum v = AstNmS SignumOp [v]
  fromInteger = AstConstantS . AstPrimalPartS . AstConstS . fromInteger

instance (Real r, Real (OS.Array sh r)) => Real (AstShaped r sh) where
  toRational = undefined
    -- very low priority, since these are all extremely not continuous

instance Enum (AstShaped Int64 n) where
  toEnum = undefined
  fromEnum = undefined  -- do we need to define our own Enum for this?

-- Warning: this class lacks toInteger, which also makes it impossible
-- to include AstInt in Ast via fromIntegral, hence AstIota.
-- Warning: div and mod operations are very costly (simplifying them
-- requires constructing conditionals, etc). If this error is removed,
-- they are going to work, but slowly.
instance Integral (OS.Array sh Int64) => Integral (AstShaped Int64 sh) where
  quot u v = AstOpIntegralS QuotOp [u, v]
  rem u v = AstOpIntegralS RemOp [u, v]
  quotRem u v = (AstOpIntegralS QuotOp [u, v], AstOpIntegralS RemOp [u, v])
  divMod _ _ = error "divMod: disabled; much less efficient than quot and rem"
  toInteger = undefined  -- we can't evaluate uninstantiated variables, etc.

instance Fractional (OS.Array sh r)
         => Fractional (AstShaped r sh) where
  u / v = AstOpS DivideOp  [u, v]
  recip v = AstOpS RecipOp [v]
  fromRational = AstConstantS . AstPrimalPartS . AstConstS . fromRational

instance (RealFloat r, Floating (OS.Array sh r))
         => Floating (AstShaped r sh) where
  pi = AstConstantS $ AstPrimalPartS $ AstConstS pi
  exp u = AstOpS ExpOp [u]
  log u = AstOpS LogOp [u]
  sqrt u = AstOpS SqrtOp [u]
  u ** v = AstOpS PowerOp [u, v]
  logBase u v = AstOpS LogBaseOp [u, v]
  sin u = AstOpS SinOp [u]
  cos u = AstOpS CosOp [u]
  tan u = AstOpS TanOp [u]
  asin u = AstOpS AsinOp [u]
  acos u = AstOpS AcosOp [u]
  atan u = AstOpS AtanOp [u]
  sinh u = AstOpS SinhOp [u]
  cosh u = AstOpS CoshOp [u]
  tanh u = AstOpS TanhOp [u]
  asinh u = AstOpS AsinhOp [u]
  acosh u = AstOpS AcoshOp [u]
  atanh u = AstOpS AtanhOp [u]

instance (RealFloat r, RealFrac (OS.Array sh r))
         => RealFrac (AstShaped r sh) where
  properFraction = undefined
    -- The integral type doesn't have a Storable constraint,
    -- so we can't implement this (nor RealFracB from Boolean package).

instance (RealFloat r, RealFloat (OS.Array sh r))
         => RealFloat (AstShaped r sh) where
  atan2 u v = AstOpS Atan2Op [u, v]
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

instance Eq (AstPrimalPartS r sh) where
  _ == _ = error "AstPrimalPartS: can't evaluate terms for Eq"

instance (Ord r, Num r, Ord (AstShaped r sh)) => Ord (AstPrimalPartS r sh) where
  max (AstPrimalPartS u) (AstPrimalPartS v) =
    AstPrimalPartS (AstNmS MaxOp [u, v])
      -- these are only correct when the dual part is empty, as it's here
  min (AstPrimalPartS u) (AstPrimalPartS v) =
    AstPrimalPartS (AstNmS MinOp [u, v])
  _ <= _ = error "AstPrimalPartS: can't evaluate terms for Ord"

deriving instance Num (AstShaped r sh) => Num (AstPrimalPartS r sh)
deriving instance (Real r, Real (AstShaped r sh))
                  => Real (AstPrimalPartS r sh)
deriving instance Enum (AstShaped r sh) => Enum (AstPrimalPartS r sh)
deriving instance (Real r, Integral (AstShaped r sh))
                  => Integral (AstPrimalPartS r sh)
deriving instance Fractional (AstShaped r sh)
                  => Fractional (AstPrimalPartS r sh)
deriving instance Floating (AstShaped r sh) => Floating (AstPrimalPartS r sh)
deriving instance (RealFloat r, RealFrac (AstShaped r sh))
                  => RealFrac (AstPrimalPartS r sh)
deriving instance (RealFloat r, RealFloat (AstShaped r sh))
                  => RealFloat (AstPrimalPartS r sh)


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
data ADShare = ADShareNil
             | forall r. GoodScalar r
               => ADShareCons Int AstVarId (AstDynamic r) ADShare
deriving instance Show ADShare

emptyADShare :: ADShare
emptyADShare = ADShareNil

insertADShare :: forall r. GoodScalar r
              => AstVarId -> AstDynamic r -> ADShare -> ADShare
insertADShare !key !t !s =
  -- The Maybe over-engineering ensures that we never refresh an id
  -- unnecessarily. In theory, when merging alternating equal lists
  -- with different ids, this improves runtime from quadratic to linear,
  -- but we apparently don't have such tests or they are too small,
  -- so this causes a couple percent overhead instead.
  let insertAD :: ADShare -> Maybe ADShare
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

freshInsertADShare :: GoodScalar r => AstVarId -> AstDynamic r -> ADShare
                   -> ADShare
{-# NOINLINE freshInsertADShare #-}
freshInsertADShare !key !t !s = unsafePerformIO $ do
  id0 <- unsafeGetFreshId
  return $! ADShareCons id0 key t s

mergeADShare :: ADShare -> ADShare -> ADShare
mergeADShare !s1 !s2 =
  let mergeAD :: ADShare -> ADShare -> Maybe ADShare
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
subtractADShare :: ADShare -> ADShare -> [(AstVarId, DynamicExists AstDynamic)]
{-# INLINE subtractADShare #-}  -- help list fusion
subtractADShare !s1 !s2 =
  let subAD :: ADShare -> ADShare -> [(AstVarId, DynamicExists AstDynamic)]
      subAD !l ADShareNil = assocsADShare l
      subAD ADShareNil _ = []
      subAD l1@(ADShareCons id1 key1 t1 rest1)
            l2@(ADShareCons id2 key2 _ rest2) =
        if id1 == id2
        then []  -- the lists only ever grow and only in fresh/unique way,
                 -- so an identical id means the rest is the same
        else case compare key1 key2 of
          EQ -> subAD rest1 rest2
          LT -> subAD l1 rest2
          GT -> (key1, DynamicExists t1) : subAD rest1 l2
  in subAD s1 s2

flattenADShare :: [ADShare] -> ADShare
flattenADShare = foldl' mergeADShare emptyADShare

assocsADShare :: ADShare -> [(AstVarId, DynamicExists AstDynamic)]
{-# INLINE assocsADShare #-}  -- help list fusion
assocsADShare ADShareNil = []
assocsADShare (ADShareCons _ key t rest) =
  (key, DynamicExists t) : assocsADShare rest

_lengthADShare :: Int -> ADShare -> Int
_lengthADShare acc ADShareNil = acc
_lengthADShare acc (ADShareCons _ _ _ rest) = _lengthADShare (acc + 1) rest

nullADShare :: ADShare -> Bool
nullADShare ADShareNil = True
nullADShare ADShareCons{} = False
