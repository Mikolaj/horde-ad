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
  ( AstSpanType(..), AstSpan, sameAstSpan, astSpanT
  , AstInt
  , pattern AstIntVar, pattern AstPVar, pattern AstIntConst, pattern AstPConst
  , AstOf, AstVarId, intToAstVarId, ADAstArtifact6
  , AstIndex, AstVarList, AstIndexS, AstVarListS
  , AstRanked(..), AstPrimalPart(..), AstDualPart(..)
  , AstShaped(..), AstPrimalPartS(..), AstDualPartS(..)
  , AstDynamic(..), AstDomains(..)
  , AstVarName(..), AstDynamicVarName(..), AstBool(..)
  , OpCode(..), OpCodeNum(..), OpCodeIntegral(..), OpCodeBool(..), OpCodeRel(..)
  , ADShare
  , emptyADShare, insertADShare, mergeADShare, subtractADShare
  , flattenADShare, assocsADShare, intVarInADShare, nullADShare
  , astCond, astCondS, astPrimalPart, astPrimalPartS
  , AstNoVectorize(..), AstNoSimplify(..)
  ) where

import Prelude

import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as OS
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Clown
import           Data.Bifunctor.Flip
import           Data.Int (Int64)
import           Data.IORef.Unboxed (Counter, atomicAddCounter_, newCounter)
import           Data.Kind (Type)
import           Data.List (foldl')
import           Data.Maybe (fromMaybe)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality ((:~:) (Refl))
import           GHC.TypeLits (KnownNat, type (+), type (<=))
import           System.IO.Unsafe (unsafePerformIO)
import           Type.Reflection (Typeable, eqTypeRep, typeRep, (:~~:) (HRefl))

import HordeAd.Core.ShapedList (ShapedList (..))
import HordeAd.Core.SizedIndex
import HordeAd.Core.SizedList
import HordeAd.Core.Types

-- * Basic types and type family instances

-- To be promoted.
data AstSpanType = AstPrimal | AstDual | AstFull
  deriving Typeable

-- A poor man's singleton type, modelled after orthotope's @Shape@.
class Typeable s => AstSpan (s :: AstSpanType) where
  astSpanP :: Proxy s -> AstSpanType

instance AstSpan AstPrimal where
  astSpanP _ = AstPrimal

instance AstSpan AstDual where
  astSpanP _ = AstDual

instance AstSpan AstFull where
  astSpanP _ = AstFull

astSpanT :: forall s. AstSpan s => AstSpanType
{-# INLINE astSpanT #-}
astSpanT = astSpanP (Proxy :: Proxy s)

sameAstSpan :: forall s1 s2. (AstSpan s1, AstSpan s2) => Maybe (s1 :~: s2)
sameAstSpan = case eqTypeRep (typeRep @s1) (typeRep @s2) of
                Just HRefl -> Just Refl
                Nothing -> Nothing

type instance RankedOf (Clown (AstDynamic s)) = AstRanked s
type instance ShapedOf (Clown (AstDynamic s)) = AstShaped s
type instance RankedOf (AstRanked s) = AstRanked s
type instance ShapedOf (AstRanked s) = AstShaped s
type instance PrimalOf (AstRanked s) = AstPrimalPart s  -- AstRanked AstPrimal
type instance DualOf (AstRanked s) = AstDualPart s
-- type instance DualOf (AstRanked AstFull) = AstRanked AstDual
-- type instance DualOf (AstRanked AstPrimal) = DummyDual
type instance RankedOf (AstShaped s) = AstRanked s
type instance ShapedOf (AstShaped s) = AstShaped s
type instance PrimalOf (AstShaped s) = AstPrimalPartS s  -- AstShaped AstPrimal
type instance DualOf (AstShaped s) = AstDualPartS s
-- type instance DualOf (AstShaped AstFull) = AstShaped AstDual
-- type instance DualOf (AstShaped AstPrimal) = DummyDual

-- TODO: remove
type instance RankedOf (AstPrimalPart s) = AstPrimalPart s
type instance ShapedOf (AstPrimalPart s) = AstPrimalPartS s
type instance PrimalOf (AstPrimalPart s) = AstPrimalPart s
type instance DualOf (AstPrimalPart s) = DummyDual
type instance RankedOf (AstPrimalPartS s) = AstPrimalPart s
type instance ShapedOf (AstPrimalPartS s) = AstPrimalPartS s
type instance PrimalOf (AstPrimalPartS s) = AstPrimalPartS s
type instance DualOf (AstPrimalPartS s) = DummyDual


-- * Assorted small definitions

type AstInt = AstPrimalPart AstPrimal Int64 0

pattern AstIntVar :: AstVarId -> AstInt
pattern AstIntVar var = AstPrimalPart (AstVar ZS var)

pattern AstPVar :: AstVarId -> AstPrimalPart s r n
pattern AstPVar var <- AstPrimalPart (AstVar _ var)

pattern AstIntConst :: OR.Array 0 Int64 -> AstInt
pattern AstIntConst i = AstPrimalPart (AstConst i)

pattern AstPConst :: OR.Array n r -> AstPrimalPart s r n
pattern AstPConst r = AstPrimalPart (AstConst r)

-- | The type family that to a concrete tensor type assigns its
-- corresponding AST type.
type AstOf :: forall k. TensorKind k -> TensorKind k
type family AstOf f = result | result -> f where
  AstOf (Clown OD.Array) = Clown (AstDynamic AstPrimal)
  AstOf (Flip OR.Array) = AstRanked AstPrimal
  AstOf (Flip OS.Array) = AstShaped AstPrimal

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
type ADAstArtifact6 f s r y =
  ( (AstVarName (f r y), [AstDynamicVarName]), AstDomains s
  , PrimalOf (AstOf f) r y )

type AstIndex n = Index n AstInt

type AstVarList n = SizedList n AstVarId

type AstIndexS sh = ShapedList sh AstInt

type AstVarListS sh = ShapedList sh AstVarId


-- * ASTs

-- | AST for ranked tensors that are meant to be differentiated.
--
-- We use here @ShapeInt@ for simplicity. @Shape n AstInt@ gives
-- more expressiveness, but leads to irregular tensors,
-- especially after vectorization, and prevents static checking of shapes.
data AstRanked :: AstSpanType -> RankedTensorKind where
  -- To permit defining objective functions in Ast, not just constants:
  AstVar :: ShapeInt n -> AstVarId -> AstRanked s r n
  AstLet :: (KnownNat n, KnownNat m, GoodScalar r)
         => AstVarId -> AstRanked s r n -> AstRanked s r2 m -> AstRanked s r2 m
  AstLetADShare :: ADShare -> AstRanked AstPrimal r n -> AstRanked AstPrimal r n
   -- there are mixed local/global lets, because they can be identical
   -- to the lets stored in the D constructor and so should not be inlined
   -- even in trivial cases until the transpose pass eliminates D

  -- For the numeric classes:
  AstNm :: OpCodeNum -> [AstRanked s r n] -> AstRanked s r n
             -- name of the same length as AstOp for tests
  AstOp :: Differentiable r
        => OpCode -> [AstRanked s r n] -> AstRanked s r n
  AstOpIntegral :: Integral r
                => OpCodeIntegral -> [AstRanked s r n] -> AstRanked s r n
  AstSumOfList :: [AstRanked s r n] -> AstRanked s r n
  AstIota :: AstRanked s r 1

  -- For the Tensor class:
  AstIndex :: forall m n r s. KnownNat m
           => AstRanked s r (m + n) -> AstIndex m -> AstRanked s r n
    -- first ix is for outermost dimension; empty index means identity,
    -- if index is out of bounds, the result is defined and is 0,
    -- but vectorization is permitted to change the value
  AstSum :: AstRanked s r (1 + n) -> AstRanked s r n
  AstScatter :: forall m n p r s. (KnownNat m, KnownNat n, KnownNat p)
             => ShapeInt (p + n)
             -> AstRanked s r (m + n) -> (AstVarList m, AstIndex p)
             -> AstRanked s r (p + n)

  AstFromList :: KnownNat n
              => [AstRanked s r n] -> AstRanked s r (1 + n)
  AstFromVector :: KnownNat n
                => Data.Vector.Vector (AstRanked s r n) -> AstRanked s r (1 + n)
  AstReplicate :: KnownNat n
               => Int -> AstRanked s r n -> AstRanked s r (1 + n)
  AstAppend :: KnownNat n
            => AstRanked s r (1 + n) -> AstRanked s r (1 + n)
            -> AstRanked s r (1 + n)
  AstSlice :: KnownNat n
           => Int -> Int -> AstRanked s r (1 + n) -> AstRanked s r (1 + n)
  AstReverse :: KnownNat n
             => AstRanked s r (1 + n) -> AstRanked s r (1 + n)
  AstTranspose :: Permutation -> AstRanked s r n -> AstRanked s r n
  AstReshape :: KnownNat n
             => ShapeInt m -> AstRanked s r n -> AstRanked s r m
  AstBuild1 :: KnownNat n
            => Int -> (AstVarId, AstRanked s r n) -> AstRanked s r (1 + n)
  AstGather :: forall m n p r s. (KnownNat m, KnownNat n, KnownNat p)
            => ShapeInt (m + n)
            -> AstRanked s r (p + n) -> (AstVarList m, AstIndex p)
            -> AstRanked s r (m + n)
    -- out of bounds indexing is permitted
  AstCast :: (GoodScalar r1, RealFrac r1, RealFrac r2)
          => AstRanked s r1 n -> AstRanked s r2 n
  AstFromIntegral :: (GoodScalar r1, Integral r1)
                  => AstPrimalPart s r1 n -> AstRanked s r2 n

  AstSToR :: OS.Shape sh
          => AstShaped s r sh -> AstRanked s r (OS.Rank sh)

  -- For the forbidden half of the Tensor class:
  AstConst :: OR.Array n r -> AstRanked s r n
  AstConstant :: AstPrimalPart s r n -> AstRanked s r n
  AstD :: AstPrimalPart s r n -> AstDualPart s r n -> AstRanked s r n
  AstLetDomains :: Data.Vector.Vector AstVarId -> AstDomains s
                -> AstRanked s r n
                -> AstRanked s r n

  AstCond :: AstBool
          -> AstRanked s r n -> AstRanked s r n -> AstRanked s r n
  -- Morally these should live in AstPrimalPart, but that would complicate
  -- things, so they are least have AstPrimalPart domains, which often makes
  -- it possible to simplify terms, e.g., deleting AstDualPart applications.
  AstFloor :: (GoodScalar r, RealFrac r, Integral r2)
           => AstPrimalPart s r n -> AstRanked s r2 n
  AstMinIndex :: GoodScalar r
              => AstPrimalPart s r (1 + n) -> AstRanked s r2 n
  AstMaxIndex :: GoodScalar r
              => AstPrimalPart s r (1 + n) -> AstRanked s r2 n

deriving instance GoodScalar r => Show (AstRanked s r n)

newtype AstPrimalPart s r n =
  AstPrimalPart {unAstPrimalPart :: AstRanked s r n}
deriving instance GoodScalar r => Show (AstPrimalPart s r n)

newtype AstDualPart s r n =
  AstDualPart {unAstDualPart :: AstRanked s r n}
deriving instance GoodScalar r => Show (AstDualPart s r n)

-- | AST for shaped tensors that are meant to be differentiated.
data AstShaped :: AstSpanType -> ShapedTensorKind where
  -- To permit defining objective functions in Ast, not just constants:
  AstVarS :: forall sh r s. AstVarId -> AstShaped s r sh
  AstLetS :: (OS.Shape sh, OS.Shape sh2, GoodScalar r)
          => AstVarId -> AstShaped s r sh -> AstShaped s r2 sh2
          -> AstShaped s r2 sh2
  AstLetADShareS :: ADShare -> AstShaped AstPrimal r sh -> AstShaped AstPrimal r sh
   -- there are mixed local/global lets, because they can be identical
   -- to the lets stored in the D constructor and so should not be inlined
   -- even in trivial cases until the transpose pass eliminates D

  -- For the numeric classes:
  AstNmS :: OpCodeNum -> [AstShaped s r sh] -> AstShaped s r sh
  AstOpS :: Differentiable r
         => OpCode -> [AstShaped s r sh] -> AstShaped s r sh
  AstOpIntegralS :: Integral r
                 => OpCodeIntegral -> [AstShaped s r sh] -> AstShaped s r sh
  AstSumOfListS :: [AstShaped s r sh] -> AstShaped s r sh
  AstIotaS :: forall n r s. KnownNat n => AstShaped s r '[n]

  -- For the Tensor class:
  AstIndexS :: forall sh1 sh2 s r.
               (OS.Shape sh1, OS.Shape sh2, OS.Shape (sh1 OS.++ sh2))
            => AstShaped s r (sh1 OS.++ sh2) -> AstIndexS sh1
            -> AstShaped s r sh2
    -- first ix is for outermost dimension; empty index means identity,
    -- if index is out of bounds, the result is defined and is 0,
    -- but vectorization is permitted to change the value
  AstSumS :: KnownNat n
          => AstShaped s r (n ': sh) -> AstShaped s r sh
  AstScatterS :: forall sh2 p sh r s.
                 ( OS.Shape sh2, OS.Shape sh
                 , OS.Shape (OS.Take p sh), OS.Shape (OS.Drop p sh)
                 , OS.Shape (sh2 OS.++ OS.Drop p sh) )
              => AstShaped s r (sh2 OS.++ OS.Drop p sh)
              -> (AstVarListS sh2, AstIndexS (OS.Take p sh))
              -> AstShaped s r sh

  AstFromListS :: (KnownNat n, OS.Shape sh)
               => [AstShaped s r sh] -> AstShaped s r (n ': sh)
  AstFromVectorS :: (KnownNat n, OS.Shape sh)
                 => Data.Vector.Vector (AstShaped s r sh)
                 -> AstShaped s r (n ': sh)
  AstReplicateS :: (KnownNat n, OS.Shape sh)
                => AstShaped s r sh -> AstShaped s r (n ': sh)
  AstAppendS :: (KnownNat n, KnownNat m, OS.Shape sh)
             => AstShaped s r (m ': sh) -> AstShaped s r (n ': sh)
             -> AstShaped s r ((m + n) ': sh)
  AstSliceS :: (KnownNat i, KnownNat n, KnownNat k, OS.Shape sh)
            => AstShaped s r (i + n + k ': sh) -> AstShaped s r (n ': sh)
  AstReverseS :: (KnownNat n, OS.Shape sh)
              => AstShaped s r (n ': sh) -> AstShaped s r (n ': sh)
  AstTransposeS :: forall perm sh r s.
                   ( OS.Permutation perm, OS.Shape perm, OS.Shape sh
                   , KnownNat (OS.Rank sh), OS.Rank perm <= OS.Rank sh )
                => AstShaped s r sh -> AstShaped s r (OS.Permute perm sh)
  AstReshapeS :: (OS.Shape sh, OS.Size sh ~ OS.Size sh2)
              => AstShaped s r sh -> AstShaped s r sh2
    -- beware that the order of type arguments is different than in orthotope
    -- and than the order of value arguments in the ranked version
  AstBuild1S :: (KnownNat n, OS.Shape sh)
             => (AstVarId, AstShaped s r sh) -> AstShaped s r (n ': sh)
  AstGatherS :: forall sh2 p sh r s.
                ( OS.Shape sh, OS.Shape sh2
                , OS.Shape (OS.Take p sh), OS.Shape (OS.Drop p sh) )
             => AstShaped s r sh
             -> (AstVarListS sh2, AstIndexS (OS.Take p sh))
             -> AstShaped s r (sh2 OS.++ OS.Drop p sh)
    -- out of bounds indexing is permitted
  AstCastS :: (GoodScalar r1, RealFrac r1, RealFrac r2)
           => AstShaped s r1 sh -> AstShaped s r2 sh
  AstFromIntegralS :: (GoodScalar r1, Integral r1)
                   => AstPrimalPartS s r1 sh -> AstShaped s r2 sh

  AstRToS :: (OS.Shape sh, KnownNat (OS.Rank sh))
          => AstRanked s r (OS.Rank sh) -> AstShaped s r sh

  -- For the forbidden half of the Tensor class:
  AstConstS :: OS.Array sh r -> AstShaped s r sh
  AstConstantS :: AstPrimalPartS s r sh -> AstShaped s r sh
  AstDS :: AstPrimalPartS s r sh -> AstDualPartS s r sh -> AstShaped s r sh
  AstLetDomainsS :: Data.Vector.Vector AstVarId -> AstDomains s
                 -> AstShaped s r sh
                 -> AstShaped s r sh

  AstCondS :: AstBool
           -> AstShaped s r sh -> AstShaped s r sh -> AstShaped s r sh
  -- Morally these should live in AstPrimalPartS, but that would complicate
  -- things, so they are least have AstPrimalPartS domains, which often makes
  -- it possible to simplify terms, e.g., deleting AstDualPartS applications.
  AstFloorS :: (GoodScalar r, RealFrac r, Integral r2)
            => AstPrimalPartS s r sh -> AstShaped s r2 sh
  AstMinIndexS :: (OS.Shape sh, KnownNat n, GoodScalar r)
               => AstPrimalPartS s r (n ': sh)
               -> AstShaped s r2 (OS.Init (n ': sh))
  AstMaxIndexS :: (OS.Shape sh, KnownNat n, GoodScalar r)
               => AstPrimalPartS s r (n ': sh)
               -> AstShaped s r2 (OS.Init (n ': sh))

deriving instance (GoodScalar r, OS.Shape sh) => Show (AstShaped s r sh)

newtype AstPrimalPartS s r sh =
  AstPrimalPartS {unAstPrimalPartS :: AstShaped s r sh}
deriving instance (GoodScalar r, OS.Shape sh) => Show (AstPrimalPartS s r sh)

newtype AstDualPartS s r sh =
  AstDualPartS {unAstDualPartS :: AstShaped s r sh}
deriving instance (GoodScalar r, OS.Shape sh) => Show (AstDualPartS s r sh)

data AstDynamic :: AstSpanType -> Type -> Type where
  AstRToD :: KnownNat n
          => AstRanked s r n -> AstDynamic s r
  AstSToD :: OS.Shape sh
          => AstShaped s r sh -> AstDynamic s r
deriving instance GoodScalar r => Show (AstDynamic s r)

data AstDomains s where
  AstDomains :: Data.Vector.Vector (DynamicExists (AstDynamic s))
             -> AstDomains s
  AstDomainsLet :: (KnownNat n, GoodScalar r)
                => AstVarId -> AstRanked s r n -> AstDomains s
                -> AstDomains s
  AstDomainsLetS :: (OS.Shape sh, GoodScalar r)
                 => AstVarId -> AstShaped s r sh -> AstDomains s
                 -> AstDomains s
deriving instance Show (AstDomains s)

data AstBool where
  AstBoolOp :: OpCodeBool -> [AstBool] -> AstBool
  AstBoolConst :: Bool -> AstBool
  AstRel :: (KnownNat n, GoodScalar r, AstSpan s)
         => OpCodeRel -> [AstPrimalPart s r n] -> AstBool
  AstRelS :: (OS.Shape sh, GoodScalar r, AstSpan s)
          => OpCodeRel -> [AstPrimalPartS s r sh] -> AstBool
deriving instance Show AstBool

data OpCodeNum =
    MinusOp | TimesOp | NegateOp | AbsOp | SignumOp
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

data OpCodeBool =
    NotOp | AndOp | OrOp
 deriving Show

data OpCodeRel =
    EqOp | NeqOp
  | LeqOp| GeqOp | LsOp | GtOp
 deriving Show


-- * Unlawful instances of AST for bool; they are lawful modulo evaluation

instance Boolean AstBool where
  true = AstBoolConst True
  false = AstBoolConst False
  notB b = AstBoolOp NotOp [b]
  AstBoolConst b &&* AstBoolConst c = AstBoolConst $ b && c
                                        -- common in indexing
  b &&* c = AstBoolOp AndOp [b, c]
  b ||* c = AstBoolOp OrOp [b, c]


-- * Unlawful boolean instances of ranked AST; they are lawful modulo evaluation

type instance BoolOf (AstRanked s) = AstBool

instance IfF (AstRanked s) where
  ifF = astCond

-- No simplification yet done at this point, so AstBoolConst unlikely,
-- but it's a constant time simplification, so no harm done.
-- The AstConstant is more helpful, making Delta expressions smaller.
-- A stronger version of this function is in AstSimplify.
astCond :: AstBool -> AstRanked s r n -> AstRanked s r n -> AstRanked s r n
astCond (AstBoolConst b) v w = if b then v else w
astCond b (AstConstant (AstPrimalPart v))
          (AstConstant (AstPrimalPart w)) =
  AstConstant $ astPrimalPart $ AstCond b v w
astCond b v w = AstCond b v w

astPrimalPart :: AstRanked s r n -> AstPrimalPart s r n
astPrimalPart (AstConstant t) = t
astPrimalPart t = AstPrimalPart t

instance AstSpan s => EqF (AstRanked s) where
  v ==. u = AstRel EqOp [astPrimalPart v, astPrimalPart u]
  v /=. u = AstRel NeqOp [astPrimalPart v, astPrimalPart u]

instance AstSpan s => OrdF (AstRanked s) where
  AstConst u <. AstConst v = AstBoolConst $ u < v  -- common in indexing
  v <. u = AstRel LsOp [astPrimalPart v, astPrimalPart u]
  AstConst u <=. AstConst v = AstBoolConst $ u <= v  -- common in indexing
  v <=. u = AstRel LeqOp [astPrimalPart v, astPrimalPart u]
  AstConst u >. AstConst v = AstBoolConst $ u > v  -- common in indexing
  v >. u = AstRel GtOp [astPrimalPart v, astPrimalPart u]
  AstConst u >=. AstConst v = AstBoolConst $ u >= v  -- common in indexing
  v >=. u = AstRel GeqOp [astPrimalPart v, astPrimalPart u]

type instance BoolOf (AstPrimalPart s) = AstBool

deriving instance IfF (AstPrimalPart s)
deriving instance AstSpan s => EqF (AstPrimalPart s)
deriving instance AstSpan s => OrdF (AstPrimalPart s)


-- * Unlawful numeric instances of ranked AST; they are lawful modulo evaluation

-- These are, unfortunately, required by some numeric instances.
instance Eq (AstRanked s r n) where
  (==) = error "AST requires that EqF be used instead"
  (/=) = error "AST requires that EqF be used instead"

instance Ord (AstRanked s r n) where
  (<=) = error "AST requires that OrdF be used instead"

instance Num (OR.Array n r) => Num (AstRanked s r n) where
  -- The normal form has AstConst, if any, as the first element of the list
  -- all lists fully flattened and length >= 2.
  AstSumOfList (AstConst u : lu) + AstSumOfList (AstConst v : lv) =
    AstSumOfList (AstConst (u + v) : lu ++ lv)
  AstSumOfList lu + AstSumOfList (AstConst v : lv) =
    AstSumOfList (AstConst v : lv ++ lu)
  AstSumOfList lu + AstSumOfList lv = AstSumOfList (lu ++ lv)

  AstConst u + AstSumOfList (AstConst v : lv) =
    AstSumOfList (AstConst (u + v) : lv)
  u + AstSumOfList (AstConst v : lv) = AstSumOfList (AstConst v : u : lv)
  u + AstSumOfList lv = AstSumOfList (u : lv)

  AstSumOfList (AstConst u : lu) + AstConst v =
    AstSumOfList (AstConst (u + v) : lu)
  AstSumOfList (AstConst u : lu) + v = AstSumOfList (AstConst u : v : lu)
  AstSumOfList lu + v = AstSumOfList (v : lu)

  AstConst u + AstConst v = AstConst (u + v)
  u + AstConst v = AstSumOfList [AstConst v, u]
  u + v = AstSumOfList [u, v]

  AstConst u - AstConst v = AstConst (u - v)  -- common in indexing
  u - v = AstNm MinusOp [u, v]
  AstConst u * AstConst v = AstConst (u * v)  -- common in indexing
  u * v = AstNm TimesOp [u, v]
    -- no hacks like for AstSumOfList, because when tscaleByScalar
    -- is reconstructed, it looks for the binary form
  negate (u) = AstNm NegateOp [u]
  abs (v) = AstNm AbsOp [v]
  signum (v) = AstNm SignumOp [v]
  fromInteger = AstConstant . AstPrimalPart . AstConst . fromInteger
    -- it's crucial that there is no AstConstant in fromInteger code
    -- so that we don't need 4 times the simplification rules

instance (Real (OR.Array n r))
         => Real (AstRanked s r n) where
  toRational = undefined
    -- very low priority, since these are all extremely not continuous

instance Enum r => Enum (AstRanked s r n) where
  toEnum = undefined  -- AstConst . OR.scalar . toEnum
  fromEnum = undefined  -- do we need to define our own Enum for this?

-- Warning: div and mod operations are very costly (simplifying them
-- requires constructing conditionals, etc). If this error is removed,
-- they are going to work, but slowly.
instance (Integral r, Integral (OR.Array n r))
         => Integral (AstRanked s r n) where
  quot u v = AstOpIntegral QuotOp [u, v]
  rem u v = AstOpIntegral RemOp [u, v]
  quotRem u v = (AstOpIntegral QuotOp [u, v], AstOpIntegral RemOp [u, v])
  divMod _ _ = error "divMod: disabled; much less efficient than quot and rem"
  toInteger = undefined  -- we can't evaluate uninstantiated variables, etc.

instance (Differentiable r, Fractional (OR.Array n r))
         => Fractional (AstRanked s r n) where
  u / v = AstOp DivideOp  [u, v]
  recip v = AstOp RecipOp [v]
  fromRational = AstConstant . AstPrimalPart . AstConst . fromRational

instance (Differentiable r, Floating (OR.Array n r))
         => Floating (AstRanked s r n) where
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

instance (Differentiable r, RealFrac (OR.Array n r))
         => RealFrac (AstRanked s r n) where
  properFraction = undefined
    -- The integral type doesn't have a Storable constraint,
    -- so we can't implement this (nor RealFracB from Boolean package).

instance (Differentiable r, RealFloat (OR.Array n r))
         => RealFloat (AstRanked s r n) where
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

instance Eq (AstPrimalPart s r n) where
  (==) = error "AST requires that EqF be used instead"
  (/=) = error "AST requires that EqF be used instead"

instance Ord (AstPrimalPart s r n) where
  (<=) = error "AST requires that OrdF be used instead"

instance (Num (AstRanked s r n), Num (OR.Array n r))
         => Num (AstPrimalPart s r n) where
  (AstPrimalPart u) + (AstPrimalPart v) = AstPrimalPart $ u + v
  (AstPrimalPart u) - (AstPrimalPart v) = AstPrimalPart $ u - v
  (AstPrimalPart u) * (AstPrimalPart v) = AstPrimalPart $ u * v
  negate (AstPrimalPart u) = AstPrimalPart $ negate u
  abs (AstPrimalPart v) = AstPrimalPart $ abs v
  signum (AstPrimalPart v) = AstPrimalPart $ signum v
  fromInteger = AstPrimalPart . AstConst . fromInteger

instance (Fractional (AstRanked s r n), Fractional (OR.Array n r))
         => Fractional (AstPrimalPart s r n) where
  (AstPrimalPart u) / (AstPrimalPart v) = AstPrimalPart $ u / v
  recip (AstPrimalPart v) = AstPrimalPart $ recip v
  fromRational = AstPrimalPart . AstConst . fromRational

deriving instance (Real (AstRanked s r n), Num (OR.Array n r))
                  => Real (AstPrimalPart s r n)
deriving instance (Enum (AstRanked s r n)) => Enum (AstPrimalPart s r n)
deriving instance (Integral (AstRanked s r n), Num (OR.Array n r))
                  => Integral (AstPrimalPart s r n)
deriving instance (Floating (AstRanked s r n), Floating (OR.Array n r))
                  => Floating (AstPrimalPart s r n)
deriving instance (RealFrac (AstRanked s r n), RealFrac (OR.Array n r))
                  => RealFrac (AstPrimalPart s r n)
deriving instance (RealFloat (AstRanked s r n), RealFloat (OR.Array n r))
                  => RealFloat (AstPrimalPart s r n)


-- * Unlawful boolean instances of shaped AST; they are lawful modulo evaluation

type instance BoolOf (AstShaped s) = AstBool

instance IfF (AstShaped s) where
  ifF = astCondS

-- No simplification yet done at this point, so AstBoolConst unlikely,
-- but it's a constant time simplification, so no harm done.
-- The AstConstant is more helpful, making Delta expressions smaller.
-- A stronger version of this function is in AstSimplify.
astCondS :: AstBool -> AstShaped s r sh -> AstShaped s r sh -> AstShaped s r sh
astCondS (AstBoolConst b) v w = if b then v else w
astCondS b (AstConstantS (AstPrimalPartS v))
           (AstConstantS (AstPrimalPartS w)) =
  AstConstantS $ astPrimalPartS $ AstCondS b v w
astCondS b v w = AstCondS b v w

astPrimalPartS :: AstShaped s r n -> AstPrimalPartS s r n
astPrimalPartS (AstConstantS t) = t
astPrimalPartS t = AstPrimalPartS t

instance AstSpan s => EqF (AstShaped s) where
  v ==. u = AstRelS EqOp [astPrimalPartS v, astPrimalPartS u]
  v /=. u = AstRelS NeqOp [astPrimalPartS v, astPrimalPartS u]

instance AstSpan s => OrdF (AstShaped s) where
  AstConstS u <. AstConstS v = AstBoolConst $ u < v  -- common in indexing
  v <. u = AstRelS LsOp [astPrimalPartS v, astPrimalPartS u]
  AstConstS u <=. AstConstS v = AstBoolConst $ u <= v  -- common in indexing
  v <=. u = AstRelS LeqOp [astPrimalPartS v, astPrimalPartS u]
  AstConstS u >. AstConstS v = AstBoolConst $ u > v  -- common in indexing
  v >. u = AstRelS GtOp [astPrimalPartS v, astPrimalPartS u]
  AstConstS u >=. AstConstS v = AstBoolConst $ u >= v  -- common in indexing
  v >=. u = AstRelS GeqOp [astPrimalPartS v, astPrimalPartS u]

type instance BoolOf (AstPrimalPartS s) = AstBool

deriving instance IfF (AstPrimalPartS s)
deriving instance AstSpan s => EqF (AstPrimalPartS s)
deriving instance AstSpan s => OrdF (AstPrimalPartS s)


-- * Unlawful numeric instances of shaped AST; they are lawful modulo evaluation

instance Eq (AstShaped s r sh) where
  (==) = error "AST requires that EqF be used instead"
  (/=) = error "AST requires that EqF be used instead"

instance Ord (AstShaped s r sh) where
  (<=) = error "AST requires that OrdF be used instead"

instance Num (OS.Array sh r) => Num (AstShaped s r sh) where
  -- The normal form has AstConst, if any, as the first element of the list
  -- all lists fully flattened and length >= 2.
  AstSumOfListS (AstConstS u : lu) + AstSumOfListS (AstConstS v : lv) =
    AstSumOfListS (AstConstS (u + v) : lu ++ lv)
  AstSumOfListS lu + AstSumOfListS (AstConstS v : lv) =
    AstSumOfListS (AstConstS v : lv ++ lu)
  AstSumOfListS lu + AstSumOfListS lv = AstSumOfListS (lu ++ lv)

  AstConstS u + AstSumOfListS (AstConstS v : lv) =
    AstSumOfListS (AstConstS (u + v) : lv)
  u + AstSumOfListS (AstConstS v : lv) = AstSumOfListS (AstConstS v : u : lv)
  u + AstSumOfListS lv = AstSumOfListS (u : lv)

  AstSumOfListS (AstConstS u : lu) + AstConstS v =
    AstSumOfListS (AstConstS (u + v) : lu)
  AstSumOfListS (AstConstS u : lu) + v = AstSumOfListS (AstConstS u : v : lu)
  AstSumOfListS lu + v = AstSumOfListS (v : lu)

  AstConstS u + AstConstS v = AstConstS (u + v)
  u + AstConstS v = AstSumOfListS [AstConstS v, u]
  u + v = AstSumOfListS [u, v]

  AstConstS u - AstConstS v = AstConstS (u - v)  -- common in indexing
  u - v = AstNmS MinusOp [u, v]
  AstConstS u * AstConstS v = AstConstS (u * v)  -- common in indexing
  u * v = AstNmS TimesOp [u, v]
    -- no hacks like for AstSumOfList, because when tscaleByScalar
    -- is reconstructed, it looks for the binary form
  negate (u) = AstNmS NegateOp [u]
  abs (v) = AstNmS AbsOp [v]
  signum (v) = AstNmS SignumOp [v]
  fromInteger = AstConstantS . AstPrimalPartS . AstConstS . fromInteger
    -- it's crucial that there is no AstConstant in fromInteger code
    -- so that we don't need 4 times the simplification rules

instance (Real (OS.Array sh r)) => Real (AstShaped s r sh) where
  toRational = undefined
    -- very low priority, since these are all extremely not continuous

instance Enum r => Enum (AstShaped s r n) where
  toEnum = undefined
  fromEnum = undefined  -- do we need to define our own Enum for this?

-- Warning: div and mod operations are very costly (simplifying them
-- requires constructing conditionals, etc). If this error is removed,
-- they are going to work, but slowly.
instance (Integral r, Integral (OS.Array sh r))
         => Integral (AstShaped s r sh) where
  quot u v = AstOpIntegralS QuotOp [u, v]
  rem u v = AstOpIntegralS RemOp [u, v]
  quotRem u v = (AstOpIntegralS QuotOp [u, v], AstOpIntegralS RemOp [u, v])
  divMod _ _ = error "divMod: disabled; much less efficient than quot and rem"
  toInteger = undefined  -- we can't evaluate uninstantiated variables, etc.

instance (Differentiable r, Fractional (OS.Array sh r))
         => Fractional (AstShaped s r sh) where
  u / v = AstOpS DivideOp  [u, v]
  recip v = AstOpS RecipOp [v]
  fromRational = AstConstantS . AstPrimalPartS . AstConstS . fromRational

instance (Differentiable r, Floating (OS.Array sh r))
         => Floating (AstShaped s r sh) where
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

instance (Differentiable r, RealFrac (OS.Array sh r))
         => RealFrac (AstShaped s r sh) where
  properFraction = undefined
    -- The integral type doesn't have a Storable constraint,
    -- so we can't implement this (nor RealFracB from Boolean package).

instance (Differentiable r, RealFloat (OS.Array sh r))
         => RealFloat (AstShaped s r sh) where
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

instance Eq (AstPrimalPartS s r sh) where
  (==) = error "AST requires that EqF be used instead"
  (/=) = error "AST requires that EqF be used instead"

instance Ord (AstPrimalPartS s r sh) where
  (<=) = error "AST requires that OrdF be used instead"

instance (Num (AstShaped s r sh), Num (OS.Array sh r))
         => Num (AstPrimalPartS s r sh) where
  (AstPrimalPartS u) + (AstPrimalPartS v) = AstPrimalPartS $ u + v
  (AstPrimalPartS u) - (AstPrimalPartS v) = AstPrimalPartS $ u - v
  (AstPrimalPartS u) * (AstPrimalPartS v) = AstPrimalPartS $ u * v
  negate (AstPrimalPartS u) = AstPrimalPartS $ negate u
  abs (AstPrimalPartS v) = AstPrimalPartS $ abs v
  signum (AstPrimalPartS v) = AstPrimalPartS $ signum v
  fromInteger = AstPrimalPartS . AstConstS . fromInteger

instance (Fractional (AstShaped s r sh), Fractional (OS.Array sh r))
         => Fractional (AstPrimalPartS s r sh) where
  (AstPrimalPartS u) / (AstPrimalPartS v) = AstPrimalPartS $ u / v
  recip (AstPrimalPartS v) = AstPrimalPartS $ recip v
  fromRational = AstPrimalPartS . AstConstS . fromRational

deriving instance (Real (AstShaped s r sh), Num (OS.Array sh r))
                  => Real (AstPrimalPartS s r sh)
deriving instance Enum (AstShaped s r sh) => Enum (AstPrimalPartS s r sh)
deriving instance (Integral (AstShaped s r sh), Num (OS.Array sh r))
                  => Integral (AstPrimalPartS s r sh)
deriving instance (Floating (AstShaped s r sh), Floating (OS.Array sh r))
                  => Floating (AstPrimalPartS s r sh)
deriving instance (RealFrac (AstShaped s r sh), RealFrac (OS.Array sh r))
                  => RealFrac (AstPrimalPartS s r sh)
deriving instance (RealFloat (AstShaped s r sh), RealFloat (OS.Array sh r))
                  => RealFloat (AstPrimalPartS s r sh)


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
               => ADShareCons Int AstVarId (AstDynamic AstPrimal r) ADShare
deriving instance Show ADShare

emptyADShare :: ADShare
emptyADShare = ADShareNil

insertADShare :: forall r. GoodScalar r
              => AstVarId -> AstDynamic AstPrimal r -> ADShare -> ADShare
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

freshInsertADShare :: GoodScalar r => AstVarId -> AstDynamic AstPrimal r -> ADShare
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
subtractADShare :: ADShare -> ADShare
                -> [(AstVarId, DynamicExists (AstDynamic AstPrimal))]
{-# INLINE subtractADShare #-}  -- help list fusion
subtractADShare !s1 !s2 =
  let subAD :: ADShare -> ADShare -> [(AstVarId, DynamicExists (AstDynamic AstPrimal))]
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

assocsADShare :: ADShare -> [(AstVarId, DynamicExists (AstDynamic AstPrimal))]
{-# INLINE assocsADShare #-}  -- help list fusion
assocsADShare ADShareNil = []
assocsADShare (ADShareCons _ key t rest) =
  (key, DynamicExists t) : assocsADShare rest

_lengthADShare :: Int -> ADShare -> Int
_lengthADShare acc ADShareNil = acc
_lengthADShare acc (ADShareCons _ _ _ rest) = _lengthADShare (acc + 1) rest

intVarInADShare :: (forall r. AstVarId -> AstDynamic AstPrimal r -> Bool)
                -> AstVarId -> ADShare
                -> Bool
{-# INLINE intVarInADShare #-}
intVarInADShare _ _ ADShareNil = False
intVarInADShare intVarInAstDynamic var (ADShareCons _ _ d rest) =
  intVarInAstDynamic var d || intVarInADShare intVarInAstDynamic var rest
    -- TODO: for good Core, probably a local recursive 'go' is needed

nullADShare :: ADShare -> Bool
{-# INLINE nullADShare #-}
nullADShare ADShareNil = True
nullADShare ADShareCons{} = False


-- * The auxiliary AstNoVectorize and AstNoSimplify definitions, for tests

type instance RankedOf AstNoVectorize = AstNoVectorize
type instance ShapedOf AstNoVectorize = AstShaped AstPrimal
type instance PrimalOf AstNoVectorize = AstPrimalPart AstPrimal
type instance DualOf AstNoVectorize = AstDualPart AstPrimal
type instance RankedOf AstNoSimplify = AstNoSimplify
type instance ShapedOf AstNoSimplify = AstShaped AstPrimal
type instance PrimalOf AstNoSimplify = AstPrimalPart AstPrimal
type instance DualOf AstNoSimplify = AstDualPart AstPrimal

newtype AstNoVectorize r n =
  AstNoVectorize {unAstNoVectorize :: AstRanked AstPrimal r n}
deriving instance GoodScalar r => Show (AstNoVectorize r n)

type instance BoolOf AstNoVectorize = AstBool

deriving instance IfF AstNoVectorize
deriving instance EqF AstNoVectorize
deriving instance OrdF AstNoVectorize
deriving instance Eq (AstNoVectorize r n)
deriving instance Ord (AstNoVectorize r n)
deriving instance Num (AstRanked AstPrimal r n) => Num (AstNoVectorize r n)
deriving instance (Real (AstRanked AstPrimal r n))
                   => Real (AstNoVectorize r n)
deriving instance Enum (AstRanked AstPrimal r n) => Enum (AstNoVectorize r n)
deriving instance (Integral (AstRanked AstPrimal r n))
                  => Integral (AstNoVectorize r n)
deriving instance Fractional (AstRanked AstPrimal r n)
                  => Fractional (AstNoVectorize r n)
deriving instance Floating (AstRanked AstPrimal r n) => Floating (AstNoVectorize r n)
deriving instance (RealFrac (AstRanked AstPrimal r n))
                  => RealFrac (AstNoVectorize r n)
deriving instance (RealFloat (AstRanked AstPrimal r n))
                  => RealFloat (AstNoVectorize r n)

newtype AstNoSimplify r n =
  AstNoSimplify {unAstNoSimplify :: AstRanked AstPrimal r n}
deriving instance GoodScalar r => Show (AstNoSimplify r n)

type instance BoolOf AstNoSimplify = AstBool

deriving instance IfF AstNoSimplify
deriving instance EqF AstNoSimplify
deriving instance OrdF AstNoSimplify
deriving instance Eq (AstNoSimplify r n)
deriving instance Ord (AstNoSimplify r n)
deriving instance Num (AstRanked AstPrimal r n) => Num (AstNoSimplify r n)
deriving instance (Real (AstRanked AstPrimal r n))
                  => Real (AstNoSimplify r n)
deriving instance Enum (AstRanked AstPrimal r n) => Enum (AstNoSimplify r n)
deriving instance (Integral (AstRanked AstPrimal r n))
                  => Integral (AstNoSimplify r n)
deriving instance Fractional (AstRanked AstPrimal r n) => Fractional (AstNoSimplify r n)
deriving instance Floating (AstRanked AstPrimal r n) => Floating (AstNoSimplify r n)
deriving instance (RealFrac (AstRanked AstPrimal r n))
                  => RealFrac (AstNoSimplify r n)
deriving instance (RealFloat (AstRanked AstPrimal r n))
                  => RealFloat (AstNoSimplify r n)
