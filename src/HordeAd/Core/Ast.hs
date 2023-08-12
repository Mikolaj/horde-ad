{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
-- | AST of the code to be differentiated. It's needed mostly for handling
-- higher order operations such as build and map, via vectorization,
-- and for producing reusable reverse derivative terms. However,
-- it can also be used for other code transformations, e.g., simplification.
module HordeAd.Core.Ast
  ( -- * The AstSpan kind
    AstSpanType(..), AstSpan(..), astSpanT, sameAstSpan
    -- * Assorted small definitions
  , AstInt, IntVarName, pattern AstIntVar, isRankedInt, ConcreteOf
    -- * More and less typed variables and type synonyms containing them
  , AstId, intToAstId
  , AstVarId, intToAstVarId, astIdToAstVarId, astVarIdToAstId, varNameToAstId
  , AstArtifactRev, AstArtifactFwd
  , AstIndex, AstVarList, AstIndexS, AstVarListS
    -- * ASTs
  , AstRanked(..), AstShaped(..), AstDynamic(..), AstDomains(..)
  , AstVarName(..), AstDynamicVarName(..), AstBool(..)
  , OpCodeNum1(..), OpCodeNum2(..), OpCode1(..), OpCode2(..)
  , OpCodeIntegral2(..), OpCodeBool(..), OpCodeRel(..)
    -- * Boolean definitions and instances
  , BoolOf, IfF(..), EqF(..), OrdF(..), minF, maxF
    -- * ADShare definition
  , AstBindings, ADShare
  , emptyADShare, insertADShare, mergeADShare, subtractADShare
  , flattenADShare, assocsADShare, varInADShare, nullADShare
    -- * The auxiliary AstNoVectorize and AstNoSimplify definitions, for tests
  , AstNoVectorize(..), AstNoVectorizeS(..)
  , AstNoSimplify(..), AstNoSimplifyS(..)
  ) where

import Prelude

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
import           Data.Type.Equality (testEquality, (:~:) (Refl))
import           GHC.TypeLits (KnownNat, sameNat, type (+), type (<=))
import           System.IO.Unsafe (unsafePerformIO)
import           Type.Reflection (Typeable, eqTypeRep, typeRep, (:~~:) (HRefl))

import HordeAd.Core.Types
import HordeAd.Util.ShapedList (ShapedList (..))
import HordeAd.Util.SizedIndex
import HordeAd.Util.SizedList

-- * The AstSpan kind

-- | A kind (a type intended to be promoted) marking whether an AST term
-- is supposed to denote the primal part of a dual number, the dual part
-- or the whole dual number. It's mainly used to index the terms
-- of the AstRanked and realated GADTs.
data AstSpanType = PrimalSpan | DualSpan | FullSpan
  deriving Typeable

-- A poor man's singleton type, modelled after orthotope's @Shape@.
class Typeable s => AstSpan (s :: AstSpanType) where
  astSpanP :: Proxy s -> AstSpanType
  fromPrimal :: AstRanked PrimalSpan r y -> AstRanked s r y
  fromPrimalS :: AstShaped PrimalSpan r y -> AstShaped s r y

instance AstSpan PrimalSpan where
  astSpanP _ = PrimalSpan
  fromPrimal = id
  fromPrimalS = id

instance AstSpan DualSpan where
  astSpanP _ = DualSpan
  fromPrimal t = AstDualPart $ AstConstant t  -- this is nil (not primal 0)
  fromPrimalS t = AstDualPartS $ AstConstantS t

instance AstSpan FullSpan where
  astSpanP _ = FullSpan
  fromPrimal = AstConstant
  fromPrimalS = AstConstantS

astSpanT :: forall s. AstSpan s => AstSpanType
{-# INLINE astSpanT #-}
astSpanT = astSpanP (Proxy :: Proxy s)

sameAstSpan :: forall s1 s2. (AstSpan s1, AstSpan s2) => Maybe (s1 :~: s2)
sameAstSpan = case eqTypeRep (typeRep @s1) (typeRep @s2) of
                Just HRefl -> Just Refl
                Nothing -> Nothing


-- * Basic type family instances

type instance RankedOf (Clown (AstDynamic s)) = AstRanked s
type instance ShapedOf (Clown (AstDynamic s)) = AstShaped s
type instance DynamicOf (Clown (AstDynamic s)) = AstDynamic s

type instance RankedOf (AstRanked s) = AstRanked s
type instance ShapedOf (AstRanked s) = AstShaped s
type instance DynamicOf (AstRanked s) = AstDynamic s
type instance PrimalOf (AstRanked s) = AstRanked PrimalSpan
type instance DualOf (AstRanked s) = AstRanked DualSpan

type instance RankedOf (AstShaped s) = AstRanked s
type instance ShapedOf (AstShaped s) = AstShaped s
type instance DynamicOf (AstShaped s) = AstDynamic s
type instance PrimalOf (AstShaped s) = AstShaped PrimalSpan
type instance DualOf (AstShaped s) = AstShaped DualSpan


-- * Assorted small definitions

-- | This is the (arbitrarily) chosen representation of terms representing
-- integers in the indexes of tensor operations.
type AstInt = AstRanked PrimalSpan Int64 0

type IntVarName = AstVarName PrimalSpan AstRanked Int64 0

pattern AstIntVar :: IntVarName -> AstInt
pattern AstIntVar var = AstVar ZS var

isRankedInt :: forall s r n. (AstSpan s, GoodScalar r, KnownNat n)
            => AstRanked s r n
            -> Maybe (AstRanked s r n :~: AstRanked PrimalSpan Int64 0)
isRankedInt _ = case ( sameAstSpan @s @PrimalSpan
                     , testEquality (typeRep @r) (typeRep @Int64)
                     , sameNat (Proxy @n) (Proxy @0) ) of
                  (Just Refl, Just Refl, Just Refl) -> Just Refl
                  _ -> Nothing

-- | The closed type family that assigns a concrete tensor type
-- to its corresponding AST type.
type ConcreteOf :: forall k. (AstSpanType -> TensorKind k) -> TensorKind k
type family ConcreteOf f = result | result -> f where
  ConcreteOf AstRanked = Flip OR.Array
  ConcreteOf AstShaped = Flip OS.Array


-- * More and less typed variables and type synonyms containing them

newtype AstId = AstId Int
 deriving (Eq, Ord, Show, Enum)

intToAstId :: Int -> AstId
intToAstId = AstId

-- We avoid adding a phantom type denoting the tensor functor,
-- because it can't be easily compared (even fully applies) and so the phantom
-- is useless. We don't add the underlying scalar nor the rank/shape,
-- because some collections differ in those to, e.g., domain,
-- e.g. in AstLetDomainsS.
newtype AstVarId (s :: AstSpanType) = AstVarId Int
 deriving (Eq, Ord, Show, Enum)

intToAstVarId :: Int -> AstVarId s
intToAstVarId = AstVarId

astIdToAstVarId :: AstId -> AstVarId s
astIdToAstVarId (AstId x) = AstVarId x

astVarIdToAstId :: AstVarId s -> AstId
astVarIdToAstId (AstVarId x) = AstId x

varNameToAstId :: AstVarName s f r y -> AstId
varNameToAstId (AstVarName var) = astVarIdToAstId var

newtype AstVarName
          (s :: AstSpanType) (f :: AstSpanType -> TensorKind k)
          (r :: Type) (y :: k) =
            AstVarName (AstVarId s)
 deriving (Eq, Ord, Enum)

instance Show (AstVarName s f r y) where
  showsPrec d (AstVarName var) =
    showsPrec d var  -- backward compatibility vs test results

-- This needs to carry sh regardless of f, even for AstRanked, because
-- then it needs to recover the shape argument for AstVar.
--
-- The explicit kind is required to compile with GHC 9.2.
--
-- A lot of the variables are existential, but there's no nesting,
-- so no special care about picking specializations at runtime is needed.
data AstDynamicVarName s f where
  AstDynamicVarName :: forall k sh r y s (f :: AstSpanType -> TensorKind k).
                       (OS.Shape sh, GoodScalar r)
                    => AstVarName s f r y -> AstDynamicVarName s f
deriving instance Show (AstDynamicVarName s f)

-- The reverse derivative artifact from step 6) of our full pipeline.
type AstArtifactRev (f :: AstSpanType -> TensorKind k) r y =
  ( (AstVarName PrimalSpan f r y, [AstDynamicVarName PrimalSpan f])
  , AstDomains PrimalSpan, f PrimalSpan r y )

type AstArtifactFwd (f :: AstSpanType -> TensorKind k) r y =
  ( ([AstDynamicVarName PrimalSpan f], [AstDynamicVarName PrimalSpan f])
  , f PrimalSpan r y, f PrimalSpan r y )

type AstIndex n = Index n AstInt

type AstVarList n = SizedList n IntVarName

type AstIndexS sh = ShapedList sh AstInt

type AstVarListS sh = ShapedList sh IntVarName


-- * ASTs

-- | AST for ranked tensors that are meant to be differentiated.
--
-- We use here @ShapeInt@ for simplicity. @Shape n AstInt@ gives
-- more expressiveness, but leads to irregular tensors,
-- especially after vectorization, and prevents static checking of shapes.
data AstRanked :: AstSpanType -> RankedTensorKind where
  AstVar :: ShapeInt n -> AstVarName s AstRanked r n -> AstRanked s r n
  -- The r variable is existential here, so a proper specialization needs
  -- to be picked explicitly at runtime.
  AstLet :: (KnownNat n, KnownNat m, GoodScalar r, AstSpan s)
         => AstVarName s AstRanked r n -> AstRanked s r n
         -> AstRanked s2 r2 m
         -> AstRanked s2 r2 m
  AstLetADShare :: ADShare -> AstRanked PrimalSpan r n
                -> AstRanked PrimalSpan r n
   -- these are mixed local/global lets, because they can be identical
   -- to the lets stored in the D constructor and so should not be inlined
   -- even in trivial cases until the transpose pass eliminates D
  AstCond :: AstBool
          -> AstRanked s r n -> AstRanked s r n -> AstRanked s r n

  -- TODO: there are existential variables here, as well.
  AstMinIndex :: GoodScalar r
              => AstRanked PrimalSpan r (1 + n) -> AstRanked PrimalSpan r2 n
  AstMaxIndex :: GoodScalar r
              => AstRanked PrimalSpan r (1 + n) -> AstRanked PrimalSpan r2 n
  AstFloor :: (GoodScalar r, RealFrac r, Integral r2)
           => AstRanked PrimalSpan r n -> AstRanked PrimalSpan r2 n
  AstIota :: AstRanked PrimalSpan r 1

  -- For the numeric classes:
  AstN1 :: OpCodeNum1 -> AstRanked s r n -> AstRanked s r n
  AstN2 :: OpCodeNum2 -> AstRanked s r n -> AstRanked s r n
        -> AstRanked s r n
  AstR1 :: Differentiable r
        => OpCode1 -> AstRanked s r n -> AstRanked s r n
  AstR2 :: Differentiable r
        => OpCode2 -> AstRanked s r n -> AstRanked s r n
        -> AstRanked s r n
  AstI2 :: Integral r
        => OpCodeIntegral2 -> AstRanked s r n -> AstRanked s r n
        -> AstRanked s r n
  AstSumOfList :: [AstRanked s r n] -> AstRanked s r n

  -- For the main part of the RankedTensor class:
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
            => Int -> (IntVarName, AstRanked s r n)
            -> AstRanked s r (1 + n)
  AstGather :: forall m n p r s. (KnownNat m, KnownNat n, KnownNat p)
            => ShapeInt (m + n)
            -> AstRanked s r (p + n) -> (AstVarList m, AstIndex p)
            -> AstRanked s r (m + n)
    -- out of bounds indexing is permitted
  -- TODO: there are existential variables here, as well.
  AstCast :: (GoodScalar r1, RealFrac r1, RealFrac r2)
          => AstRanked s r1 n -> AstRanked s r2 n
  AstFromIntegral :: (GoodScalar r1, Integral r1)
                  => AstRanked PrimalSpan r1 n -> AstRanked PrimalSpan r2 n
  AstConst :: OR.Array n r -> AstRanked PrimalSpan r n

  AstSToR :: OS.Shape sh
          => AstShaped s r sh -> AstRanked s r (OS.Rank sh)

  -- For the forbidden half of the RankedTensor class:
  AstConstant :: AstRanked PrimalSpan r n -> AstRanked FullSpan r n
  AstPrimalPart :: AstRanked FullSpan r n -> AstRanked PrimalSpan r n
  AstDualPart :: AstRanked FullSpan r n -> AstRanked DualSpan r n
  AstD :: AstRanked PrimalSpan r n -> AstRanked DualSpan r n
       -> AstRanked FullSpan r n
  AstLetDomains :: AstSpan s
                => Data.Vector.Vector (AstVarId s) -> AstDomains s
                -> AstRanked s2 r n
                -> AstRanked s2 r n

deriving instance GoodScalar r => Show (AstRanked s r n)

-- | AST for shaped tensors that are meant to be differentiated.
data AstShaped :: AstSpanType -> ShapedTensorKind where
  -- To permit defining objective functions in Ast, not just constants:
  AstVarS :: forall sh r s. AstVarName s AstShaped r sh -> AstShaped s r sh
  AstLetS :: (OS.Shape sh, OS.Shape sh2, GoodScalar r, AstSpan s)
          => AstVarName s AstShaped r sh -> AstShaped s r sh
          -> AstShaped s2 r2 sh2
          -> AstShaped s2 r2 sh2
  AstLetADShareS :: ADShare -> AstShaped PrimalSpan r sh
                 -> AstShaped PrimalSpan r sh
   -- these are mixed local/global lets, because they can be identical
   -- to the lets stored in the D constructor and so should not be inlined
   -- even in trivial cases until the transpose pass eliminates D
  AstCondS :: AstBool
           -> AstShaped s r sh -> AstShaped s r sh -> AstShaped s r sh

  AstMinIndexS :: (OS.Shape sh, KnownNat n, GoodScalar r)
               => AstShaped PrimalSpan r (n ': sh)
               -> AstShaped PrimalSpan r2 (OS.Init (n ': sh))
  AstMaxIndexS :: (OS.Shape sh, KnownNat n, GoodScalar r)
               => AstShaped PrimalSpan r (n ': sh)
               -> AstShaped PrimalSpan r2 (OS.Init (n ': sh))
  AstFloorS :: (GoodScalar r, RealFrac r, Integral r2)
            => AstShaped PrimalSpan r sh -> AstShaped PrimalSpan r2 sh
  AstIotaS :: forall n r. KnownNat n => AstShaped PrimalSpan r '[n]

  -- For the numeric classes:
  AstN1S :: OpCodeNum1 -> AstShaped s r sh -> AstShaped s r sh
  AstN2S :: OpCodeNum2 -> AstShaped s r sh -> AstShaped s r sh
         -> AstShaped s r sh
  AstR1S :: Differentiable r
         => OpCode1 -> AstShaped s r sh -> AstShaped s r sh
  AstR2S :: Differentiable r
         => OpCode2 -> AstShaped s r sh -> AstShaped s r sh
         -> AstShaped s r sh
  AstI2S :: Integral r
         => OpCodeIntegral2 -> AstShaped s r sh -> AstShaped s r sh
         -> AstShaped s r sh
  AstSumOfListS :: [AstShaped s r sh] -> AstShaped s r sh

  -- For the main part of the ShapedTensor class:
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
             => (IntVarName, AstShaped s r sh)
             -> AstShaped s r (n ': sh)
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
                   => AstShaped PrimalSpan r1 sh -> AstShaped PrimalSpan r2 sh
  AstConstS :: OS.Array sh r -> AstShaped PrimalSpan r sh

  AstRToS :: (OS.Shape sh, KnownNat (OS.Rank sh))
          => AstRanked s r (OS.Rank sh) -> AstShaped s r sh

  -- For the forbidden half of the ShapedTensor class:
  AstConstantS :: AstShaped PrimalSpan r sh -> AstShaped FullSpan r sh
  AstPrimalPartS :: AstShaped FullSpan r sh -> AstShaped PrimalSpan r sh
  AstDualPartS :: AstShaped FullSpan r sh -> AstShaped DualSpan r sh
  AstDS :: AstShaped PrimalSpan r sh -> AstShaped DualSpan r sh
        -> AstShaped FullSpan r sh
  AstLetDomainsS :: AstSpan s
                 => Data.Vector.Vector (AstVarId s) -> AstDomains s
                 -> AstShaped s2 r sh
                 -> AstShaped s2 r sh

deriving instance (GoodScalar r, OS.Shape sh) => Show (AstShaped s r sh)

data AstDynamic :: AstSpanType -> Type -> Type where
  AstRToD :: KnownNat n
          => AstRanked s r n -> AstDynamic s r
  AstSToD :: OS.Shape sh
          => AstShaped s r sh -> AstDynamic s r
deriving instance GoodScalar r => Show (AstDynamic s r)

data AstDomains s where
  AstDomains :: Data.Vector.Vector (DynamicExists (AstDynamic s))
             -> AstDomains s
  -- The r variable is existential here, so a proper specialization needs
  -- to be picked explicitly at runtime.
  AstDomainsLet :: (KnownNat n, GoodScalar r)
                => AstVarName s AstRanked r n
                -> AstRanked s r n -> AstDomains s
                -> AstDomains s
  AstDomainsLetS :: (OS.Shape sh, GoodScalar r)
                 => AstVarName s AstShaped r sh
                 -> AstShaped s r sh -> AstDomains s
                 -> AstDomains s
deriving instance Show (AstDomains s)

data AstBool where
  AstBoolOp :: OpCodeBool -> [AstBool] -> AstBool
  AstBoolConst :: Bool -> AstBool
  -- TODO: there are existential variables here, as well.
  AstRel :: (KnownNat n, GoodScalar r)
         => OpCodeRel -> [AstRanked PrimalSpan r n] -> AstBool
  AstRelS :: (OS.Shape sh, GoodScalar r)
          => OpCodeRel -> [AstShaped PrimalSpan r sh] -> AstBool
deriving instance Show AstBool

data OpCodeNum1 =
    NegateOp | AbsOp | SignumOp
 deriving Show

data OpCodeNum2 =
    MinusOp | TimesOp
 deriving Show

data OpCode1 =
    RecipOp
  | ExpOp | LogOp | SqrtOp
  | SinOp | CosOp | TanOp | AsinOp | AcosOp | AtanOp
  | SinhOp | CoshOp | TanhOp | AsinhOp | AcoshOp | AtanhOp
 deriving Show

data OpCode2 =
    DivideOp
  | PowerOp | LogBaseOp
  | Atan2Op
 deriving Show

data OpCodeIntegral2 =
    QuotOp | RemOp
 deriving Show

data OpCodeBool =
    NotOp | AndOp | OrOp
 deriving Show

data OpCodeRel =
    EqOp | NeqOp
  | LeqOp| GeqOp | LsOp | GtOp
 deriving Show


-- * Unlawful numeric instances of ranked AST; they are lawful modulo evaluation

-- These are, unfortunately, required by some numeric instances.
instance Eq (AstRanked s r n) where
  (==) = error "AST requires that EqF be used instead"
  (/=) = error "AST requires that EqF be used instead"

instance Ord (AstRanked s r n) where
  (<=) = error "AST requires that OrdF be used instead"

instance (Num (OR.Array n r), AstSpan s)
         => Num (AstRanked s r n) where
  -- The normal form has AstConst, if any, as the first element of the list
  -- all lists fully flattened and length >= 2.
  AstSumOfList (AstConst u : lu) + AstSumOfList (AstConst v : lv) =
    AstSumOfList (AstConst (u + v) : lu ++ lv)
  AstSumOfList lu + AstSumOfList (AstConst v : lv) =
    AstSumOfList (AstConst v : lv ++ lu)
  AstSumOfList lu + AstSumOfList lv = AstSumOfList (lu ++ lv)

  AstLetADShare l u + v = AstLetADShare l $ u + v
  u + AstLetADShare l v = AstLetADShare l $ u + v

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
  AstLetADShare l u - v = AstLetADShare l $ u - v
  u - AstLetADShare l v = AstLetADShare l $ u - v
  u - v = AstN2 MinusOp u v

  AstConst u * AstConst v = AstConst (u * v)  -- common in indexing
  AstLetADShare l u * v = AstLetADShare l $ u * v
  u * AstLetADShare l v = AstLetADShare l $ u * v
  u * v = AstN2 TimesOp u v

  negate (AstLetADShare l u) = AstLetADShare l $ negate u
  negate u = AstN1 NegateOp u
  abs v = AstN1 AbsOp v
  signum v = AstN1 SignumOp v
  fromInteger = fromPrimal . AstConst . fromInteger
    -- it's crucial that there is no AstConstant in fromInteger code
    -- so that we don't need 4 times the simplification rules

instance (Real (OR.Array n r), AstSpan s)
         => Real (AstRanked s r n) where
  toRational = undefined
    -- very low priority, since these are all extremely not continuous

instance Enum r => Enum (AstRanked s r n) where
  toEnum = undefined  -- AstConst . OR.scalar . toEnum
  fromEnum = undefined  -- do we need to define our own Enum for this?

-- Warning: div and mod operations are very costly (simplifying them
-- requires constructing conditionals, etc). If this error is removed,
-- they are going to work, but slowly.
instance (Integral r, Integral (OR.Array n r), AstSpan s)
         => Integral (AstRanked s r n) where
  quot u v = AstI2 QuotOp u v
  rem u v = AstI2 RemOp u v
  quotRem u v = (AstI2 QuotOp u v, AstI2 RemOp u v)
  divMod _ _ = error "divMod: disabled; much less efficient than quot and rem"
  toInteger = undefined  -- we can't evaluate uninstantiated variables, etc.

instance (Differentiable r, Fractional (OR.Array n r), AstSpan s)
         => Fractional (AstRanked s r n) where
  u / v = AstR2 DivideOp u v
  recip v = AstR1 RecipOp v
  fromRational = fromPrimal . AstConst . fromRational

instance (Differentiable r, Floating (OR.Array n r), AstSpan s)
         => Floating (AstRanked s r n) where
  pi = fromPrimal $ AstConst pi
  exp u = AstR1 ExpOp u
  log u = AstR1 LogOp u
  sqrt u = AstR1 SqrtOp u
  u ** v = AstR2 PowerOp u v
  logBase u v = AstR2 LogBaseOp u v
  sin u = AstR1 SinOp u
  cos u = AstR1 CosOp u
  tan u = AstR1 TanOp u
  asin u = AstR1 AsinOp u
  acos u = AstR1 AcosOp u
  atan u = AstR1 AtanOp u
  sinh u = AstR1 SinhOp u
  cosh u = AstR1 CoshOp u
  tanh u = AstR1 TanhOp u
  asinh u = AstR1 AsinhOp u
  acosh u = AstR1 AcoshOp u
  atanh u = AstR1 AtanhOp u

instance (Differentiable r, RealFrac (OR.Array n r), AstSpan s)
         => RealFrac (AstRanked s r n) where
  properFraction = undefined
    -- The integral type doesn't have a Storable constraint,
    -- so we can't implement this (nor RealFracB from Boolean package).

instance (Differentiable r, RealFloat (OR.Array n r), AstSpan s)
         => RealFloat (AstRanked s r n) where
  atan2 u v = AstR2 Atan2Op u v
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


-- * Unlawful numeric instances of shaped AST; they are lawful modulo evaluation

instance Eq (AstShaped s r sh) where
  (==) = error "AST requires that EqF be used instead"
  (/=) = error "AST requires that EqF be used instead"

instance Ord (AstShaped s r sh) where
  (<=) = error "AST requires that OrdF be used instead"

instance (Num (OS.Array sh r), AstSpan s)
         => Num (AstShaped s r sh) where
  -- The normal form has AstConst, if any, as the first element of the list
  -- all lists fully flattened and length >= 2.
  AstSumOfListS (AstConstS u : lu) + AstSumOfListS (AstConstS v : lv) =
    AstSumOfListS (AstConstS (u + v) : lu ++ lv)
  AstSumOfListS lu + AstSumOfListS (AstConstS v : lv) =
    AstSumOfListS (AstConstS v : lv ++ lu)
  AstSumOfListS lu + AstSumOfListS lv = AstSumOfListS (lu ++ lv)

  AstLetADShareS l u + v = AstLetADShareS l $ u + v
  u + AstLetADShareS l v = AstLetADShareS l $ u + v

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
  AstLetADShareS l u - v = AstLetADShareS l $ u - v
  u - AstLetADShareS l v = AstLetADShareS l $ u - v
  u - v = AstN2S MinusOp u v

  AstConstS u * AstConstS v = AstConstS (u * v)  -- common in indexing
  AstLetADShareS l u * v = AstLetADShareS l $ u * v
  u * AstLetADShareS l v = AstLetADShareS l $ u * v
  u * v = AstN2S TimesOp u v

  negate (AstLetADShareS l u) = AstLetADShareS l $ negate u
  negate u = AstN1S NegateOp u
  abs v = AstN1S AbsOp v
  signum v = AstN1S SignumOp v
  fromInteger = fromPrimalS . AstConstS . fromInteger
    -- it's crucial that there is no AstConstant in fromInteger code
    -- so that we don't need 4 times the simplification rules

instance (Real (OS.Array sh r), AstSpan s) => Real (AstShaped s r sh) where
  toRational = undefined
    -- very low priority, since these are all extremely not continuous

instance Enum r => Enum (AstShaped s r n) where
  toEnum = undefined
  fromEnum = undefined  -- do we need to define our own Enum class for this?

-- Warning: div and mod operations are very costly (simplifying them
-- requires constructing conditionals, etc). If this error is removed,
-- they are going to work, but slowly.
instance (Integral r, Integral (OS.Array sh r), AstSpan s)
         => Integral (AstShaped s r sh) where
  quot u v = AstI2S QuotOp u v
  rem u v = AstI2S RemOp u v
  quotRem u v = (AstI2S QuotOp u v, AstI2S RemOp u v)
  divMod _ _ = error "divMod: disabled; much less efficient than quot and rem"
  toInteger = undefined  -- we can't evaluate uninstantiated variables, etc.

instance (Differentiable r, Fractional (OS.Array sh r), AstSpan s)
         => Fractional (AstShaped s r sh) where
  u / v = AstR2S DivideOp u v
  recip v = AstR1S RecipOp v
  fromRational = fromPrimalS . AstConstS . fromRational

instance (Differentiable r, Floating (OS.Array sh r), AstSpan s)
         => Floating (AstShaped s r sh) where
  pi = fromPrimalS $ AstConstS pi
  exp u = AstR1S ExpOp u
  log u = AstR1S LogOp u
  sqrt u = AstR1S SqrtOp u
  u ** v = AstR2S PowerOp u v
  logBase u v = AstR2S LogBaseOp u v
  sin u = AstR1S SinOp u
  cos u = AstR1S CosOp u
  tan u = AstR1S TanOp u
  asin u = AstR1S AsinOp u
  acos u = AstR1S AcosOp u
  atan u = AstR1S AtanOp u
  sinh u = AstR1S SinhOp u
  cosh u = AstR1S CoshOp u
  tanh u = AstR1S TanhOp u
  asinh u = AstR1S AsinhOp u
  acosh u = AstR1S AcoshOp u
  atanh u = AstR1S AtanhOp u

instance (Differentiable r, RealFrac (OS.Array sh r), AstSpan s)
         => RealFrac (AstShaped s r sh) where
  properFraction = undefined
    -- The integral type doesn't have a Storable constraint,
    -- so we can't implement this (nor RealFracB from Boolean package).

instance (Differentiable r, RealFloat (OS.Array sh r), AstSpan s)
         => RealFloat (AstShaped s r sh) where
  atan2 u v = AstR2S Atan2Op u v
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


-- * Unlawful instances of AST for bool; they are lawful modulo evaluation

instance Boolean AstBool where
  true = AstBoolConst True
  false = AstBoolConst False
  notB b = AstBoolOp NotOp [b]
  AstBoolConst b &&* AstBoolConst c = AstBoolConst $ b && c
                                        -- common in indexing
  b &&* c = AstBoolOp AndOp [b, c]
  b ||* c = AstBoolOp OrOp [b, c]


-- * Boolean definitions and instances

type BoolOf f = (ADShare, SimpleBoolOf f)

-- This and below is inspired by https://hackage.haskell.org/package/Boolean,
-- but renamed so that it does not conflict with it nor with Applicative
-- and modified to depend on the tensor structure functor only,
-- not on the type resulting from applying the functor to the underlying
-- scalar and rank/shape.
instance Boolean b => Boolean (ADShare, b) where
  true = (emptyADShare, true)
  false = (emptyADShare, false)
  notB (l, b) = (l, notB b)
  (l1, b) &&* (l2, c) = (l1 `mergeADShare` l2, b &&* c)
  (l1, b) ||* (l2, c) = (l1 `mergeADShare` l2, b ||* c)

class Boolean (BoolOf f) => IfF (f :: TensorKind k) where
  ifF :: (GoodScalar r, HasSingletonDict y)
      => BoolOf f -> f r y -> f r y -> f r y

infix 4 ==., /=.
class Boolean (BoolOf f) => EqF (f :: TensorKind k) where
  -- TODO: there are existential variables here, as well.
  (==.), (/=.) :: (GoodScalar r, HasSingletonDict y)
               => f r y -> f r y -> BoolOf f
  u /=. v = notB (u ==. v)

infix 4 <., <=., >=., >.
class Boolean (BoolOf f) => OrdF (f :: TensorKind k) where
  -- TODO: there are existential variables here, as well.
  (<.), (<=.), (>.), (>=.) :: (GoodScalar r, HasSingletonDict y)
                           => f r y -> f r y -> BoolOf f
  u >. v = v <. u
  u >=. v = notB (u <. v)
  u <=. v = v >=. u

minF :: (IfF f, OrdF f, GoodScalar r, HasSingletonDict y)
     => f r y -> f r y -> f r y
minF u v = ifF (u <=. v) u v

maxF :: (IfF f, OrdF f, GoodScalar r, HasSingletonDict y)
     => f r y -> f r y -> f r y
maxF u v = ifF (u >=. v) u v


-- * ADShare definition

type AstBindings f = [(AstId, DynamicExists (DynamicOf f))]

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
--
-- The r variable is existential, but operations that depends on it instance
-- are rarely called and relatively cheap, so no picking specializations
-- at runtime is needed.
data ADShare = ADShareNil
             | forall r. GoodScalar r
               => ADShareCons Int AstId (AstDynamic PrimalSpan r) ADShare
deriving instance Show ADShare

emptyADShare :: ADShare
emptyADShare = ADShareNil

insertADShare :: forall r. GoodScalar r
              => AstId -> AstDynamic PrimalSpan r -> ADShare -> ADShare
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

freshInsertADShare :: GoodScalar r
                   => AstId -> AstDynamic PrimalSpan r -> ADShare
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
                -> AstBindings (AstRanked PrimalSpan)
{-# INLINE subtractADShare #-}  -- help list fusion
subtractADShare !s1 !s2 =
  let subAD :: ADShare -> ADShare
            -> AstBindings (AstRanked PrimalSpan)
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

assocsADShare :: ADShare -> AstBindings (AstRanked PrimalSpan)
{-# INLINE assocsADShare #-}  -- help list fusion
assocsADShare ADShareNil = []
assocsADShare (ADShareCons _ key t rest) =
  (key, DynamicExists t) : assocsADShare rest

_lengthADShare :: Int -> ADShare -> Int
_lengthADShare acc ADShareNil = acc
_lengthADShare acc (ADShareCons _ _ _ rest) = _lengthADShare (acc + 1) rest

varInADShare :: (forall r. AstId -> AstDynamic PrimalSpan r -> Bool)
                -> AstId -> ADShare
                -> Bool
{-# INLINE varInADShare #-}
varInADShare _ _ ADShareNil = False
varInADShare varInAstDynamic var (ADShareCons _ _ d rest) =
  varInAstDynamic var d || varInADShare varInAstDynamic var rest
    -- TODO: for good Core, probably a local recursive 'go' is needed

nullADShare :: ADShare -> Bool
{-# INLINE nullADShare #-}
nullADShare ADShareNil = True
nullADShare ADShareCons{} = False


-- * The auxiliary AstNoVectorize and AstNoSimplify definitions, for tests

type instance RankedOf (AstNoVectorize s) = AstNoVectorize s
type instance ShapedOf (AstNoVectorize s) = AstNoVectorizeS s
type instance DynamicOf (AstNoVectorize s) = AstDynamic s
type instance PrimalOf (AstNoVectorize s) = AstRanked PrimalSpan
type instance DualOf (AstNoVectorize s) = AstRanked DualSpan
type instance RankedOf (AstNoVectorizeS s) = AstNoVectorize s
type instance ShapedOf (AstNoVectorizeS s) = AstNoVectorizeS s
type instance DynamicOf (AstNoVectorizeS s) = AstDynamic s
type instance PrimalOf (AstNoVectorizeS s) = AstShaped PrimalSpan
type instance DualOf (AstNoVectorizeS s) = AstShaped DualSpan
type instance RankedOf (AstNoSimplify s) = AstNoSimplify s
type instance ShapedOf (AstNoSimplify s) = AstNoSimplifyS s
type instance DynamicOf (AstNoSimplify s) = AstDynamic s
type instance PrimalOf (AstNoSimplify s) = AstRanked PrimalSpan
type instance DualOf (AstNoSimplify s) = AstRanked DualSpan
type instance RankedOf (AstNoSimplifyS s) = AstNoSimplify s
type instance ShapedOf (AstNoSimplifyS s) = AstNoSimplifyS s
type instance DynamicOf (AstNoSimplifyS s) = AstDynamic s
type instance PrimalOf (AstNoSimplifyS s) = AstShaped PrimalSpan
type instance DualOf (AstNoSimplifyS s) = AstShaped DualSpan

newtype AstNoVectorize s r n =
  AstNoVectorize {unAstNoVectorize :: AstRanked s r n}
deriving instance GoodScalar r => Show (AstNoVectorize s r n)

newtype AstNoVectorizeS s r sh =
  AstNoVectorizeS {unAstNoVectorizeS :: AstShaped s r sh}
deriving instance (GoodScalar r, OS.Shape sh) => Show (AstNoVectorizeS s r sh)

newtype AstNoSimplify s r n =
  AstNoSimplify {unAstNoSimplify :: AstRanked s r n}
deriving instance GoodScalar r => Show (AstNoSimplify s r n)

newtype AstNoSimplifyS s r sh =
  AstNoSimplifyS {unAstNoSimplifyS :: AstShaped s r sh}
deriving instance (GoodScalar r, OS.Shape sh) => Show (AstNoSimplifyS s r sh)
