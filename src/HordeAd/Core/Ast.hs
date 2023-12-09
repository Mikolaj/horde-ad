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
  , AstInt, IntVarName, pattern AstIntVar, isRankedInt, ConcreteOf, ADShare
    -- * More and less typed variables and type synonyms containing them
  , AstVarName(..), varNameToAstVarId
  , AstDynamicVarName(..), dynamicVarNameToAstVarId
  , AstArtifactRev, AstArtifactFwd
  , AstIndex, AstVarList, AstIndexS, AstVarListS
    -- * ASTs
  , AstRanked(..), AstShaped(..), AstDynamic(..), AstDomains(..)
  , AstBool(..), OpCodeNum1(..), OpCodeNum2(..), OpCode1(..), OpCode2(..)
  , OpCodeIntegral2(..), OpCodeBool(..), OpCodeRel(..)
    -- * Boolean definitions and instances
  , BoolOf, IfF(..), EqF(..), OrdF(..), minF, maxF
    -- * The auxiliary AstNoVectorize and AstNoSimplify definitions, for tests
  , AstNoVectorize(..), AstNoVectorizeS(..)
  , AstNoSimplify(..), AstNoSimplifyS(..)
  ) where

import Prelude hiding (foldl')

import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as OS
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Clown
import           Data.Bifunctor.Flip
import           Data.Int (Int64)
import           Data.Kind (Type)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality (testEquality, (:~:) (Refl))
import           GHC.TypeLits (KnownNat, sameNat, type (+), type (<=))
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
type instance DomainsOf (Clown (AstDynamic s)) = AstDomains s

type instance RankedOf (AstRanked s) = AstRanked s
type instance ShapedOf (AstRanked s) = AstShaped s
type instance DynamicOf (AstRanked s) = AstDynamic s
type instance DomainsOf (AstRanked s) = AstDomains s
type instance PrimalOf (AstRanked s) = AstRanked PrimalSpan
type instance DualOf (AstRanked s) = AstRanked DualSpan

type instance RankedOf (AstShaped s) = AstRanked s
type instance ShapedOf (AstShaped s) = AstShaped s
type instance DynamicOf (AstShaped s) = AstDynamic s
type instance DomainsOf (AstShaped s) = AstDomains s
type instance PrimalOf (AstShaped s) = AstShaped PrimalSpan
type instance DualOf (AstShaped s) = AstShaped DualSpan


-- * Assorted small definitions

-- | This is the (arbitrarily) chosen representation of terms representing
-- integers in the indexes of tensor operations.
type AstInt = AstRanked PrimalSpan Int64 0

type IntVarName = AstVarName (AstRanked PrimalSpan) Int64 0

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
type ConcreteOf :: forall k. TensorKind k -> TensorKind k
type family ConcreteOf f = result | result -> f where
  ConcreteOf (AstRanked FullSpan) = Flip OR.Array
  ConcreteOf (AstShaped FullSpan) = Flip OS.Array

type ADShare = ADShareD (AstDynamic PrimalSpan)


-- * More and less typed variables and type synonyms containing them

type role AstVarName phantom phantom nominal
newtype AstVarName (f :: TensorKind k) (r :: Type) (y :: k) =
   AstVarName AstVarId
 deriving (Eq, Ord, Enum)

instance Show (AstVarName f r y) where
  showsPrec d (AstVarName var) =
    showsPrec d var  -- backward compatibility vs test results

varNameToAstVarId :: AstVarName f r y -> AstVarId
varNameToAstVarId (AstVarName var) = var

-- This needs to carry sh regardless of f, even for AstRanked, because
-- then it needs to recover the shape argument for AstVar.
--
-- The explicit kind is required to compile with GHC 9.2.
--
-- A lot of the variables are existential, but there's no nesting,
-- so no special care about picking specializations at runtime is needed.
type role AstDynamicVarName phantom
type AstDynamicVarName :: forall {k}. TensorKind k -> Type
data AstDynamicVarName f where
  AstDynamicVarName :: forall k sh r y (f :: TensorKind k).
                       (OS.Shape sh, GoodScalar r)
                    => AstVarName f r y -> AstDynamicVarName f
deriving instance Show (AstDynamicVarName f)

dynamicVarNameToAstVarId :: AstDynamicVarName f -> AstVarId
dynamicVarNameToAstVarId (AstDynamicVarName (AstVarName var)) = var

-- The reverse derivative artifact from step 6) of our full pipeline.
type AstArtifactRev (f :: TensorKind k) r y =
  ( (AstVarName f r y, [AstDynamicVarName f])
  , AstDomains PrimalSpan, f r y, OR.ShapeL )

type AstArtifactFwd (f :: TensorKind k) r y =
  ( ([AstDynamicVarName f], [AstDynamicVarName f])
  , f r y, f r y )

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
type role AstRanked nominal nominal nominal
  -- r has to be nominal, because type class arguments always are
data AstRanked :: AstSpanType -> RankedTensorKind where
  AstVar :: ShapeInt n -> AstVarName (AstRanked s) r n -> AstRanked s r n
  -- The r variable is existential here, so a proper specialization needs
  -- to be picked explicitly at runtime.
  AstLet :: (KnownNat n, KnownNat m, GoodScalar r, AstSpan s)
         => AstVarName (AstRanked s) r n -> AstRanked s r n
         -> AstRanked s2 r2 m
         -> AstRanked s2 r2 m
  AstLetADShare :: ADShare -> AstRanked PrimalSpan r n
                -> AstRanked PrimalSpan r n
   -- these are mixed local/global lets, because they can be identical
   -- to the lets stored in the D constructor and so should not be inlined
   -- even in trivial cases until the transpose pass eliminates D
  AstCond :: AstBool
          -> AstRanked s r n -> AstRanked s r n -> AstRanked s r n

  -- There are existential variables here, as well.
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
  -- There are existential variables here, as well.
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
                => [AstDynamicVarName (AstShaped s)] -> AstDomains s
                -> AstRanked s2 r n
                -> AstRanked s2 r n

deriving instance GoodScalar r => Show (AstRanked s r n)

-- | AST for shaped tensors that are meant to be differentiated.
type role AstShaped nominal nominal nominal
data AstShaped :: AstSpanType -> ShapedTensorKind where
  -- To permit defining objective functions in Ast, not just constants:
  AstVarS :: forall sh r s. AstVarName (AstShaped s) r sh -> AstShaped s r sh
  AstLetS :: (OS.Shape sh, OS.Shape sh2, GoodScalar r, AstSpan s)
          => AstVarName (AstShaped s) r sh -> AstShaped s r sh
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
                 => [AstDynamicVarName (AstShaped s)] -> AstDomains s
                 -> AstShaped s2 r sh
                 -> AstShaped s2 r sh

deriving instance (GoodScalar r, OS.Shape sh) => Show (AstShaped s r sh)

type role AstDynamic nominal nominal
data AstDynamic :: AstSpanType -> Type -> Type where
  AstRToD :: forall n r s. KnownNat n
          => AstRanked s r n -> AstDynamic s r
  AstSToD :: forall sh r s. OS.Shape sh
          => AstShaped s r sh -> AstDynamic s r
deriving instance GoodScalar r => Show (AstDynamic s r)

type role AstDomains nominal
data AstDomains s where
  -- There are existential variables inside DynamicExists here.
  AstDomains :: Domains (AstDynamic s) -> AstDomains s
  -- The r variable is existential here, so a proper specialization needs
  -- to be picked explicitly at runtime.
  AstDomainsLet :: (KnownNat n, GoodScalar r, AstSpan s)
                => AstVarName (AstRanked s) r n -> AstRanked s r n
                -> AstDomains s2
                -> AstDomains s2
  AstDomainsLetS :: (OS.Shape sh, GoodScalar r, AstSpan s)
                 => AstVarName (AstShaped s) r sh -> AstShaped s r sh
                 -> AstDomains s2
                 -> AstDomains s2
  AstRev :: (GoodScalar r, KnownNat n)
         => ([AstDynamicVarName (AstRanked s)], AstRanked s r n)
         -> AstDomains s
         -> AstDomains s
    -- ^ the function body can't have any free variables outside those
    -- listed in the first component of the pair; this reflects
    -- the quantification in 'rrev' and prevents cotangent confusion
deriving instance Show (AstDomains s)

data AstBool where
  AstBoolNot :: AstBool -> AstBool
  AstB2 :: OpCodeBool -> AstBool -> AstBool -> AstBool
  AstBoolConst :: Bool -> AstBool
  -- There are existential variables here, as well.
  AstRel :: (KnownNat n, GoodScalar r)
         => OpCodeRel -> AstRanked PrimalSpan r n -> AstRanked PrimalSpan r n
         -> AstBool
  AstRelS :: (OS.Shape sh, GoodScalar r)
          => OpCodeRel -> AstShaped PrimalSpan r sh -> AstShaped PrimalSpan r sh
          -> AstBool
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
    AndOp | OrOp
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
  abs = AstN1 AbsOp
  signum = AstN1 SignumOp
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
  quot = AstI2 QuotOp
  rem = AstI2 RemOp
  quotRem u v = (AstI2 QuotOp u v, AstI2 RemOp u v)
  divMod _ _ = error "divMod: disabled; much less efficient than quot and rem"
  toInteger = undefined  -- we can't evaluate uninstantiated variables, etc.

instance (Differentiable r, Fractional (OR.Array n r), AstSpan s)
         => Fractional (AstRanked s r n) where
  u / v = AstR2 DivideOp u v
  recip = AstR1 RecipOp
  fromRational = fromPrimal . AstConst . fromRational

instance (Differentiable r, Floating (OR.Array n r), AstSpan s)
         => Floating (AstRanked s r n) where
  pi = fromPrimal $ AstConst pi
  exp = AstR1 ExpOp
  log = AstR1 LogOp
  sqrt = AstR1 SqrtOp
  (**) = AstR2 PowerOp
  logBase = AstR2 LogBaseOp
  sin = AstR1 SinOp
  cos = AstR1 CosOp
  tan = AstR1 TanOp
  asin = AstR1 AsinOp
  acos = AstR1 AcosOp
  atan = AstR1 AtanOp
  sinh = AstR1 SinhOp
  cosh = AstR1 CoshOp
  tanh = AstR1 TanhOp
  asinh = AstR1 AsinhOp
  acosh = AstR1 AcoshOp
  atanh = AstR1 AtanhOp

instance (Differentiable r, RealFrac (OR.Array n r), AstSpan s)
         => RealFrac (AstRanked s r n) where
  properFraction = undefined
    -- The integral type doesn't have a Storable constraint,
    -- so we can't implement this (nor RealFracB from Boolean package).

instance (Differentiable r, RealFloat (OR.Array n r), AstSpan s)
         => RealFloat (AstRanked s r n) where
  atan2 = AstR2 Atan2Op
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
  abs = AstN1S AbsOp
  signum = AstN1S SignumOp
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
  quot = AstI2S QuotOp
  rem = AstI2S RemOp
  quotRem u v = (AstI2S QuotOp u v, AstI2S RemOp u v)
  divMod _ _ = error "divMod: disabled; much less efficient than quot and rem"
  toInteger = undefined  -- we can't evaluate uninstantiated variables, etc.

instance (Differentiable r, Fractional (OS.Array sh r), AstSpan s)
         => Fractional (AstShaped s r sh) where
  u / v = AstR2S DivideOp u v
  recip = AstR1S RecipOp
  fromRational = fromPrimalS . AstConstS . fromRational

instance (Differentiable r, Floating (OS.Array sh r), AstSpan s)
         => Floating (AstShaped s r sh) where
  pi = fromPrimalS $ AstConstS pi
  exp = AstR1S ExpOp
  log = AstR1S LogOp
  sqrt = AstR1S SqrtOp
  (**) = AstR2S PowerOp
  logBase = AstR2S LogBaseOp
  sin = AstR1S SinOp
  cos = AstR1S CosOp
  tan = AstR1S TanOp
  asin = AstR1S AsinOp
  acos = AstR1S AcosOp
  atan = AstR1S AtanOp
  sinh = AstR1S SinhOp
  cosh = AstR1S CoshOp
  tanh = AstR1S TanhOp
  asinh = AstR1S AsinhOp
  acosh = AstR1S AcoshOp
  atanh = AstR1S AtanhOp

instance (Differentiable r, RealFrac (OS.Array sh r), AstSpan s)
         => RealFrac (AstShaped s r sh) where
  properFraction = undefined
    -- The integral type doesn't have a Storable constraint,
    -- so we can't implement this (nor RealFracB from Boolean package).

instance (Differentiable r, RealFloat (OS.Array sh r), AstSpan s)
         => RealFloat (AstShaped s r sh) where
  atan2 = AstR2S Atan2Op
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
  notB = AstBoolNot
  AstBoolConst b &&* AstBoolConst c = AstBoolConst $ b && c
                                        -- common in indexing
  b &&* c = AstB2 AndOp b c
  b ||* c = AstB2 OrOp b c


-- * Boolean definitions and instances

type BoolOf :: forall {k}. TensorKind k -> Type
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

class Boolean (SimpleBoolOf f) => IfF (f :: TensorKind k) where
  ifF :: (GoodScalar r, HasSingletonDict y)
      => BoolOf f -> f r y -> f r y -> f r y

infix 4 ==., /=.
class Boolean (SimpleBoolOf f) => EqF (f :: TensorKind k) where
  -- The existential variables here are handled in instances, e.g., via AstRel.
  (==.), (/=.) :: (GoodScalar r, HasSingletonDict y)
               => f r y -> f r y -> BoolOf f
  u /=. v = notB (u ==. v)

infix 4 <., <=., >=., >.
class Boolean (SimpleBoolOf f) => OrdF (f :: TensorKind k) where
  -- The existential variables here are handled in instances, e.g., via AstRel.
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

type role AstNoVectorize nominal nominal nominal
newtype AstNoVectorize s r n =
  AstNoVectorize {unAstNoVectorize :: AstRanked s r n}
deriving instance GoodScalar r => Show (AstNoVectorize s r n)

type role AstNoVectorizeS nominal nominal nominal
newtype AstNoVectorizeS s r sh =
  AstNoVectorizeS {unAstNoVectorizeS :: AstShaped s r sh}
deriving instance (GoodScalar r, OS.Shape sh) => Show (AstNoVectorizeS s r sh)

type role AstNoSimplify nominal nominal nominal
newtype AstNoSimplify s r n =
  AstNoSimplify {unAstNoSimplify :: AstRanked s r n}
deriving instance GoodScalar r => Show (AstNoSimplify s r n)

type role AstNoSimplifyS nominal nominal nominal
newtype AstNoSimplifyS s r sh =
  AstNoSimplifyS {unAstNoSimplifyS :: AstShaped s r sh}
deriving instance (GoodScalar r, OS.Shape sh) => Show (AstNoSimplifyS s r sh)