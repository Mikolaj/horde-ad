{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
-- | AST of the code built using the @RankedTensor@ and related classes.
-- The AST is needed for handling second order operations (such as build
-- and map, via IET (vectorization), and for producing reusable reverse
-- derivative terms. However, it can also be used for other code
-- transformations, e.g., simplification.
module HordeAd.Core.Ast
  ( -- * The AstSpan kind
    AstSpanType(..), AstSpan(..), sameAstSpan
    -- * More and less typed variables and related type synonyms
  , AstVarId, intToAstVarId
  , AstDynamicVarName(..), dynamicVarNameToAstVarId, voidFromVar, voidFromVars
  , AstInt, IntVarName, pattern AstIntVar, isRankedInt
  , AstVarName, mkAstVarName, varNameToAstVarId, tensorKindFromAstVarName
  , AstArtifactRev(..), AstArtifactFwd(..)
  , AstIndex, AstVarList, AstIndexS, AstVarListS, AstIndexX
    -- * AstBindingsCase and AstBindings
  , AstBindingsCase, AstBindings
    -- * ASTs
  , AstMethodOfSharing(..), AstTensor(..)
  , AstDynamic, AstHFun(..)
  , AstBool(..), OpCodeNum1(..), OpCodeNum2(..), OpCode1(..), OpCode2(..)
  , OpCodeIntegral2(..), OpCodeBool(..), OpCodeRel(..)
    -- * The AstRaw, AstNoVectorize and AstNoSimplify definitions
  , AstRaw(..)
  , AstNoVectorize(..)
  , AstNoSimplify(..)
  ) where

import Prelude hiding (foldl')

import Data.Array.Internal (valueOf)
import Data.Dependent.EnumMap.Strict (DEnumMap)
import Data.Dependent.EnumMap.Strict qualified as DMap
import Data.Functor.Const
import Data.GADT.Compare
import Data.GADT.Show
import Data.Int (Int64)
import Data.Kind (Type)
import Data.Proxy (Proxy (Proxy))
import Data.Some
import Data.Strict.Vector qualified as Data.Vector
import Data.Type.Equality (testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat, Nat, sameNat, type (+), type (<=))
import Type.Reflection (Typeable, eqTypeRep, typeRep, (:~~:) (HRefl))

import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape (IShX, IxX, ListX)
import Data.Array.Nested (KnownShX, Rank, type (++))
import Data.Array.Nested qualified as Nested

import HordeAd.Core.HVector
import HordeAd.Core.Types
import HordeAd.Internal.OrthotopeOrphanInstances
  (IntegralF (..), RealFloatF (..))
import HordeAd.Util.ShapedList (Drop, IndexS, Init, SizedListS, Take)
import HordeAd.Util.SizedList

-- * Basic type family instances

type instance PrimalOf (AstTensor ms s) = AstTensor ms PrimalSpan
type instance DualOf (AstTensor ms s) = AstTensor ms DualSpan
type instance ShareOf (AstTensor ms s) = AstRaw s

-- This can't be just HFun, because they need to be vectorized
-- and vectorization applies such functions to the variable from build1
-- and the variable has to be eliminated via vectorization to preserve
-- the closed form of the function. Just applying a Haskell closure
-- to the build1 variable and then duplicating the result of the function
-- would not eliminate the variable and also would likely results
-- in more costly computations. Also, that would prevent simplification
-- of the instances, especially after applied to arguments that are terms.
type instance HFunOf (AstTensor AstMethodLet s) x z = AstHFun x z  -- TODO: PrimalSpan


-- * The AstSpan kind

-- | A kind (a type intended to be promoted) marking whether an AST term
-- is supposed to denote the primal part of a dual number, the dual part
-- or the whole dual number. It's mainly used to index the terms
-- of the AstTensor and related GADTs.
type data AstSpanType = PrimalSpan | DualSpan | FullSpan

class Typeable s => AstSpan (s :: AstSpanType) where
  fromPrimal :: TensorKind y => AstTensor ms PrimalSpan y -> AstTensor ms s y

instance AstSpan PrimalSpan where
  fromPrimal = id

instance AstSpan DualSpan where
  fromPrimal t = AstDualPart $ AstConstant t  -- this is nil (not primal 0)

instance AstSpan FullSpan where
  fromPrimal = AstConstant

sameAstSpan :: forall s1 s2. (AstSpan s1, AstSpan s2) => Maybe (s1 :~: s2)
sameAstSpan = case eqTypeRep (typeRep @s1) (typeRep @s2) of
                Just HRefl -> Just Refl
                Nothing -> Nothing


-- * More and less typed variables and related type synonyms

-- We avoid adding a phantom type denoting the tensor functor,
-- because it can't be easily compared (even fully applied) and so the phantom
-- is useless. We don't add the underlying scalar nor the rank/shape,
-- because some collections differ in those too. We don't add a phantom span,
-- because carrying around type constructors that need to be applied to span
-- complicates the system greatly for moderate type safety gain
-- and a high number of different ID types induces many conversions.
newtype AstVarId = AstVarId Int
 deriving (Eq, Ord, Show, Enum)

intToAstVarId :: Int -> AstVarId
intToAstVarId = AstVarId

-- This can't be replaced by AstVarId. because in some places it's used
-- to record the type, scalar and shape of arguments in a HVector.
--
-- These variables have existential parameters, but there's no nesting,
-- so no special care about picking specializations at runtime is needed.
data AstDynamicVarName where
  AstDynamicVarName :: forall (ty :: Type) r sh.
                       (Typeable ty, GoodScalar r, KnownShS sh)
                    => AstVarId -> AstDynamicVarName
deriving instance Show AstDynamicVarName

dynamicVarNameToAstVarId :: AstDynamicVarName -> AstVarId
dynamicVarNameToAstVarId (AstDynamicVarName varId) = varId

voidFromVar :: AstDynamicVarName -> DynamicTensor VoidTensor
voidFromVar (AstDynamicVarName @ty @rD @shD _) =
  case testEquality (typeRep @ty) (typeRep @Nat) of
    Just Refl -> DynamicRankedDummy @rD @shD Proxy Proxy
    _ -> DynamicShapedDummy @rD @shD Proxy Proxy

voidFromVars :: [AstDynamicVarName] -> VoidHVector
voidFromVars = V.fromList . map voidFromVar

-- TODO: remove the rank field once we have TensorKindType singletons
type role AstVarName nominal nominal
data AstVarName :: AstSpanType -> TensorKindType -> Type where
  AstVarName :: forall s y. TensorKind y => AstVarId -> AstVarName s y

deriving instance Eq (AstVarName s y)

instance Show (AstVarName s y) where
  showsPrec d (AstVarName varId) =
    showsPrec d varId  -- less verbose, more readable

instance GEq (AstVarName s) where
  geq (AstVarName @_ @y1 varId1) (AstVarName @_ @y2 varId2) =
    case varId1 == varId2 of
      True | Just Refl <- sameTensorKind @y1 @y2 -> Just Refl
      True -> error "geq: different types of same AstVarName"
      False -> Nothing

instance GCompare (AstVarName s) where
  gcompare (AstVarName @_ @y1 varId1) (AstVarName @_ @y2 varId2) =
    case compare varId1 varId2 of
       LT -> GLT
       EQ | Just Refl <- sameTensorKind @y1 @y2 -> GEQ
       EQ -> error "gcompare: different types of same AstVarName"
       GT -> GGT

instance GShow (AstVarName s) where
  gshowsPrec = defaultGshowsPrec

instance DMap.Enum1 (AstVarName s) where
  type Enum1Info (AstVarName s) = Some (Dict TensorKind)
  fromEnum1 (AstVarName @_ @a varId) = (fromEnum varId, Some @_ @a Dict)
  toEnum1 varIdInt (Some @_ @a Dict) = Some $ AstVarName @s @a $ toEnum varIdInt

mkAstVarName :: forall s y. TensorKind y => AstVarId -> AstVarName s y
mkAstVarName = AstVarName

varNameToAstVarId :: AstVarName s y -> AstVarId
varNameToAstVarId (AstVarName varId) = varId

tensorKindFromAstVarName :: AstVarName s y -> Dict TensorKind y
tensorKindFromAstVarName AstVarName{} = Dict

-- The reverse derivative artifact from step 6) of our full pipeline.
type role AstArtifactRev nominal nominal
data AstArtifactRev x z = AstArtifactRev
  { artVarDtRev      :: AstVarName PrimalSpan (ADTensorKind z)
  , artVarDomainRev  :: AstVarName PrimalSpan x
  , artDerivativeRev :: AstTensor AstMethodLet PrimalSpan (ADTensorKind x)
  , artPrimalRev     :: AstTensor AstMethodLet PrimalSpan z
  }

-- The forward derivative artifact.
type role AstArtifactFwd nominal nominal
data AstArtifactFwd x z = AstArtifactFwd
  { artVarDsFwd      :: AstVarName PrimalSpan (ADTensorKind x)
  , artVarDomainFwd  :: AstVarName PrimalSpan x
  , artDerivativeFwd :: AstTensor AstMethodLet PrimalSpan (ADTensorKind z)
  , artPrimalFwd     :: AstTensor AstMethodLet PrimalSpan z
  }

-- | This is the (arbitrarily) chosen representation of terms denoting
-- integers in the indexes of tensor operations.
type AstInt ms = AstTensor ms PrimalSpan (TKR Int64 0)

-- TODO: type IntVarNameF = AstVarName PrimalSpan Int64
type IntVarName = AstVarName PrimalSpan (TKR Int64 0)

pattern AstIntVar :: IntVarName -> AstInt ms
pattern AstIntVar var = AstVar (FTKR ZSR) var

isRankedInt :: forall s y ms. (AstSpan s, TensorKind y)
            => AstTensor ms s y
            -> Maybe (AstTensor ms s y :~: AstInt ms)
isRankedInt _ = case ( sameAstSpan @s @PrimalSpan
                     , sameTensorKind @y @(TKR Int64 0) ) of
                  (Just Refl, Just Refl) -> Just Refl
                  _ -> Nothing

type AstIndex ms n = Index n (AstInt ms)

type AstVarList n = SizedList n IntVarName

type AstIndexS ms sh = IndexS sh (AstInt ms)

type AstVarListS sh = SizedListS sh (Const IntVarName)

type AstIndexX ms sh = IxX sh (AstInt ms)

type AstVarListX sh = ListX sh (Const IntVarName)


-- * AstBindingsCase and AstBindings

type AstBindingsCase y = AstTensor AstMethodLet PrimalSpan y

type AstBindings = DEnumMap (AstVarName PrimalSpan)
                            (AstTensor AstMethodLet PrimalSpan)


-- * ASTs

type data AstMethodOfSharing = AstMethodShare | AstMethodLet

-- | AST for ranked and shaped tensors that are meant to be differentiated.
type role AstTensor nominal nominal nominal
  -- r has to be nominal, because type class arguments always are
data AstTensor :: AstMethodOfSharing -> AstSpanType -> TensorKindType -> Type where
  -- Here starts the general part.
  AstScalar :: GoodScalar r
            => AstTensor ms s (TKScalar r) -> AstTensor ms s (TKR r 0)
  AstUnScalar :: GoodScalar r
              => AstTensor ms s (TKR r 0) -> AstTensor ms s (TKScalar r)
  AstPair :: (TensorKind y, TensorKind z)
           => AstTensor ms s y -> AstTensor ms s z
           -> AstTensor ms s (TKProduct y z)
  AstProject1 :: forall x z s ms. (TensorKind x, TensorKind z)
              => AstTensor ms s (TKProduct x z) -> AstTensor ms s x
  AstProject2 :: forall x z s ms. (TensorKind x, TensorKind z)
              => AstTensor ms s (TKProduct x z) -> AstTensor ms s z
  AstVar :: TensorKind y
         => TensorKindFull y -> AstVarName s y -> AstTensor ms s y
  AstPrimalPart :: TensorKind y
                => AstTensor ms FullSpan y -> AstTensor ms PrimalSpan y
  AstDualPart :: TensorKind y
              => AstTensor ms FullSpan y -> AstTensor ms DualSpan y
  AstConstant :: TensorKind y
              => AstTensor ms PrimalSpan y -> AstTensor ms FullSpan y
  AstD :: TensorKind y
       => AstTensor ms PrimalSpan y -> AstTensor ms DualSpan y
       -> AstTensor ms FullSpan y
  AstCond :: TensorKind y
          => AstBool ms -> AstTensor ms s y -> AstTensor ms s y -> AstTensor ms s y
  AstReplicate :: TensorKind y
               => SNat k -> AstTensor ms s y -> AstTensor ms s (BuildTensorKind k y)
  AstBuild1 :: TensorKind y
            => SNat k -> (IntVarName, AstTensor ms s y)
            -> AstTensor ms s (BuildTensorKind k y)
  AstLet :: forall y z s s2. (AstSpan s, TensorKind y, TensorKind z)
         => AstVarName s y -> AstTensor AstMethodLet s y
         -> AstTensor AstMethodLet s2 z
         -> AstTensor AstMethodLet s2 z
  AstShare :: TensorKind y
           => AstVarName s y -> AstTensor AstMethodShare s y
           -> AstTensor AstMethodShare s y
  AstToShare :: AstTensor AstMethodLet s y
             -> AstTensor AstMethodShare s y

  -- Here starts the ranked part.
  -- The r variable is often existential here, so a proper specialization needs
  -- to be picked explicitly at runtime.
  AstMinIndex :: (GoodScalar r, KnownNat n, GoodScalar r2)
              => AstTensor ms PrimalSpan (TKR r (1 + n))
              -> AstTensor ms PrimalSpan (TKR r2 n)
  AstMaxIndex :: (GoodScalar r, KnownNat n, GoodScalar r2)
              => AstTensor ms PrimalSpan (TKR r (1 + n))
              -> AstTensor ms PrimalSpan (TKR r2 n)
  AstFloor :: (GoodScalar r, RealFrac r, GoodScalar r2, Integral r2, KnownNat n)
           => AstTensor ms PrimalSpan (TKR r n) -> AstTensor ms PrimalSpan (TKR r2 n)
  AstIota :: GoodScalar r => AstTensor ms PrimalSpan (TKR r 1)

  -- For the numeric classes:
  AstN1 :: (GoodScalar r, KnownNat n)
        => OpCodeNum1 -> AstTensor ms s (TKR r n) -> AstTensor ms s (TKR r n)
  AstN2 :: (GoodScalar r, KnownNat n)
        => OpCodeNum2 -> AstTensor ms s (TKR r n) -> AstTensor ms s (TKR r n)
        -> AstTensor ms s (TKR r n)
  AstR1 :: (Differentiable r, GoodScalar r, KnownNat n)
        => OpCode1 -> AstTensor ms s (TKR r n) -> AstTensor ms s (TKR r n)
  AstR2 :: (Differentiable r, GoodScalar r, KnownNat n)
        => OpCode2 -> AstTensor ms s (TKR r n) -> AstTensor ms s (TKR r n)
        -> AstTensor ms s (TKR r n)
  AstI2 :: (Integral r, GoodScalar r, KnownNat n)
        => OpCodeIntegral2 -> AstTensor ms s (TKR r n) -> AstTensor ms s (TKR r n)
        -> AstTensor ms s (TKR r n)
  AstSumOfList :: (GoodScalar r, KnownNat n)
               => [AstTensor ms s (TKR r n)] -> AstTensor ms s (TKR r n)

  -- For the main part of the RankedTensor class:
  AstIndex :: forall m n r s ms. (KnownNat m, KnownNat n, GoodScalar r)
           => AstTensor ms s (TKR r (m + n)) -> AstIndex ms m
           -> AstTensor ms s (TKR r n)
    -- first ix is for outermost dimension; empty index means identity,
    -- if index is out of bounds, the result is defined and is 0,
    -- but vectorization is permitted to change the value
  AstSum :: (KnownNat n, GoodScalar r)
         => AstTensor ms s (TKR r (1 + n)) -> AstTensor ms s (TKR r n)
  AstScatter :: forall m n p r s ms. (KnownNat m, KnownNat n, KnownNat p, GoodScalar r)
             => IShR (p + n)
             -> AstTensor ms s (TKR r (m + n)) -> (AstVarList m, AstIndex ms p)
             -> AstTensor ms s (TKR r (p + n))

  AstFromVector :: (KnownNat n, GoodScalar r)
                => Data.Vector.Vector (AstTensor ms s (TKR r n)) -> AstTensor ms s (TKR r (1 + n))
  AstAppend :: (KnownNat n, GoodScalar r)
            => AstTensor ms s (TKR r (1 + n)) -> AstTensor ms s (TKR r (1 + n))
            -> AstTensor ms s (TKR r (1 + n))
  AstSlice :: (KnownNat n, GoodScalar r)
           => Int -> Int -> AstTensor ms s (TKR r (1 + n))
           -> AstTensor ms s (TKR r (1 + n))
  AstReverse :: (KnownNat n, GoodScalar r)
             => AstTensor ms s (TKR r (1 + n)) -> AstTensor ms s (TKR r (1 + n))
  AstTranspose :: (KnownNat n, GoodScalar r)
               => Permutation.PermR -> AstTensor ms s (TKR r n) -> AstTensor ms s (TKR r n)
  AstReshape :: (KnownNat n, KnownNat m, GoodScalar r)
             => IShR m -> AstTensor ms s (TKR r n) -> AstTensor ms s (TKR r m)
  AstGather :: forall m n p r s ms. (KnownNat m, KnownNat n, KnownNat p, GoodScalar r)
            => IShR (m + n)
            -> AstTensor ms s (TKR r (p + n)) -> (AstVarList m, AstIndex ms p)
            -> AstTensor ms s (TKR r (m + n))
    -- out of bounds indexing is permitted
  -- There are existential variables here, as well.
  AstCast :: (GoodScalar r1, RealFrac r1, RealFrac r2, GoodScalar r2, KnownNat n)
          => AstTensor ms s (TKR r1 n) -> AstTensor ms s (TKR r2 n)
  AstFromIntegral :: (GoodScalar r1, Integral r1, GoodScalar r2, KnownNat n)
                  => AstTensor ms PrimalSpan (TKR r1 n) -> AstTensor ms PrimalSpan (TKR r2 n)
  AstConst :: forall n r ms. (GoodScalar r, KnownNat n)
           => Nested.Ranked n r -> AstTensor ms PrimalSpan (TKR r n)
  AstProjectR :: (GoodScalar r, KnownNat n)
             => AstTensor ms s TKUntyped -> Int -> AstTensor ms s (TKR r n)
  AstLetHVectorIn :: forall s s2 z. (AstSpan s, TensorKind z)
                  => [AstDynamicVarName] -> AstTensor AstMethodLet s TKUntyped
                  -> AstTensor AstMethodLet s2 z
                  -> AstTensor AstMethodLet s2 z
  AstRFromS :: (KnownShS sh, GoodScalar r)
            => AstTensor ms s (TKS r sh) -> AstTensor ms s (TKR r (Rank sh))

  -- Here starts the shaped part.
  AstMinIndexS :: ( KnownShS sh, KnownNat n, GoodScalar r, GoodScalar r2
                  , GoodScalar r2, KnownShS (Init (n ': sh)) )
               => AstTensor ms PrimalSpan (TKS r (n ': sh))
               -> AstTensor ms PrimalSpan (TKS r2 (Init (n ': sh)))
  AstMaxIndexS :: ( KnownShS sh, KnownNat n, GoodScalar r, GoodScalar r2
                  , GoodScalar r2, KnownShS (Init (n ': sh)) )
               => AstTensor ms PrimalSpan (TKS r (n ': sh))
               -> AstTensor ms PrimalSpan (TKS r2 (Init (n ': sh)))
  AstFloorS :: ( GoodScalar r, RealFrac r, Integral r2, GoodScalar r2
               , KnownShS sh )
            => AstTensor ms PrimalSpan (TKS r sh)
            -> AstTensor ms PrimalSpan (TKS r2 sh)
  AstIotaS :: forall n r ms. (GoodScalar r, KnownNat n)
           => AstTensor ms PrimalSpan (TKS r '[n])

  -- For the numeric classes:
  AstN1S :: (GoodScalar r, KnownShS sh)
         => OpCodeNum1 -> AstTensor ms s (TKS r sh) -> AstTensor ms s (TKS r sh)
  AstN2S :: (GoodScalar r, KnownShS sh)
         => OpCodeNum2 -> AstTensor ms s (TKS r sh) -> AstTensor ms s (TKS r sh)
         -> AstTensor ms s (TKS r sh)
  AstR1S :: (Differentiable r, GoodScalar r, KnownShS sh)
         => OpCode1 -> AstTensor ms s (TKS r sh) -> AstTensor ms s (TKS r sh)
  AstR2S :: (Differentiable r, GoodScalar r, KnownShS sh)
         => OpCode2 -> AstTensor ms s (TKS r sh) -> AstTensor ms s (TKS r sh)
         -> AstTensor ms s (TKS r sh)
  AstI2S :: (Integral r, GoodScalar r, KnownShS sh)
         => OpCodeIntegral2 -> AstTensor ms s (TKS r sh) -> AstTensor ms s (TKS r sh)
         -> AstTensor ms s (TKS r sh)
  AstSumOfListS :: (KnownShS sh, GoodScalar r)
                => [AstTensor ms s (TKS r sh)] -> AstTensor ms s (TKS r sh)

  -- For the main part of the ShapedTensor class:
  AstIndexS :: forall sh1 sh2 s r ms.
               (KnownShS sh1, KnownShS sh2, KnownShS (sh1 ++ sh2), GoodScalar r)
            => AstTensor ms s (TKS r (sh1 ++ sh2)) -> AstIndexS ms sh1
            -> AstTensor ms s (TKS r sh2)
    -- first ix is for outermost dimension; empty index means identity,
    -- if index is out of bounds, the result is defined and is 0,
    -- but vectorization is permitted to change the value
  AstSumS :: forall n sh r s ms. (KnownNat n, KnownShS sh, GoodScalar r)
          => AstTensor ms s (TKS r (n ': sh)) -> AstTensor ms s (TKS r sh)
  AstScatterS :: forall sh2 p sh r s ms.
                 ( KnownShS sh2, KnownShS sh, KnownNat p
                 , KnownShS (Take p sh), KnownShS (Drop p sh)
                 , KnownShS (sh2 ++ Drop p sh), GoodScalar r )
              => AstTensor ms s (TKS r (sh2 ++ Drop p sh))
              -> (AstVarListS sh2, AstIndexS ms (Take p sh))
              -> AstTensor ms s (TKS r sh)

  AstFromVectorS :: (KnownNat n, KnownShS sh, GoodScalar r)
                 => Data.Vector.Vector (AstTensor ms s (TKS r sh))
                 -> AstTensor ms s (TKS r (n ': sh))
  AstAppendS :: (KnownNat n, KnownNat m, KnownShS sh, GoodScalar r)
             => AstTensor ms s (TKS r (m ': sh)) -> AstTensor ms s (TKS r (n ': sh))
             -> AstTensor ms s (TKS r ((m + n) ': sh))
  AstSliceS :: (KnownNat i, KnownNat n, KnownNat k, KnownShS sh, GoodScalar r)
            => AstTensor ms s (TKS r (i + n + k ': sh)) -> AstTensor ms s (TKS r (n ': sh))
  AstReverseS :: (KnownNat n, KnownShS sh, GoodScalar r)
              => AstTensor ms s (TKS r (n ': sh)) -> AstTensor ms s (TKS r (n ': sh))
  AstTransposeS :: forall perm sh r s ms.
                   (PermC perm, KnownShS sh, Rank perm <= Rank sh, GoodScalar r)
                => Permutation.Perm perm -> AstTensor ms s (TKS r sh)
                -> AstTensor ms s (TKS r (Permutation.PermutePrefix perm sh))
  AstReshapeS :: (KnownShS sh, Nested.Product sh ~ Nested.Product sh2, GoodScalar r, KnownShS sh2)
              => AstTensor ms s (TKS r sh) -> AstTensor ms s (TKS r sh2)
    -- beware that the order of type arguments is different than in orthotope
    -- and than the order of value arguments in the ranked version
  AstGatherS :: forall sh2 p sh r s ms.
                ( GoodScalar r, KnownShS sh, KnownShS sh2, KnownNat p
                , KnownShS (Take p sh), KnownShS (Drop p sh)
                , KnownShS (sh2 ++ Drop p sh) )
             => AstTensor ms s (TKS r sh)
             -> (AstVarListS sh2, AstIndexS ms (Take p sh))
             -> AstTensor ms s (TKS r (sh2 ++ Drop p sh))
    -- out of bounds indexing is permitted
  AstCastS :: (GoodScalar r1, RealFrac r1, GoodScalar r2, RealFrac r2, KnownShS sh)
           => AstTensor ms s (TKS r1 sh) -> AstTensor ms s (TKS r2 sh)
  AstFromIntegralS :: (GoodScalar r1, Integral r1, GoodScalar r2, KnownShS sh)
                   => AstTensor ms PrimalSpan (TKS r1 sh)
                   -> AstTensor ms PrimalSpan (TKS r2 sh)
  AstConstS :: forall sh r ms. (GoodScalar r, KnownShS sh)
            => Nested.Shaped sh r -> AstTensor ms PrimalSpan (TKS r sh)
  AstProjectS :: (GoodScalar r, KnownShS sh)
              => AstTensor ms s TKUntyped -> Int -> AstTensor ms s (TKS r sh)
  AstSFromR :: (KnownShS sh, KnownNat (Rank sh), GoodScalar r)
            => AstTensor ms s (TKR r (Rank sh)) -> AstTensor ms s (TKS r sh)

  -- Here starts the mixed part.
  AstMinIndexX :: ( KnownShX sh, KnownNat n, GoodScalar r, GoodScalar r2
                  , GoodScalar r2, KnownShX (Init (Just n ': sh)) )
               => AstTensor ms PrimalSpan (TKX r (Just n ': sh))
               -> AstTensor ms PrimalSpan (TKX r2 (Init (Just n ': sh)))
  AstMaxIndexX :: ( KnownShX sh, KnownNat n, GoodScalar r, GoodScalar r2
                  , GoodScalar r2, KnownShX (Init (Just n ': sh)) )
               => AstTensor ms PrimalSpan (TKX r (Just n ': sh))
               -> AstTensor ms PrimalSpan (TKX r2 (Init (Just n ': sh)))
  AstFloorX :: ( GoodScalar r, RealFrac r, Integral r2, GoodScalar r2
               , KnownShX sh )
            => AstTensor ms PrimalSpan (TKX r sh)
            -> AstTensor ms PrimalSpan (TKX r2 sh)
  AstIotaX :: forall n r ms. (GoodScalar r, KnownNat n)
           => AstTensor ms PrimalSpan (TKX r '[Just n])

  -- For the numeric classes:
  AstN1X :: (GoodScalar r, KnownShX sh)
         => OpCodeNum1 -> AstTensor ms s (TKX r sh) -> AstTensor ms s (TKX r sh)
  AstN2X :: (GoodScalar r, KnownShX sh)
         => OpCodeNum2 -> AstTensor ms s (TKX r sh) -> AstTensor ms s (TKX r sh)
         -> AstTensor ms s (TKX r sh)
  AstR1X :: (Differentiable r, GoodScalar r, KnownShX sh)
         => OpCode1 -> AstTensor ms s (TKX r sh) -> AstTensor ms s (TKX r sh)
  AstR2X :: (Differentiable r, GoodScalar r, KnownShX sh)
         => OpCode2 -> AstTensor ms s (TKX r sh) -> AstTensor ms s (TKX r sh)
         -> AstTensor ms s (TKX r sh)
  AstI2X :: (Integral r, GoodScalar r, KnownShX sh)
         => OpCodeIntegral2 -> AstTensor ms s (TKX r sh)
         -> AstTensor ms s (TKX r sh)
         -> AstTensor ms s (TKX r sh)
  AstSumOfListX :: (KnownShX sh, GoodScalar r)
                => [AstTensor ms s (TKX r sh)] -> AstTensor ms s (TKX r sh)

  AstIndexX :: forall sh1 sh2 s r ms.
               (KnownShX sh1, KnownShX sh2, KnownShX (sh1 ++ sh2), GoodScalar r)
            => AstTensor ms s (TKX r (sh1 ++ sh2)) -> AstIndexX ms sh1
            -> AstTensor ms s (TKX r sh2)
    -- first ix is for outermost dimension; empty index means identity,
    -- if index is out of bounds, the result is defined and is 0,
    -- but vectorization is permitted to change the value
  AstSumX :: forall n sh r s ms. (KnownNat n, KnownShX sh, GoodScalar r)
          => AstTensor ms s (TKX r (Just n ': sh)) -> AstTensor ms s (TKX r sh)
  AstScatterX :: forall sh2 p sh r s ms.
                 ( KnownShX sh2, KnownShX sh, KnownNat p
                 , KnownShX (Take p sh), KnownShX (Drop p sh)
                 , KnownShX (sh2 ++ Drop p sh), GoodScalar r )
              => AstTensor ms s (TKX r (sh2 ++ Drop p sh))
              -> (AstVarListX sh2, AstIndexX ms (Take p sh))
              -> AstTensor ms s (TKX r sh)

  AstFromVectorX :: (KnownNat n, KnownShX sh, GoodScalar r)
                 => Data.Vector.Vector (AstTensor ms s (TKX r sh))
                 -> AstTensor ms s (TKX r (Just n ': sh))
  AstAppendX :: (KnownNat n, KnownNat m, KnownShX sh, GoodScalar r)
             => AstTensor ms s (TKX r (Just m ': sh)) -> AstTensor ms s (TKX r (Just n ': sh))
             -> AstTensor ms s (TKX r (Just (m + n) ': sh))
  AstSliceX :: (KnownNat i, KnownNat n, KnownNat k, KnownShX sh, GoodScalar r)
            => AstTensor ms s (TKX r (Just (i + n + k) ': sh)) -> AstTensor ms s (TKX r (Just n ': sh))
  AstReverseX :: (KnownNat n, KnownShX sh, GoodScalar r)
              => AstTensor ms s (TKX r (Just n ': sh)) -> AstTensor ms s (TKX r (Just n ': sh))
  AstTransposeX :: forall perm sh r s ms.
                   (PermC perm, KnownShX sh, Rank perm <= Rank sh, GoodScalar r)
                => Permutation.Perm perm -> AstTensor ms s (TKX r sh)
                -> AstTensor ms s (TKX r (Permutation.PermutePrefix perm sh))
  AstReshapeX :: (KnownShX sh, GoodScalar r, KnownShX sh2)
              => IShX sh2 -> AstTensor ms s (TKX r sh)
              -> AstTensor ms s (TKX r sh2)
    -- beware that the order of type arguments is different than in orthotope
    -- and than the order of value arguments in the ranked version
  AstGatherX :: forall sh2 p sh r s ms.
                ( GoodScalar r, KnownShX sh, KnownShX sh2, KnownNat p
                , KnownShX (Take p sh), KnownShX (Drop p sh)
                , KnownShX (sh2 ++ Drop p sh) )
             => AstTensor ms s (TKX r sh)
             -> (AstVarListX sh2, AstIndexX ms (Take p sh))
             -> AstTensor ms s (TKX r (sh2 ++ Drop p sh))
    -- out of bounds indexing is permitted
  AstCastX :: (GoodScalar r1, RealFrac r1, GoodScalar r2, RealFrac r2, KnownShX sh)
           => AstTensor ms s (TKX r1 sh) -> AstTensor ms s (TKX r2 sh)
  AstFromIntegralX :: (GoodScalar r1, Integral r1, GoodScalar r2, KnownShX sh)
                   => AstTensor ms PrimalSpan (TKX r1 sh)
                   -> AstTensor ms PrimalSpan (TKX r2 sh)
  AstConstX :: forall sh r ms. (GoodScalar r, KnownShX sh)
            => Nested.Mixed sh r -> AstTensor ms PrimalSpan (TKX r sh)
  AstProjectX :: (GoodScalar r, KnownShX sh)
              => AstTensor ms s TKUntyped -> Int -> AstTensor ms s (TKX r sh)
  AstXFromR :: (KnownShX sh, KnownNat (Rank sh), GoodScalar r)
            => AstTensor ms s (TKR r (Rank sh)) -> AstTensor ms s (TKX r sh)

  -- Here starts the misc part

  -- There are existential variables inside DynamicTensor here.
  AstMkHVector :: HVector (AstTensor ms s) -> AstTensor ms s TKUntyped
  AstHApply :: (TensorKind x, TensorKind z)
            => AstHFun x z -> AstTensor ms s x -> AstTensor ms s z
  -- The operations below is why we need AstTensor ms s TKUntyped.
  -- If we kept a vector of terms instead, we'd need to let-bind in each
  -- of the terms separately, duplicating the let-bound term.
  AstBuildHVector1 :: SNat k -> (IntVarName, AstTensor ms s TKUntyped)
                   -> AstTensor ms s TKUntyped
  AstMapAccumRDer
    :: (TensorKind accShs, TensorKind bShs, TensorKind eShs)
    => SNat k
    -> TensorKindFull accShs
    -> TensorKindFull bShs
    -> TensorKindFull eShs
    -> AstHFun (TKProduct accShs eShs) (TKProduct accShs bShs)
    -> AstHFun (TKProduct (ADTensorKind (TKProduct accShs eShs))
                          (TKProduct accShs eShs))
               (ADTensorKind (TKProduct accShs bShs))
    -> AstHFun (TKProduct (ADTensorKind (TKProduct accShs bShs))
                          (TKProduct accShs eShs))
               (ADTensorKind (TKProduct accShs eShs))
    -> AstTensor ms s accShs
    -> AstTensor ms s (BuildTensorKind k eShs)
    -> AstTensor ms s (TKProduct accShs (BuildTensorKind k bShs))
  AstMapAccumLDer
    :: (TensorKind accShs, TensorKind bShs, TensorKind eShs)
    => SNat k
    -> TensorKindFull accShs
    -> TensorKindFull bShs
    -> TensorKindFull eShs
    -> AstHFun (TKProduct accShs eShs) (TKProduct accShs bShs)
    -> AstHFun (TKProduct (ADTensorKind (TKProduct accShs eShs))
                          (TKProduct accShs eShs))
               (ADTensorKind (TKProduct accShs bShs))
    -> AstHFun (TKProduct (ADTensorKind (TKProduct accShs bShs))
                          (TKProduct accShs eShs))
               (ADTensorKind (TKProduct accShs eShs))
    -> AstTensor ms s accShs
    -> AstTensor ms s (BuildTensorKind k eShs)
    -> AstTensor ms s (TKProduct accShs (BuildTensorKind k bShs))

deriving instance Show (AstTensor ms s y)

type AstDynamic ms (s :: AstSpanType) = DynamicTensor (AstTensor ms s)

type role AstHFun nominal nominal
data AstHFun x z where
  AstLambda :: TensorKind x
            => ~( AstVarName PrimalSpan x, TensorKindFull x
                , AstTensor AstMethodLet PrimalSpan z )
            -> AstHFun x z
    -- ^ The function body can't have any free variables outside those
    -- listed in the first component of the pair; this reflects
    -- the quantification in 'rrev' and prevents cotangent confusion.
    --
    -- The constructor is non-strict in order not to pre-compute
    -- higher derivatives (e.g., inside folds) that are never going to be used.
    -- As a side effect, all lambdas (closed functions) are processed
    -- lazily, which makes no harm, since they have no outside free variables
    -- and so can't easiliy induce leaks by retaining outside values (e.g.,
    -- big environments from which values for the variables would be drawn).
    -- The cost of computing a reverse derivative of a fold nested inside
    -- the function argument n times is reduced by the laziness from 20^n
    -- to under 2^n (TODO: determine the exact cost). Note, however,
    -- that if the n-th forward and reverse derivative is taken,
    -- the laziness is defeated.

deriving instance Show (AstHFun x z)

type role AstBool nominal
data AstBool ms where
  AstBoolNot :: AstBool ms -> AstBool ms
  AstB2 :: OpCodeBool -> AstBool ms -> AstBool ms -> AstBool ms
  AstBoolConst :: Bool -> AstBool ms
  -- There are existential variables here, as well.
  AstRel :: TensorKind y
         => OpCodeRel -> AstTensor ms PrimalSpan y -> AstTensor ms PrimalSpan y
         -> AstBool ms
deriving instance Show (AstBool ms)

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
instance Eq (AstTensor ms s y) where
  (==) = error "AST requires that EqF be used instead"
  (/=) = error "AST requires that EqF be used instead"

instance Ord (AstTensor ms s y) where
  (<=) = error "AST requires that OrdF be used instead"

instance (Num (Nested.Ranked n r), AstSpan s, GoodScalar r, KnownNat n)
         => Num (AstTensor ms s (TKR r n)) where
  -- The normal form has AstConst, if any, as the first element of the list.
  -- All lists fully flattened and length >= 2.
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
  u - v = AstN2 MinusOp u v

  AstConst u * AstConst v = AstConst (u * v)  -- common in indexing
  u * v = AstN2 TimesOp u v

  negate (AstConst u) = AstConst $ negate u  -- common in indexing
  negate u = AstN1 NegateOp u
  abs = AstN1 AbsOp
  signum = AstN1 SignumOp
  fromInteger :: Integer -> AstTensor ms s (TKR r n)
  fromInteger i = case sameNat (Proxy @n) (Proxy @0) of
    Just Refl -> fromPrimal . AstConst . fromInteger $ i
    Nothing -> error $ "fromInteger not defined for Ast of non-zero ranks: "
                       ++ show (i, valueOf @n :: Int)
    -- it's crucial that there is no AstConstant in fromInteger code
    -- so that we don't need 4 times the simplification rules

-- Warning: div and mod operations are very costly (simplifying them
-- requires constructing conditionals, etc). If this error is removed,
-- they are going to work, but slowly.
instance (GoodScalar r, Integral r, KnownNat n)
         => IntegralF (AstTensor ms s (TKR r n)) where
  quotF = AstI2 QuotOp
  remF = AstI2 RemOp

instance (GoodScalar r, Differentiable r, Fractional (Nested.Ranked n r), AstSpan s, KnownNat n)
         => Fractional (AstTensor ms s (TKR r n)) where
  u / v = AstR2 DivideOp u v
  recip = AstR1 RecipOp
  fromRational r = error $ "fromRational not defined for Ast: "
                           ++ show r

instance (GoodScalar r, Differentiable r, Floating (Nested.Ranked n r), AstSpan s, KnownNat n)
         => Floating (AstTensor ms s (TKR r n)) where
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

instance (GoodScalar r, Differentiable r, Floating (Nested.Ranked n r), AstSpan s, KnownNat n)
         => RealFloatF (AstTensor ms s (TKR r n)) where
  atan2F = AstR2 Atan2Op


-- * Unlawful numeric instances of shaped AST; they are lawful modulo evaluation

instance (GoodScalar r, Num (Nested.Shaped sh r), KnownShS sh)
         => Num (AstTensor ms s (TKS r sh)) where
  -- The normal form has AstConst, if any, as the first element of the list.
  -- All lists fully flattened and length >= 2.
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
  u - v = AstN2S MinusOp u v

  AstConstS u * AstConstS v = AstConstS (u * v)  -- common in indexing
  u * v = AstN2S TimesOp u v

  negate = AstN1S NegateOp
  abs = AstN1S AbsOp
  signum = AstN1S SignumOp
  fromInteger i = error $ "fromInteger not defined for AstShaped: "
                          ++ show i

-- Warning: div and mod operations are very costly (simplifying them
-- requires constructing conditionals, etc). If this error is removed,
-- they are going to work, but slowly.
instance (Integral r, GoodScalar r, KnownShS sh)
         => IntegralF (AstTensor ms s (TKS r sh)) where
  quotF = AstI2S QuotOp
  remF = AstI2S RemOp

instance ( GoodScalar r, Differentiable r, Fractional (Nested.Shaped sh r)
         , KnownShS sh )
         => Fractional (AstTensor ms s (TKS r sh)) where
  u / v = AstR2S DivideOp u v
  recip = AstR1S RecipOp
  fromRational r = error $ "fromRational not defined for AstShaped: "
                           ++ show r

instance (GoodScalar r, Differentiable r, KnownShS sh, Floating (Nested.Shaped sh r), AstSpan s)
         => Floating (AstTensor ms s (TKS r sh)) where
  pi = fromPrimal $ AstConstS pi
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

instance (GoodScalar r, Differentiable r, KnownShS sh, Floating (Nested.Shaped sh r), AstSpan s)
         => RealFloatF (AstTensor ms s (TKS r sh)) where
  atan2F = AstR2S Atan2Op


-- mixed

instance (GoodScalar r, Num (Nested.Mixed sh r), KnownShX sh)
         => Num (AstTensor ms s (TKX r sh)) where
  -- The normal form has AstConst, if any, as the first element of the list.
  -- All lists fully flattened and length >= 2.
  AstSumOfListX (AstConstX u : lu) + AstSumOfListX (AstConstX v : lv) =
    AstSumOfListX (AstConstX (u + v) : lu ++ lv)
  AstSumOfListX lu + AstSumOfListX (AstConstX v : lv) =
    AstSumOfListX (AstConstX v : lv ++ lu)
  AstSumOfListX lu + AstSumOfListX lv = AstSumOfListX (lu ++ lv)

  AstConstX u + AstSumOfListX (AstConstX v : lv) =
    AstSumOfListX (AstConstX (u + v) : lv)
  u + AstSumOfListX (AstConstX v : lv) = AstSumOfListX (AstConstX v : u : lv)
  u + AstSumOfListX lv = AstSumOfListX (u : lv)

  AstSumOfListX (AstConstX u : lu) + AstConstX v =
    AstSumOfListX (AstConstX (u + v) : lu)
  AstSumOfListX (AstConstX u : lu) + v = AstSumOfListX (AstConstX u : v : lu)
  AstSumOfListX lu + v = AstSumOfListX (v : lu)

  AstConstX u + AstConstX v = AstConstX (u + v)
  u + AstConstX v = AstSumOfListX [AstConstX v, u]
  u + v = AstSumOfListX [u, v]

  AstConstX u - AstConstX v = AstConstX (u - v)  -- common in indexing
  u - v = AstN2X MinusOp u v

  AstConstX u * AstConstX v = AstConstX (u * v)  -- common in indexing
  u * v = AstN2X TimesOp u v

  negate = AstN1X NegateOp
  abs = AstN1X AbsOp
  signum = AstN1X SignumOp
  fromInteger i = error $ "fromInteger not defined for AstShaped: "
                          ++ show i

-- Warning: div and mod operations are very costly (simplifying them
-- requires constructing conditionals, etc). If this error is removed,
-- they are going to work, but slowly.
instance (Integral r, GoodScalar r, KnownShX sh)
         => IntegralF (AstTensor ms s (TKX r sh)) where
  quotF = AstI2X QuotOp
  remF = AstI2X RemOp

instance ( GoodScalar r, Differentiable r, Fractional (Nested.Mixed sh r)
         , KnownShX sh )
         => Fractional (AstTensor ms s (TKX r sh)) where
  u / v = AstR2X DivideOp u v
  recip = AstR1X RecipOp
  fromRational r = error $ "fromRational not defined for AstShaped: "
                           ++ show r

instance (GoodScalar r, Differentiable r, KnownShX sh, Floating (Nested.Mixed sh r), AstSpan s)
         => Floating (AstTensor ms s (TKX r sh)) where
  pi = fromPrimal $ AstConstX pi
  exp = AstR1X ExpOp
  log = AstR1X LogOp
  sqrt = AstR1X SqrtOp
  (**) = AstR2X PowerOp
  logBase = AstR2X LogBaseOp
  sin = AstR1X SinOp
  cos = AstR1X CosOp
  tan = AstR1X TanOp
  asin = AstR1X AsinOp
  acos = AstR1X AcosOp
  atan = AstR1X AtanOp
  sinh = AstR1X SinhOp
  cosh = AstR1X CoshOp
  tanh = AstR1X TanhOp
  asinh = AstR1X AsinhOp
  acosh = AstR1X AcoshOp
  atanh = AstR1X AtanhOp

instance (GoodScalar r, Differentiable r, KnownShX sh, Floating (Nested.Mixed sh r), AstSpan s)
         => RealFloatF (AstTensor ms s (TKX r sh)) where
  atan2F = AstR2X Atan2Op

-- * Unlawful instances of AST for bool; they are lawful modulo evaluation

instance Boolean (AstBool ms) where
  true = AstBoolConst True
  false = AstBoolConst False
  notB = AstBoolNot
  AstBoolConst b &&* AstBoolConst c = AstBoolConst $ b && c
                                        -- common in indexing
  b &&* c = AstB2 AndOp b c
  b ||* c = AstB2 OrOp b c


-- * The AstRaw, AstNoVectorize and AstNoSimplify definitions

type instance PrimalOf (AstRaw s) = AstRaw PrimalSpan
type instance DualOf (AstRaw s) = AstTensor AstMethodShare DualSpan
type instance ShareOf (AstRaw s) = AstRaw s
type instance HFunOf (AstRaw s) x y = AstHFun x y

type instance PrimalOf (AstNoVectorize s) = AstNoVectorize PrimalSpan
type instance DualOf (AstNoVectorize s) = AstTensor AstMethodLet DualSpan
type instance ShareOf (AstNoVectorize s) = AstRaw s
type instance HFunOf (AstNoVectorize s) x z = AstHFun x z

type instance PrimalOf (AstNoSimplify s) = AstNoSimplify PrimalSpan
type instance DualOf (AstNoSimplify s) = AstTensor AstMethodLet DualSpan
type instance ShareOf (AstNoSimplify s) = AstRaw s
type instance HFunOf (AstNoSimplify s) x z = AstHFun x z

type role AstRaw nominal nominal
newtype AstRaw s y =
  AstRaw {unAstRaw :: AstTensor AstMethodShare s y}
 deriving Show

type role AstNoVectorize nominal nominal
newtype AstNoVectorize s y =
  AstNoVectorize {unAstNoVectorize :: AstTensor AstMethodLet s y}
 deriving Show

type role AstNoSimplify nominal nominal
newtype AstNoSimplify s y =
  AstNoSimplify {unAstNoSimplify :: AstTensor AstMethodLet s y}
 deriving Show
