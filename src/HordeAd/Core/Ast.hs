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
  , AstVarId, intToAstVarId, AstDynamicVarName(..), dynamicVarNameToAstVarId
  , AstInt, IntVarName, pattern AstIntVar, isRankedInt
  , AstVarName, mkAstVarName, varNameToAstVarId
  , AstArtifact(..), AstArtifactRev(..), AstArtifactFwd(..)
  , AstIndex, AstVarList, AstIndexS, AstVarListS
    -- * AstBindingsCase and AstBindings
  , AstBindingsCase(..), AstBindings
    -- * ASTs
  , AstRanked(..), AstTensor(..), AstShaped(..)
  , AstDynamic, AstHFun(..)
  , AstBool(..), OpCodeNum1(..), OpCodeNum2(..), OpCode1(..), OpCode2(..)
  , OpCodeIntegral2(..), OpCodeBool(..), OpCodeRel(..)
    -- * The AstRaw, AstNoVectorize and AstNoSimplify definitions
  , AstRaw(..), AstRawS(..), AstRawWrap(..)
  , AstNoVectorize(..), AstNoVectorizeS(..), AstNoVectorizeWrap(..)
  , AstNoSimplify(..), AstNoSimplifyS(..), AstNoSimplifyWrap(..)
  ) where

import Prelude hiding (foldl')

import Data.Array.Internal (valueOf)
import Data.Array.Shape qualified as Sh
import Data.Dependent.EnumMap.Strict as DMap
import Data.Functor.Const
import Data.GADT.Compare
import Data.GADT.Show
import Data.Int (Int64)
import Data.Kind (Type)
import Data.Proxy (Proxy (Proxy))
import Data.Some
import Data.Strict.Vector qualified as Data.Vector
import Data.Type.Equality ((:~:) (Refl))
import GHC.TypeLits (KnownNat, sameNat, type (+), type (<=))
import Type.Reflection (Typeable, eqTypeRep, typeRep, (:~~:) (HRefl))

import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape qualified as X
import Data.Array.Mixed.Types qualified as X
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape qualified as Nested.Internal.Shape

import HordeAd.Core.HVector
import HordeAd.Core.Types
import HordeAd.Internal.OrthotopeOrphanInstances
  (IntegralF (..), RealFloatF (..))
import HordeAd.Util.ShapedList (IndexS, SizedListS)
import HordeAd.Util.SizedList

-- * Basic type family instances

type instance RankedOf (AstRanked s) = AstRanked s
type instance ShapedOf (AstRanked s) = AstShaped s
type instance PrimalOf (AstRanked s) = AstRanked PrimalSpan
type instance DualOf (AstRanked s) = AstRanked DualSpan

type instance HVectorOf (AstRanked s) = AstTensor s TKUntyped
-- This can't be just HFun, because they need to be vectorized
-- and vectorization applies such functions to the variable from build1
-- and the variable has to be eliminated via vectorization to preserve
-- the closed form of the function. Just applying a Haskell closure
-- to the build1 variable and then duplicating the result of the function
-- would not eliminate the variable and also would likely results
-- in more costly computations. Also, that would prevent simplification
-- of the instances, especially after applied to arguments that are terms.
type instance HFunOf (AstRanked s) x y = AstHFun x y

type instance RankedOf (AstShaped s) = AstRanked s
type instance PrimalOf (AstShaped s) = AstShaped PrimalSpan
type instance DualOf (AstShaped s) = AstShaped DualSpan


-- * The AstSpan kind

-- | A kind (a type intended to be promoted) marking whether an AST term
-- is supposed to denote the primal part of a dual number, the dual part
-- or the whole dual number. It's mainly used to index the terms
-- of the AstTensor and related GADTs.
type data AstSpanType = PrimalSpan | DualSpan | FullSpan

class Typeable s => AstSpan (s :: AstSpanType) where
  fromPrimal :: TensorKind y => AstTensor PrimalSpan y -> AstTensor s y

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

-- TODO: remove the rank field once we have TensorKindType singletons
type role AstVarName nominal nominal
data AstVarName :: AstSpanType -> TensorKindType -> Type where
  AstVarName :: forall s y. TensorKind y => AstVarId -> AstVarName s y

deriving instance Eq (AstVarName s y)
deriving instance Ord (AstVarName s y)

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

-- The reverse derivative artifact from step 6) of our full pipeline.
-- The same type can also hold the forward derivative artifact.
type role AstArtifact nominal nominal
data AstArtifact y z = AstArtifact
  { artVarsDt     :: [AstDynamicVarName]
  , artVarsPrimal :: [AstDynamicVarName]
  , artDerivative :: InterpretationTarget (AstRaw PrimalSpan) y
  , artPrimal     :: InterpretationTarget (AstRaw PrimalSpan) z
  }

-- The reverse derivative artifact from step 6) of our full pipeline.
type role AstArtifactRev nominal nominal
data AstArtifactRev x z = AstArtifactRev
  { artVarDtRev      :: AstVarName PrimalSpan z
  , artVarDomainRev  :: AstVarName PrimalSpan x
  , artDerivativeRev :: InterpretationTarget (AstRaw PrimalSpan) x
  , artPrimalRev     :: InterpretationTarget (AstRaw PrimalSpan) z
  }

-- The forward derivative artifact.
type role AstArtifactFwd nominal nominal
data AstArtifactFwd x z = AstArtifactFwd
  { artVarDsFwd      :: AstVarName PrimalSpan x
  , artVarDomainFwd  :: AstVarName PrimalSpan x
  , artDerivativeFwd :: InterpretationTarget (AstRaw PrimalSpan) z
  , artPrimalFwd     :: InterpretationTarget (AstRaw PrimalSpan) z
  }

-- | This is the (arbitrarily) chosen representation of terms denoting
-- integers in the indexes of tensor operations.
type AstInt = AstTensor PrimalSpan (TKR Int64 0)

-- TODO: type IntVarNameF = AstVarName PrimalSpan Int64
type IntVarName = AstVarName PrimalSpan (TKR Int64 0)

pattern AstIntVar :: IntVarName -> AstInt
pattern AstIntVar var = AstVar (FTKR ZSR) var

isRankedInt :: forall s y. (AstSpan s, TensorKind y)
            => AstTensor s y
            -> Maybe (AstTensor s y :~: AstInt)
isRankedInt _ = case ( sameAstSpan @s @PrimalSpan
                     , sameTensorKind @y @(TKR Int64 0) ) of
                  (Just Refl, Just Refl) -> Just Refl
                  _ -> Nothing

type AstIndex n = Index n AstInt

type AstVarList n = SizedList n IntVarName

type AstIndexS sh = IndexS sh AstInt

type AstVarListS sh = SizedListS sh (Const IntVarName)


-- * AstBindingsCase and AstBindings

type role AstBindingsCase nominal
data AstBindingsCase (s :: AstSpanType) =
    AstBindingsSimple (DynamicTensor (AstRanked s))
  | AstBindingsHVector (HVectorOf (AstRanked s))
deriving instance Show (AstBindingsCase s)

type AstBindings (s :: AstSpanType) = [(AstVarId, AstBindingsCase s)]


-- * ASTs

-- The old AstRanked reconstructed:
type role AstRanked nominal nominal nominal
newtype AstRanked s r n = AstRanked {unAstRanked :: AstTensor s (TKR r n)}
instance GoodScalar r => Show (AstRanked s r n) where
  showsPrec k (AstRanked t) = showsPrec k t
    -- to keep PP tests passing regardless of what wrappers we currently use

-- The old AstShaped reconstructed:
type role AstShaped nominal nominal nominal
newtype AstShaped s r sh = AstShaped {unAstShaped :: AstTensor s (TKS r sh)}
instance GoodScalar r => Show (AstShaped s r sh) where
  showsPrec k (AstShaped t) = showsPrec k t
    -- to keep PP tests passing regardless of what wrappers we currently use

-- | AST for ranked and shaped tensors that are meant to be differentiated.
type role AstTensor nominal nominal
  -- r has to be nominal, because type class arguments always are
data AstTensor :: AstSpanType -> TensorKindType -> Type where
  -- Here starts the general part.
  AstTuple :: (TensorKind y, TensorKind z)
           => AstTensor s y -> AstTensor s z
           -> AstTensor s (TKProduct y z)
  AstProject1 :: forall x z s. TensorKind z
              => AstTensor s (TKProduct x z) -> AstTensor s x
  AstProject2 :: forall x z s. TensorKind x
              => AstTensor s (TKProduct x z) -> AstTensor s z
  AstLetTupleIn :: ( AstSpan s, TensorKind x, TensorKind y, TensorKind z)
                => AstVarName s x -> AstVarName s y
                -> AstTensor s (TKProduct x y)
                -> AstTensor s2 z
                -> AstTensor s2 z
  AstVar :: TensorKind y
         => TensorKindFull y -> AstVarName s y -> AstTensor s y
  AstPrimalPart :: TensorKind y
                => AstTensor FullSpan y -> AstTensor PrimalSpan y
  AstDualPart :: TensorKind y
              => AstTensor FullSpan y -> AstTensor DualSpan y
  AstConstant :: TensorKind y
              => AstTensor PrimalSpan y -> AstTensor FullSpan y
  AstD :: TensorKind y
       => AstTensor PrimalSpan y -> AstTensor DualSpan y
       -> AstTensor FullSpan y
  AstCond :: TensorKind y
          => AstBool -> AstTensor s y -> AstTensor s y -> AstTensor s y
  AstReplicate :: TensorKind y
               => SNat k -> AstTensor s y -> AstTensor s (BuildTensorKind k y)
  AstBuild1 :: TensorKind y
            => SNat k -> (IntVarName, AstTensor s y)
            -> AstTensor s (BuildTensorKind k y)
  AstLet :: forall y z s s2. (AstSpan s, TensorKind y, TensorKind z)
         => AstVarName s y -> AstTensor s y -> AstTensor s2 z -> AstTensor s2 z
  AstShare :: TensorKind y
           => AstVarName s y -> AstTensor s y -> AstTensor s y

  -- Here starts the ranked part.
  -- The r variable is often existential here, so a proper specialization needs
  -- to be picked explicitly at runtime.
  AstMinIndex :: (GoodScalar r, KnownNat n, GoodScalar r2)
              => AstTensor PrimalSpan (TKR r (1 + n))
              -> AstTensor PrimalSpan (TKR r2 n)
  AstMaxIndex :: (GoodScalar r, KnownNat n, GoodScalar r2)
              => AstTensor PrimalSpan (TKR r (1 + n))
              -> AstTensor PrimalSpan (TKR r2 n)
  AstFloor :: (GoodScalar r, RealFrac r, GoodScalar r2, Integral r2, KnownNat n)
           => AstTensor PrimalSpan (TKR r n) -> AstTensor PrimalSpan (TKR r2 n)
  AstIota :: GoodScalar r => AstTensor PrimalSpan (TKR r 1)

  -- For the numeric classes:
  AstN1 :: (GoodScalar r, KnownNat n)
        => OpCodeNum1 -> AstTensor s (TKR r n) -> AstTensor s (TKR r n)
  AstN2 :: (GoodScalar r, KnownNat n)
        => OpCodeNum2 -> AstTensor s (TKR r n) -> AstTensor s (TKR r n)
        -> AstTensor s (TKR r n)
  AstR1 :: (Differentiable r, GoodScalar r, KnownNat n)
        => OpCode1 -> AstTensor s (TKR r n) -> AstTensor s (TKR r n)
  AstR2 :: (Differentiable r, GoodScalar r, KnownNat n)
        => OpCode2 -> AstTensor s (TKR r n) -> AstTensor s (TKR r n)
        -> AstTensor s (TKR r n)
  AstI2 :: (Integral r, GoodScalar r, KnownNat n)
        => OpCodeIntegral2 -> AstTensor s (TKR r n) -> AstTensor s (TKR r n)
        -> AstTensor s (TKR r n)
  AstSumOfList :: (GoodScalar r, KnownNat n)
               => [AstTensor s (TKR r n)] -> AstTensor s (TKR r n)

  -- For the main part of the RankedTensor class:
  AstIndex :: forall m n r s. (KnownNat m, KnownNat n, GoodScalar r)
           => AstTensor s (TKR r (m + n)) -> AstIndex m
           -> AstTensor s (TKR r n)
    -- first ix is for outermost dimension; empty index means identity,
    -- if index is out of bounds, the result is defined and is 0,
    -- but vectorization is permitted to change the value
  AstSum :: (KnownNat n, GoodScalar r)
         => AstTensor s (TKR r (1 + n)) -> AstTensor s (TKR r n)
  AstScatter :: forall m n p r s. (KnownNat m, KnownNat n, KnownNat p, GoodScalar r)
             => IShR (p + n)
             -> AstTensor s (TKR r (m + n)) -> (AstVarList m, AstIndex p)
             -> AstTensor s (TKR r (p + n))

  AstFromVector :: (KnownNat n, GoodScalar r)
                => Data.Vector.Vector (AstTensor s (TKR r n)) -> AstTensor s (TKR r (1 + n))
  AstAppend :: (KnownNat n, GoodScalar r)
            => AstTensor s (TKR r (1 + n)) -> AstTensor s (TKR r (1 + n))
            -> AstTensor s (TKR r (1 + n))
  AstSlice :: (KnownNat n, GoodScalar r)
           => Int -> Int -> AstTensor s (TKR r (1 + n))
           -> AstTensor s (TKR r (1 + n))
  AstReverse :: (KnownNat n, GoodScalar r)
             => AstTensor s (TKR r (1 + n)) -> AstTensor s (TKR r (1 + n))
  AstTranspose :: (KnownNat n, GoodScalar r)
               => Permutation.PermR -> AstTensor s (TKR r n) -> AstTensor s (TKR r n)
  AstReshape :: (KnownNat n, KnownNat m, GoodScalar r)
             => IShR m -> AstTensor s (TKR r n) -> AstTensor s (TKR r m)
  AstGather :: forall m n p r s. (KnownNat m, KnownNat n, KnownNat p, GoodScalar r)
            => IShR (m + n)
            -> AstTensor s (TKR r (p + n)) -> (AstVarList m, AstIndex p)
            -> AstTensor s (TKR r (m + n))
    -- out of bounds indexing is permitted
  -- There are existential variables here, as well.
  AstCast :: (GoodScalar r1, RealFrac r1, RealFrac r2, GoodScalar r2, KnownNat n)
          => AstTensor s (TKR r1 n) -> AstTensor s (TKR r2 n)
  AstFromIntegral :: (GoodScalar r1, Integral r1, GoodScalar r2, KnownNat n)
                  => AstTensor PrimalSpan (TKR r1 n) -> AstTensor PrimalSpan (TKR r2 n)
  AstConst :: forall n r. (GoodScalar r, KnownNat n)
           => Nested.Ranked n r -> AstTensor PrimalSpan (TKR r n)
  AstProjectR :: (GoodScalar r, KnownNat n)
             => AstTensor s TKUntyped -> Int -> AstTensor s (TKR r n)
  AstLetHVectorIn :: (AstSpan s, GoodScalar r, KnownNat n)
                  => [AstDynamicVarName] -> AstTensor s TKUntyped
                  -> AstTensor s2 (TKR r n)
                  -> AstTensor s2 (TKR r n)
  AstLetHFunIn :: (GoodScalar r, KnownNat n, TensorKind x, TensorKind y)
               => AstVarId -> AstHFun x y
               -> AstTensor s2 (TKR r n)
               -> AstTensor s2 (TKR r n)
  AstRFromS :: (KnownShS sh, GoodScalar r)
            => AstTensor s (TKS r sh) -> AstTensor s (TKR r (X.Rank sh))

  -- Here starts the shaped part.
  AstMinIndexS :: ( KnownShS sh, KnownNat n, GoodScalar r, GoodScalar r2
                  , GoodScalar r2, KnownShS (Sh.Init (n ': sh)) )
               => AstTensor PrimalSpan (TKS r (n ': sh))
               -> AstTensor PrimalSpan (TKS r2 (Sh.Init (n ': sh)))
  AstMaxIndexS :: ( KnownShS sh, KnownNat n, GoodScalar r, GoodScalar r2
                  , GoodScalar r2, KnownShS (Sh.Init (n ': sh)) )
               => AstTensor PrimalSpan (TKS r (n ': sh))
               -> AstTensor PrimalSpan (TKS r2 (Sh.Init (n ': sh)))
  AstFloorS :: ( GoodScalar r, RealFrac r, Integral r2, GoodScalar r2
               , KnownShS sh )
            => AstTensor PrimalSpan (TKS r sh)
            -> AstTensor PrimalSpan (TKS r2 sh)
  AstIotaS :: forall n r. (GoodScalar r, KnownNat n)
           => AstTensor PrimalSpan (TKS r '[n])

  -- For the numeric classes:
  AstN1S :: (GoodScalar r, KnownShS sh)
         => OpCodeNum1 -> AstTensor s (TKS r sh) -> AstTensor s (TKS r sh)
  AstN2S :: (GoodScalar r, KnownShS sh)
         => OpCodeNum2 -> AstTensor s (TKS r sh) -> AstTensor s (TKS r sh)
         -> AstTensor s (TKS r sh)
  AstR1S :: (Differentiable r, GoodScalar r, KnownShS sh)
         => OpCode1 -> AstTensor s (TKS r sh) -> AstTensor s (TKS r sh)
  AstR2S :: (Differentiable r, GoodScalar r, KnownShS sh)
         => OpCode2 -> AstTensor s (TKS r sh) -> AstTensor s (TKS r sh)
         -> AstTensor s (TKS r sh)
  AstI2S :: (Integral r, GoodScalar r, KnownShS sh)
         => OpCodeIntegral2 -> AstTensor s (TKS r sh) -> AstTensor s (TKS r sh)
         -> AstTensor s (TKS r sh)
  AstSumOfListS :: (KnownShS sh, GoodScalar r)
                => [AstTensor s (TKS r sh)] -> AstTensor s (TKS r sh)

  -- For the main part of the ShapedTensor class:
  AstIndexS :: forall sh1 sh2 s r.
               (KnownShS sh1, KnownShS sh2, KnownShS (sh1 X.++ sh2), GoodScalar r)
            => AstTensor s (TKS r (sh1 X.++ sh2)) -> AstIndexS sh1
            -> AstTensor s (TKS r sh2)
    -- first ix is for outermost dimension; empty index means identity,
    -- if index is out of bounds, the result is defined and is 0,
    -- but vectorization is permitted to change the value
  AstSumS :: forall n sh r s. (KnownNat n, KnownShS sh, GoodScalar r)
          => AstTensor s (TKS r (n ': sh)) -> AstTensor s (TKS r sh)
  AstScatterS :: forall sh2 p sh r s.
                 ( KnownShS sh2, KnownShS sh, KnownNat p
                 , KnownShS (Sh.Take p sh), KnownShS (Sh.Drop p sh)
                 , KnownShS (sh2 X.++ Sh.Drop p sh), GoodScalar r )
              => AstTensor s (TKS r (sh2 X.++ Sh.Drop p sh))
              -> (AstVarListS sh2, AstIndexS (Sh.Take p sh))
              -> AstTensor s (TKS r sh)

  AstFromVectorS :: (KnownNat n, KnownShS sh, GoodScalar r)
                 => Data.Vector.Vector (AstTensor s (TKS r sh))
                 -> AstTensor s (TKS r (n ': sh))
  AstAppendS :: (KnownNat n, KnownNat m, KnownShS sh, GoodScalar r)
             => AstTensor s (TKS r (m ': sh)) -> AstTensor s (TKS r (n ': sh))
             -> AstTensor s (TKS r ((m + n) ': sh))
  AstSliceS :: (KnownNat i, KnownNat n, KnownNat k, KnownShS sh, GoodScalar r)
            => AstTensor s (TKS r (i + n + k ': sh)) -> AstTensor s (TKS r (n ': sh))
  AstReverseS :: (KnownNat n, KnownShS sh, GoodScalar r)
              => AstTensor s (TKS r (n ': sh)) -> AstTensor s (TKS r (n ': sh))
  AstTransposeS :: forall perm sh r s.
                   (PermC perm, KnownShS sh, X.Rank perm <= X.Rank sh, GoodScalar r)
                => Permutation.Perm perm -> AstTensor s (TKS r sh)
                -> AstTensor s (TKS r (Permutation.PermutePrefix perm sh))
  AstReshapeS :: (KnownShS sh, Nested.Internal.Shape.Product sh ~ Nested.Internal.Shape.Product sh2, GoodScalar r, KnownShS sh2)
              => AstTensor s (TKS r sh) -> AstTensor s (TKS r sh2)
    -- beware that the order of type arguments is different than in orthotope
    -- and than the order of value arguments in the ranked version
  AstGatherS :: forall sh2 p sh r s.
                ( GoodScalar r, KnownShS sh, KnownShS sh2, KnownNat p
                , KnownShS (Sh.Take p sh), KnownShS (Sh.Drop p sh)
                , KnownShS (sh2 X.++ Sh.Drop p sh) )
             => AstTensor s (TKS r sh)
             -> (AstVarListS sh2, AstIndexS (Sh.Take p sh))
             -> AstTensor s (TKS r (sh2 X.++ Sh.Drop p sh))
    -- out of bounds indexing is permitted
  AstCastS :: (GoodScalar r1, RealFrac r1, GoodScalar r2, RealFrac r2, KnownShS sh)
           => AstTensor s (TKS r1 sh) -> AstTensor s (TKS r2 sh)
  AstFromIntegralS :: (GoodScalar r1, Integral r1, GoodScalar r2, KnownShS sh)
                   => AstTensor PrimalSpan (TKS r1 sh)
                   -> AstTensor PrimalSpan (TKS r2 sh)
  AstConstS :: forall sh r. (GoodScalar r, KnownShS sh)
            => Nested.Shaped sh r -> AstTensor PrimalSpan (TKS r sh)
  AstProjectS :: (GoodScalar r, KnownShS sh)
              => AstTensor s TKUntyped -> Int -> AstTensor s (TKS r sh)
  AstLetHVectorInS :: (AstSpan s, KnownShS sh, GoodScalar r)
                   => [AstDynamicVarName] -> AstTensor s TKUntyped
                   -> AstTensor s2 (TKS r sh)
                   -> AstTensor s2 (TKS r sh)
  AstLetHFunInS :: (GoodScalar r, KnownShS sh, TensorKind x, TensorKind y)
                => AstVarId -> AstHFun x y
                -> AstTensor s2 (TKS r sh)
                -> AstTensor s2 (TKS r sh)
  AstSFromR :: (KnownShS sh, KnownNat (X.Rank sh), GoodScalar r)
            => AstTensor s (TKR r (X.Rank sh)) -> AstTensor s (TKS r sh)

  -- There are existential variables inside DynamicTensor here.
  AstMkHVector :: HVector (AstRanked s) -> AstTensor s TKUntyped
  AstHApply :: (TensorKind x, TensorKind y)
            => AstHFun x y -> AstTensor s x -> AstTensor s y
  -- The operations below is why we need AstTensor s TKUntyped and so HVectorOf.
  -- If we kept a vector of terms instead, we'd need to let-bind in each
  -- of the terms separately, duplicating the let-bound term.
  AstLetHVectorInHVector
    :: AstSpan s
    => [AstDynamicVarName] -> AstTensor s TKUntyped
    -> AstTensor s2 TKUntyped
    -> AstTensor s2 TKUntyped
  AstLetHFunInHVector :: (TensorKind x, TensorKind y)
                      => AstVarId -> AstHFun x y
                      -> AstTensor s2 TKUntyped
                      -> AstTensor s2 TKUntyped
  AstBuildHVector1 :: SNat k -> (IntVarName, AstTensor s TKUntyped)
                   -> AstTensor s TKUntyped
  AstMapAccumRDer
    :: SNat k
    -> VoidHVector
    -> VoidHVector
    -> VoidHVector
    -> AstHFun (TKProduct TKUntyped TKUntyped) TKUntyped
    -> AstHFun (TKProduct TKUntyped TKUntyped) TKUntyped
    -> AstHFun (TKProduct TKUntyped TKUntyped) TKUntyped
    -> AstTensor s TKUntyped
    -> AstTensor s TKUntyped
    -> AstTensor s TKUntyped
  AstMapAccumLDer
    :: SNat k
    -> VoidHVector
    -> VoidHVector
    -> VoidHVector
    -> AstHFun (TKProduct TKUntyped TKUntyped) TKUntyped
    -> AstHFun (TKProduct TKUntyped TKUntyped) TKUntyped
    -> AstHFun (TKProduct TKUntyped TKUntyped) TKUntyped
    -> AstTensor s TKUntyped
    -> AstTensor s TKUntyped
    -> AstTensor s TKUntyped

deriving instance Show (AstTensor s y)

type AstDynamic (s :: AstSpanType) = DynamicTensor (AstRanked s)

type role AstHFun nominal nominal
data AstHFun x y where
  AstLambda :: TensorKind x
            => ~( AstVarName PrimalSpan x, TensorKindFull x
                , AstTensor PrimalSpan y )
            -> AstHFun x y
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
  AstVarHFun :: TensorKindFull x -> TensorKindFull y -> AstVarId -> AstHFun x y

deriving instance Show (AstHFun x y)

data AstBool where
  AstBoolNot :: AstBool -> AstBool
  AstB2 :: OpCodeBool -> AstBool -> AstBool -> AstBool
  AstBoolConst :: Bool -> AstBool
  -- There are existential variables here, as well.
  AstRel :: (KnownNat n, GoodScalar r)
         => OpCodeRel -> AstTensor PrimalSpan (TKR r n)
         -> AstTensor PrimalSpan (TKR r n)
         -> AstBool
  AstRelS :: (KnownShS sh, GoodScalar r)
          => OpCodeRel -> AstTensor PrimalSpan (TKS r sh) -> AstTensor PrimalSpan (TKS r sh)
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
instance Eq (AstTensor s (TKR r n)) where
  (==) = error "AST requires that EqF be used instead"
  (/=) = error "AST requires that EqF be used instead"

instance Ord (AstTensor s (TKR r n)) where
  (<=) = error "AST requires that OrdF be used instead"

instance (Num (Nested.Ranked n r), AstSpan s, GoodScalar r, KnownNat n)
         => Num (AstTensor s (TKR r n)) where
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
  fromInteger :: Integer -> AstTensor s (TKR r n)
  fromInteger i = case sameNat (Proxy @n) (Proxy @0) of
    Just Refl -> fromPrimal . AstConst . fromInteger $ i
    Nothing -> error $ "fromInteger not defined for AstRanked of non-zero ranks: "
                       ++ show (i, valueOf @n :: Int)
    -- it's crucial that there is no AstConstant in fromInteger code
    -- so that we don't need 4 times the simplification rules

instance (Real (Nested.Ranked n r), AstSpan s, GoodScalar r, KnownNat n)
         => Real (AstTensor s (TKR r n)) where
  toRational = undefined
    -- very low priority, since these are all extremely not continuous

-- Warning: div and mod operations are very costly (simplifying them
-- requires constructing conditionals, etc). If this error is removed,
-- they are going to work, but slowly.
instance (GoodScalar r, Integral r, KnownNat n)
         => IntegralF (AstTensor s (TKR r n)) where
  quotF = AstI2 QuotOp
  remF = AstI2 RemOp

instance (GoodScalar r, Differentiable r, Fractional (Nested.Ranked n r), AstSpan s, KnownNat n)
         => Fractional (AstTensor s (TKR r n)) where
  u / v = AstR2 DivideOp u v
  recip = AstR1 RecipOp
  fromRational r = error $ "fromRational not defined for AstRanked: "
                           ++ show r

instance (GoodScalar r, Differentiable r, Floating (Nested.Ranked n r), AstSpan s, KnownNat n)
         => Floating (AstTensor s (TKR r n)) where
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

instance (GoodScalar r, Differentiable r, RealFrac (Nested.Ranked n r), AstSpan s, KnownNat n)
         => RealFrac (AstTensor s (TKR r n)) where
  properFraction = undefined
    -- The integral type doesn't have a Storable constraint,
    -- so we can't implement this (nor RealFracB from Boolean package).

instance (GoodScalar r, Differentiable r, Floating (Nested.Ranked n r), AstSpan s, KnownNat n)
         => RealFloatF (AstTensor s (TKR r n)) where
  atan2F = AstR2 Atan2Op


-- * Unlawful numeric instances of shaped AST; they are lawful modulo evaluation

instance Eq (AstTensor s (TKS r sh)) where
  (==) = error "AST requires that EqF be used instead"
  (/=) = error "AST requires that EqF be used instead"

instance Ord (AstTensor s (TKS r sh)) where
  (<=) = error "AST requires that OrdF be used instead"

instance (GoodScalar r, Num (Nested.Shaped sh r), KnownShS sh)
         => Num (AstTensor s (TKS r sh)) where
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
         => IntegralF (AstTensor s (TKS r sh)) where
  quotF = AstI2S QuotOp
  remF = AstI2S RemOp

instance ( GoodScalar r, Differentiable r, Fractional (Nested.Shaped sh r)
         , KnownShS sh )
         => Fractional (AstTensor s (TKS r sh)) where
  u / v = AstR2S DivideOp u v
  recip = AstR1S RecipOp
  fromRational r = error $ "fromRational not defined for AstShaped: "
                           ++ show r

instance (GoodScalar r, Differentiable r, KnownShS sh, Floating (Nested.Shaped sh r), AstSpan s)
         => Floating (AstTensor s (TKS r sh)) where
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
         => RealFloatF (AstTensor s (TKS r sh)) where
  atan2F = AstR2S Atan2Op

-- * Unlawful instances of AST for bool; they are lawful modulo evaluation

instance Boolean AstBool where
  true = AstBoolConst True
  false = AstBoolConst False
  notB = AstBoolNot
  AstBoolConst b &&* AstBoolConst c = AstBoolConst $ b && c
                                        -- common in indexing
  b &&* c = AstB2 AndOp b c
  b ||* c = AstB2 OrOp b c


-- * The AstRaw, AstNoVectorize and AstNoSimplify definitions

type instance RankedOf (AstRaw s) = AstRaw s
type instance ShapedOf (AstRaw s) = AstRawS s
type instance PrimalOf (AstRaw s) = AstRaw PrimalSpan
type instance DualOf (AstRaw s) = AstRaw DualSpan
type instance HVectorOf (AstRaw s) = AstRawWrap (AstTensor s TKUntyped)
type instance HFunOf (AstRaw s) x y = AstHFun x y
type instance RankedOf (AstRawS s) = AstRaw s
type instance PrimalOf (AstRawS s) = AstRawS PrimalSpan
type instance DualOf (AstRawS s) = AstRawS DualSpan

type instance RankedOf (AstNoVectorize s) = AstNoVectorize s
type instance ShapedOf (AstNoVectorize s) = AstNoVectorizeS s
type instance PrimalOf (AstNoVectorize s) = AstNoVectorize PrimalSpan
type instance DualOf (AstNoVectorize s) = AstNoVectorize DualSpan
type instance HVectorOf (AstNoVectorize s) =
  AstNoVectorizeWrap (AstTensor s TKUntyped)
type instance HFunOf (AstNoVectorize s) x y = AstHFun x y
type instance RankedOf (AstNoVectorizeS s) = AstNoVectorize s
type instance PrimalOf (AstNoVectorizeS s) = AstNoVectorizeS PrimalSpan
type instance DualOf (AstNoVectorizeS s) = AstNoVectorizeS DualSpan

type instance RankedOf (AstNoSimplify s) = AstNoSimplify s
type instance ShapedOf (AstNoSimplify s) = AstNoSimplifyS s
type instance PrimalOf (AstNoSimplify s) = AstNoSimplify PrimalSpan
type instance DualOf (AstNoSimplify s) = AstNoSimplify DualSpan
type instance HVectorOf (AstNoSimplify s) =
  AstNoSimplifyWrap (AstTensor s TKUntyped)
type instance HFunOf (AstNoSimplify s) x y = AstHFun x y
type instance RankedOf (AstNoSimplifyS s) = AstNoSimplify s
type instance PrimalOf (AstNoSimplifyS s) = AstNoSimplifyS PrimalSpan
type instance DualOf (AstNoSimplifyS s) = AstNoSimplifyS DualSpan

type role AstRaw nominal nominal nominal
newtype AstRaw s r n =
  AstRaw {unAstRaw :: AstTensor s (TKR r n)}
deriving instance GoodScalar r => Show (AstRaw s r n)

type role AstRawS nominal nominal nominal
newtype AstRawS s r sh =
  AstRawS {unAstRawS :: AstTensor s (TKS r sh)}
deriving instance (GoodScalar r, KnownShS sh) => Show (AstRawS s r sh)

type role AstRawWrap nominal
newtype AstRawWrap t = AstRawWrap {unAstRawWrap :: t}
 deriving Show

type role AstNoVectorize nominal nominal nominal
newtype AstNoVectorize s r n =
  AstNoVectorize {unAstNoVectorize :: AstTensor s (TKR r n)}
deriving instance GoodScalar r => Show (AstNoVectorize s r n)

type role AstNoVectorizeS nominal nominal nominal
newtype AstNoVectorizeS s r sh =
  AstNoVectorizeS {unAstNoVectorizeS :: AstTensor s (TKS r sh)}
deriving instance (GoodScalar r, KnownShS sh) => Show (AstNoVectorizeS s r sh)

type role AstNoVectorizeWrap nominal
newtype AstNoVectorizeWrap t = AstNoVectorizeWrap {unAstNoVectorizeWrap :: t}
 deriving Show

type role AstNoSimplify nominal nominal nominal
newtype AstNoSimplify s r n =
  AstNoSimplify {unAstNoSimplify :: AstTensor s (TKR r n)}
deriving instance GoodScalar r => Show (AstNoSimplify s r n)

type role AstNoSimplifyS nominal nominal nominal
newtype AstNoSimplifyS s r sh =
  AstNoSimplifyS {unAstNoSimplifyS :: AstTensor s (TKS r sh)}
deriving instance (GoodScalar r, KnownShS sh) => Show (AstNoSimplifyS s r sh)

type role AstNoSimplifyWrap nominal
newtype AstNoSimplifyWrap t = AstNoSimplifyWrap {unAstNoSimplifyWrap :: t}
 deriving Show
