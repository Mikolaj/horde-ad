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
  , AstInt, IntVarName, pattern AstIntVar, isTensorInt
  , AstVarName, mkAstVarName, varNameToAstVarId, tensorKindFromAstVarName
  , AstArtifactRev(..), AstArtifactFwd(..)
  , AstIxR, AstVarList, AstIxS, AstVarListS, AstIndexX
    -- * AstBindingsCase and AstBindings
  , AstBindingsCase, AstBindings
    -- * ASTs
  , AstMethodOfSharing(..), AstTensor(..)
  , AstDynamic, AstHFun(..)
  , AstBool(..), OpCodeNum1(..), OpCodeNum2(..), OpCode1(..), OpCode2(..)
  , OpCodeIntegral2(..), OpCodeBool(..), OpCodeRel(..)
  ) where

import Prelude hiding (foldl')

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
import GHC.TypeLits (KnownNat, Nat, type (+), type (<=))
import Type.Reflection (Typeable, eqTypeRep, typeRep, (:~~:) (HRefl))

import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape (IShX, IxX, ListX)
import Data.Array.Nested
  ( IShR
  , IxR
  , IxS (..)
  , KnownShS (..)
  , KnownShX
  , ListR
  , ListS (..)
  , Rank
  , type (++)
  )
import Data.Array.Nested qualified as Nested

import HordeAd.Core.CarriersConcrete
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- Note that no Ast* module except AstInterpret and AstEnv
-- depends on any Tensor*, Carriers* and Ops* modules
-- and vice versa except CarriersAst and OpsAst.
-- Syntax is separated from semantics and they meet in the interpreter
-- and in the semantic model constructed from syntax (TensorAst).

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
  fromPrimal t = AstDualPart $ AstFromPrimal t  -- this is nil (not primal 0)

instance AstSpan FullSpan where
  fromPrimal = AstFromPrimal

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

type instance PrimalOf (AstTensor ms s) = AstTensor ms PrimalSpan

-- | This is the (arbitrarily) chosen representation of terms denoting
-- integers in the indexes of tensor operations.
type AstInt ms = IntOf (AstTensor ms FullSpan)
-- ~ AstTensor ms PrimalSpan (TKScalar Int64)

-- TODO: type IntVarNameF = AstVarName PrimalSpan Int64
type IntVarName = AstVarName PrimalSpan (TKScalar Int64)

pattern AstIntVar :: IntVarName -> AstInt ms
pattern AstIntVar var = AstVar FTKScalar var

isTensorInt :: forall s y ms. (AstSpan s, TensorKind y)
            => AstTensor ms s y
            -> Maybe (AstTensor ms s y :~: AstInt ms)
isTensorInt _ = case ( sameAstSpan @s @PrimalSpan
                     , sameTensorKind @y @(TKScalar Int64) ) of
                  (Just Refl, Just Refl) -> Just Refl
                  _ -> Nothing

type AstIxR ms n = IxR n (AstInt ms)

type AstVarList n = ListR n IntVarName

type AstIxS ms sh = IxS sh (AstInt ms)

type AstVarListS sh = ListS sh (Const IntVarName)

type AstIndexX ms sh = IxX sh (AstInt ms)

type AstIxX sh = ListX sh (Const IntVarName)


-- * AstBindingsCase and AstBindings

type AstBindingsCase y = AstTensor AstMethodLet PrimalSpan y

type AstBindings = DEnumMap (AstVarName PrimalSpan)
                            (AstTensor AstMethodLet PrimalSpan)


-- * ASTs

type data AstMethodOfSharing = AstMethodShare | AstMethodLet

-- | AST for ranked and shaped tensors that are meant to be differentiated.
type role AstTensor nominal nominal nominal
  -- r has to be nominal, because type class arguments always are
data AstTensor :: AstMethodOfSharing -> AstSpanType -> TensorKindType
               -> Type where
  -- Here starts the general part.
  AstPair :: (TensorKind1 y, TensorKind1 z)
          => AstTensor ms s y -> AstTensor ms s z
          -> AstTensor ms s (TKProduct y z)
  AstProject1 :: forall x z s ms. (TensorKind1 x, TensorKind1 z)
              => AstTensor ms s (TKProduct x z) -> AstTensor ms s x
  AstProject2 :: forall x z s ms. (TensorKind1 x, TensorKind1 z)
              => AstTensor ms s (TKProduct x z) -> AstTensor ms s z
  AstApply :: (TensorKind x, TensorKind z)
            => AstHFun x z -> AstTensor ms s x -> AstTensor ms s z
  AstVar :: TensorKind y
         => FullTensorKind y -> AstVarName s y -> AstTensor ms s y
  AstPrimalPart :: TensorKind y
                => AstTensor ms FullSpan y -> AstTensor ms PrimalSpan y
  AstDualPart :: TensorKind y
              => AstTensor ms FullSpan y -> AstTensor ms DualSpan y
  AstFromPrimal :: TensorKind y
                => AstTensor ms PrimalSpan y -> AstTensor ms FullSpan y
  AstD :: TensorKind y
       => AstTensor ms PrimalSpan y -> AstTensor ms DualSpan y
       -> AstTensor ms FullSpan y
  AstCond :: TensorKind y
          => AstBool ms -> AstTensor ms s y -> AstTensor ms s y
          -> AstTensor ms s y
  AstReplicate :: TensorKind y
               => SNat k -> AstTensor ms s y
               -> AstTensor ms s (BuildTensorKind k y)
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
  AstConcrete :: TensorKind y
              => FullTensorKind y -> RepN y -> AstTensor ms PrimalSpan y

  -- Here starts the scalar part.
  AstN1 :: GoodScalar r
        => OpCodeNum1 -> AstTensor ms s (TKScalar r)
        -> AstTensor ms s (TKScalar r)
  AstN2 :: GoodScalar r
        => OpCodeNum2 -> AstTensor ms s (TKScalar r)
        -> AstTensor ms s (TKScalar r)
        -> AstTensor ms s (TKScalar r)
  AstR1 :: (RealFloatF r, GoodScalar r)
        => OpCode1 -> AstTensor ms s (TKScalar r) -> AstTensor ms s (TKScalar r)
  AstR2 :: (RealFloatF r, GoodScalar r)
        => OpCode2 -> AstTensor ms s (TKScalar r) -> AstTensor ms s (TKScalar r)
        -> AstTensor ms s (TKScalar r)
  AstI2 :: (IntegralF r, GoodScalar r)
        => OpCodeIntegral2 -> AstTensor ms s (TKScalar r)
        -> AstTensor ms s (TKScalar r)
        -> AstTensor ms s (TKScalar r)
  AstSumOfList :: GoodScalar r
               => [AstTensor ms s (TKScalar r)] -> AstTensor ms s (TKScalar r)
  AstFloor :: (GoodScalar r, RealFrac r, GoodScalar r2, Integral r2)
           => AstTensor ms PrimalSpan (TKScalar r)
           -> AstTensor ms PrimalSpan (TKScalar r2)
  AstCast :: (GoodScalar r1, RealFrac r1, RealFrac r2, GoodScalar r2)
          => AstTensor ms s (TKScalar r1) -> AstTensor ms s (TKScalar r2)
  AstFromIntegral :: (GoodScalar r1, Integral r1, GoodScalar r2)
                  => AstTensor ms PrimalSpan (TKScalar r1)
                  -> AstTensor ms PrimalSpan (TKScalar r2)

  -- Here starts the ranked part.
  AstN1R :: (GoodScalar r, KnownNat n)
         => OpCodeNum1 -> AstTensor ms s (TKR n r) -> AstTensor ms s (TKR n r)
  AstN2R :: (GoodScalar r, KnownNat n)
         => OpCodeNum2 -> AstTensor ms s (TKR n r) -> AstTensor ms s (TKR n r)
         -> AstTensor ms s (TKR n r)
  AstR1R :: (Differentiable r, GoodScalar r, KnownNat n)
         => OpCode1 -> AstTensor ms s (TKR n r) -> AstTensor ms s (TKR n r)
  AstR2R :: (Differentiable r, GoodScalar r, KnownNat n)
         => OpCode2 -> AstTensor ms s (TKR n r) -> AstTensor ms s (TKR n r)
         -> AstTensor ms s (TKR n r)
  AstI2R :: (Integral r, GoodScalar r, KnownNat n)
         => OpCodeIntegral2 -> AstTensor ms s (TKR n r)
         -> AstTensor ms s (TKR n r)
         -> AstTensor ms s (TKR n r)
  AstSumOfListR :: (GoodScalar r, KnownNat n)
                => [AstTensor ms s (TKR n r)] -> AstTensor ms s (TKR n r)
  AstMinIndexR :: (GoodScalar r, KnownNat n, GoodScalar r2)
              => AstTensor ms PrimalSpan (TKR (1 + n) r)
              -> AstTensor ms PrimalSpan (TKR n r2)
  AstMaxIndexR :: (GoodScalar r, KnownNat n, GoodScalar r2)
              => AstTensor ms PrimalSpan (TKR (1 + n) r)
              -> AstTensor ms PrimalSpan (TKR n r2)
  AstFloorR :: ( GoodScalar r, RealFrac r, GoodScalar r2, Integral r2
               , KnownNat n )
           => AstTensor ms PrimalSpan (TKR n r)
           -> AstTensor ms PrimalSpan (TKR n r2)
  AstCastR :: ( GoodScalar r1, RealFrac r1, RealFrac r2, GoodScalar r2
             , KnownNat n )
          => AstTensor ms s (TKR n r1) -> AstTensor ms s (TKR n r2)
  AstFromIntegralR :: (GoodScalar r1, Integral r1, GoodScalar r2, KnownNat n)
                  => AstTensor ms PrimalSpan (TKR n r1)
                  -> AstTensor ms PrimalSpan (TKR n r2)
  AstIotaR :: GoodScalar r => AstTensor ms PrimalSpan (TKR 1 r)

  AstIndex :: forall m n r s ms. (KnownNat m, KnownNat n, TensorKind2 r)
           => AstTensor ms s (TKR2 (m + n) r) -> AstIxR ms m
           -> AstTensor ms s (TKR2 n r)
    -- first ix is for outermost dimension; empty index means identity,
    -- if index is out of bounds, the result is defined and is 0,
    -- but vectorization is permitted to change the value
  AstSum :: (KnownNat n, GoodScalar r)
         => AstTensor ms s (TKR (1 + n) r) -> AstTensor ms s (TKR n r)
  AstScatter :: forall m n p r s ms.
                (KnownNat m, KnownNat n, KnownNat p, GoodScalar r)
             => IShR (p + n)
             -> AstTensor ms s (TKR (m + n) r) -> (AstVarList m, AstIxR ms p)
             -> AstTensor ms s (TKR (p + n) r)
  AstFromVector :: (KnownNat n, TensorKind2 r)
                => Data.Vector.Vector (AstTensor ms s (TKR2 n r))
                -> AstTensor ms s (TKR2 (1 + n) r)
  AstAppend :: (KnownNat n, GoodScalar r)
            => AstTensor ms s (TKR (1 + n) r) -> AstTensor ms s (TKR (1 + n) r)
            -> AstTensor ms s (TKR (1 + n) r)
  AstSlice :: (KnownNat n, GoodScalar r)
           => Int -> Int -> AstTensor ms s (TKR (1 + n) r)
           -> AstTensor ms s (TKR (1 + n) r)
  AstReverse :: (KnownNat n, TensorKind2 r)
             => AstTensor ms s (TKR2 (1 + n) r) -> AstTensor ms s (TKR2 (1 + n) r)
  AstTranspose :: (KnownNat n, TensorKind2 r)
               => Permutation.PermR -> AstTensor ms s (TKR2 n r)
               -> AstTensor ms s (TKR2 n r)
  AstReshape :: (KnownNat n, KnownNat m, TensorKind2 r)
             => IShR m -> AstTensor ms s (TKR2 n r) -> AstTensor ms s (TKR2 m r)
  AstGather :: forall m n p r s ms.
               (KnownNat m, KnownNat n, KnownNat p, GoodScalar r)
            => IShR (m + n)
            -> AstTensor ms s (TKR (p + n) r) -> (AstVarList m, AstIxR ms p)
            -> AstTensor ms s (TKR (m + n) r)
    -- out of bounds indexing is permitted
  AstProjectR :: (GoodScalar r, KnownNat n)
              => AstTensor ms s TKUntyped -> Int -> AstTensor ms s (TKR n r)
  AstLetHVectorIn :: forall s s2 z. (AstSpan s, TensorKind z)
                  => [AstDynamicVarName] -> AstTensor AstMethodLet s TKUntyped
                  -> AstTensor AstMethodLet s2 z
                  -> AstTensor AstMethodLet s2 z
  AstRFromS :: (KnownShS sh, GoodScalar r)
            => AstTensor ms s (TKS sh r) -> AstTensor ms s (TKR (Rank sh) r)

  -- Here starts the shaped part.
  AstFromScalar :: GoodScalar r
                => AstTensor ms s (TKScalar r) -> AstTensor ms s (TKS '[] r)
  AstToScalar :: GoodScalar r
              => AstTensor ms s (TKS '[] r) -> AstTensor ms s (TKScalar r)
  AstN1S :: (GoodScalar r, KnownShS sh)
         => OpCodeNum1 -> AstTensor ms s (TKS sh r) -> AstTensor ms s (TKS sh r)
  AstN2S :: (GoodScalar r, KnownShS sh)
         => OpCodeNum2 -> AstTensor ms s (TKS sh r) -> AstTensor ms s (TKS sh r)
         -> AstTensor ms s (TKS sh r)
  AstR1S :: (Differentiable r, GoodScalar r, KnownShS sh)
         => OpCode1 -> AstTensor ms s (TKS sh r) -> AstTensor ms s (TKS sh r)
  AstR2S :: (Differentiable r, GoodScalar r, KnownShS sh)
         => OpCode2 -> AstTensor ms s (TKS sh r) -> AstTensor ms s (TKS sh r)
         -> AstTensor ms s (TKS sh r)
  AstI2S :: (Integral r, GoodScalar r, KnownShS sh)
         => OpCodeIntegral2 -> AstTensor ms s (TKS sh r)
         -> AstTensor ms s (TKS sh r)
         -> AstTensor ms s (TKS sh r)
  AstSumOfListS :: (KnownShS sh, GoodScalar r)
                => [AstTensor ms s (TKS sh r)] -> AstTensor ms s (TKS sh r)
  AstMinIndexS :: ( KnownShS sh, KnownNat n, GoodScalar r, GoodScalar r2
                  , GoodScalar r2, KnownShS (Init (n ': sh)) )
               => AstTensor ms PrimalSpan (TKS (n ': sh) r)
               -> AstTensor ms PrimalSpan (TKS (Init (n ': sh)) r2)
  AstMaxIndexS :: ( KnownShS sh, KnownNat n, GoodScalar r, GoodScalar r2
                  , GoodScalar r2, KnownShS (Init (n ': sh)) )
               => AstTensor ms PrimalSpan (TKS (n ': sh) r)
               -> AstTensor ms PrimalSpan (TKS (Init (n ': sh)) r2)
  AstFloorS :: ( GoodScalar r, RealFrac r, Integral r2, GoodScalar r2
               , KnownShS sh )
            => AstTensor ms PrimalSpan (TKS sh r)
            -> AstTensor ms PrimalSpan (TKS sh r2)
  AstCastS :: ( GoodScalar r1, RealFrac r1, GoodScalar r2, RealFrac r2
              , KnownShS sh )
           => AstTensor ms s (TKS sh r1) -> AstTensor ms s (TKS sh r2)
  AstFromIntegralS :: (GoodScalar r1, Integral r1, GoodScalar r2, KnownShS sh)
                   => AstTensor ms PrimalSpan (TKS sh r1)
                   -> AstTensor ms PrimalSpan (TKS sh r2)
  AstIotaS :: forall n r ms. (GoodScalar r, KnownNat n)
           => AstTensor ms PrimalSpan (TKS '[n] r)

  AstIndexS :: forall sh1 sh2 s x ms.
               ( KnownShS sh1, KnownShS sh2, KnownShS (sh1 ++ sh2)
               , TensorKind2 x )
            => AstTensor ms s (TKS2 (sh1 ++ sh2) x) -> AstIxS ms sh1
            -> AstTensor ms s (TKS2 sh2 x)
    -- first ix is for outermost dimension; empty index means identity,
    -- if index is out of bounds, the result is defined and is 0,
    -- but vectorization is permitted to change the value
  AstSumS :: forall n sh r s ms. (KnownNat n, KnownShS sh, GoodScalar r)
          => AstTensor ms s (TKS (n ': sh) r) -> AstTensor ms s (TKS sh r)
  AstScatterS :: forall sh2 p sh r s ms.
                 ( KnownShS sh2, KnownShS sh, KnownNat p
                 , KnownShS (Take p sh), KnownShS (Drop p sh)
                 , KnownShS (sh2 ++ Drop p sh), GoodScalar r )
              => AstTensor ms s (TKS (sh2 ++ Drop p sh) r)
              -> (AstVarListS sh2, AstIxS ms (Take p sh))
              -> AstTensor ms s (TKS sh r)

  AstFromVectorS :: (KnownNat n, KnownShS sh, TensorKind2 r)
                 => Data.Vector.Vector (AstTensor ms s (TKS2 sh r))
                 -> AstTensor ms s (TKS2 (n ': sh) r)
  AstAppendS :: (KnownNat n, KnownNat m, KnownShS sh, GoodScalar r)
             => AstTensor ms s (TKS (m ': sh) r)
             -> AstTensor ms s (TKS (n ': sh) r)
             -> AstTensor ms s (TKS ((m + n) ': sh) r)
  AstSliceS :: (KnownNat i, KnownNat n, KnownNat k, KnownShS sh, GoodScalar r)
            => AstTensor ms s (TKS (i + n + k ': sh) r)
            -> AstTensor ms s (TKS (n ': sh) r)
  AstReverseS :: (KnownNat n, KnownShS sh, TensorKind2 r)
              => AstTensor ms s (TKS2 (n ': sh) r)
              -> AstTensor ms s (TKS2 (n ': sh) r)
  AstTransposeS :: forall perm sh r s ms.
                   (PermC perm, KnownShS sh, Rank perm <= Rank sh, TensorKind2 r)
                => Permutation.Perm perm -> AstTensor ms s (TKS2 sh r)
                -> AstTensor ms s (TKS2 (Permutation.PermutePrefix perm sh) r)
  AstReshapeS :: ( KnownShS sh, Nested.Product sh ~ Nested.Product sh2
                 , TensorKind2 r, KnownShS sh2 )
              => AstTensor ms s (TKS2 sh r) -> AstTensor ms s (TKS2 sh2 r)
    -- beware that the order of type arguments is different than in orthotope
    -- and than the order of value arguments in the ranked version
  AstGatherS :: forall sh2 p sh r s ms.
                ( GoodScalar r, KnownShS sh, KnownShS sh2, KnownNat p
                , KnownShS (Take p sh), KnownShS (Drop p sh)
                , KnownShS (sh2 ++ Drop p sh) )
             => AstTensor ms s (TKS sh r)
             -> (AstVarListS sh2, AstIxS ms (Take p sh))
             -> AstTensor ms s (TKS (sh2 ++ Drop p sh) r)
    -- out of bounds indexing is permitted
  AstProjectS :: (GoodScalar r, KnownShS sh)
              => AstTensor ms s TKUntyped -> Int -> AstTensor ms s (TKS sh r)
  AstNestS :: forall r sh1 sh2 ms s.
              (TensorKind2 r, KnownShS sh1, KnownShS sh2, KnownShS (sh1 ++ sh2))
           => AstTensor ms s (TKS2 (sh1 ++ sh2) r)
           -> AstTensor ms s (TKS2 sh1 (TKS2 sh2 r))
  AstUnNestS :: forall r sh1 sh2 ms s.
                ( TensorKind2 r, KnownShS sh1, KnownShS sh2
                , KnownShS (sh1 ++ sh2) )
             => AstTensor ms s (TKS2 sh1 (TKS2 sh2 r))
             -> AstTensor ms s (TKS2 (sh1 ++ sh2) r)
  AstSFromR :: (KnownShS sh, KnownNat (Rank sh), GoodScalar r)
            => AstTensor ms s (TKR (Rank sh) r) -> AstTensor ms s (TKS sh r)
  AstSFromX :: ( KnownShS sh, KnownShX sh', Rank sh ~ Rank sh'
               , KnownShX (Nested.MapJust sh), GoodScalar r )
            => AstTensor ms s (TKX sh' r) -> AstTensor ms s (TKS sh r)
  AstXFromS :: ( KnownShS sh, KnownShX sh', sh' ~ Nested.MapJust sh
               , GoodScalar r )
            => AstTensor ms s (TKS sh r) -> AstTensor ms s (TKX sh' r)

  -- Here starts the mixed part.
  AstN1X :: (GoodScalar r, KnownShX sh)
         => OpCodeNum1 -> AstTensor ms s (TKX sh r) -> AstTensor ms s (TKX sh r)
  AstN2X :: (GoodScalar r, KnownShX sh)
         => OpCodeNum2 -> AstTensor ms s (TKX sh r) -> AstTensor ms s (TKX sh r)
         -> AstTensor ms s (TKX sh r)
  AstR1X :: (Differentiable r, GoodScalar r, KnownShX sh)
         => OpCode1 -> AstTensor ms s (TKX sh r) -> AstTensor ms s (TKX sh r)
  AstR2X :: (Differentiable r, GoodScalar r, KnownShX sh)
         => OpCode2 -> AstTensor ms s (TKX sh r) -> AstTensor ms s (TKX sh r)
         -> AstTensor ms s (TKX sh r)
  AstI2X :: (Integral r, GoodScalar r, KnownShX sh)
         => OpCodeIntegral2 -> AstTensor ms s (TKX sh r)
         -> AstTensor ms s (TKX sh r)
         -> AstTensor ms s (TKX sh r)
  AstSumOfListX :: (KnownShX sh, GoodScalar r)
                => [AstTensor ms s (TKX sh r)] -> AstTensor ms s (TKX sh r)
  AstMinIndexX :: ( KnownShX sh, KnownNat n, GoodScalar r, GoodScalar r2
                  , GoodScalar r2, KnownShX (Init (Just n ': sh)) )
               => AstTensor ms PrimalSpan (TKX (Just n ': sh) r)
               -> AstTensor ms PrimalSpan (TKX (Init (Just n ': sh)) r2)
  AstMaxIndexX :: ( KnownShX sh, KnownNat n, GoodScalar r, GoodScalar r2
                  , GoodScalar r2, KnownShX (Init (Just n ': sh)) )
               => AstTensor ms PrimalSpan (TKX (Just n ': sh) r)
               -> AstTensor ms PrimalSpan (TKX (Init (Just n ': sh)) r2)
  AstFloorX :: ( GoodScalar r, RealFrac r, Integral r2, GoodScalar r2
               , KnownShX sh )
            => AstTensor ms PrimalSpan (TKX sh r)
            -> AstTensor ms PrimalSpan (TKX sh r2)
  AstCastX :: ( GoodScalar r1, RealFrac r1, GoodScalar r2, RealFrac r2
              , KnownShX sh )
           => AstTensor ms s (TKX sh r1) -> AstTensor ms s (TKX sh r2)
  AstFromIntegralX :: (GoodScalar r1, Integral r1, GoodScalar r2, KnownShX sh)
                   => AstTensor ms PrimalSpan (TKX sh r1)
                   -> AstTensor ms PrimalSpan (TKX sh r2)
  AstIotaX :: forall n r ms. (GoodScalar r, KnownNat n)
           => AstTensor ms PrimalSpan (TKX '[Just n] r)

  AstIndexX :: forall sh1 sh2 s r ms.
               (KnownShX sh1, KnownShX sh2, KnownShX (sh1 ++ sh2), GoodScalar r)
            => AstTensor ms s (TKX (sh1 ++ sh2) r) -> AstIndexX ms sh1
            -> AstTensor ms s (TKX sh2 r)
    -- first ix is for outermost dimension; empty index means identity,
    -- if index is out of bounds, the result is defined and is 0,
    -- but vectorization is permitted to change the value
  AstSumX :: forall n sh r s ms. (KnownNat n, KnownShX sh, GoodScalar r)
          => AstTensor ms s (TKX (Just n ': sh) r) -> AstTensor ms s (TKX sh r)
  AstScatterX :: forall sh2 p sh r s ms.
                 ( KnownShX sh2, KnownShX sh, KnownNat p
                 , KnownShX (Take p sh), KnownShX (Drop p sh)
                 , KnownShX (sh2 ++ Drop p sh), GoodScalar r )
              => AstTensor ms s (TKX (sh2 ++ Drop p sh) r)
              -> (AstIxX sh2, AstIndexX ms (Take p sh))
              -> AstTensor ms s (TKX sh r)

  AstFromVectorX :: (KnownNat n, KnownShX sh, GoodScalar r)
                 => Data.Vector.Vector (AstTensor ms s (TKX sh r))
                 -> AstTensor ms s (TKX (Just n ': sh) r)
  AstAppendX :: (KnownNat n, KnownNat m, KnownShX sh, GoodScalar r)
             => AstTensor ms s (TKX (Just m ': sh) r)
             -> AstTensor ms s (TKX (Just n ': sh) r)
             -> AstTensor ms s (TKX (Just (m + n) ': sh) r)
  AstSliceX :: (KnownNat i, KnownNat n, KnownNat k, KnownShX sh, GoodScalar r)
            => AstTensor ms s (TKX (Just (i + n + k) ': sh) r)
            -> AstTensor ms s (TKX (Just n ': sh) r)
  AstReverseX :: (KnownNat n, KnownShX sh, GoodScalar r)
              => AstTensor ms s (TKX (Just n ': sh) r)
              -> AstTensor ms s (TKX (Just n ': sh) r)
  AstTransposeX :: forall perm sh r s ms.
                   (PermC perm, KnownShX sh, Rank perm <= Rank sh, GoodScalar r)
                => Permutation.Perm perm -> AstTensor ms s (TKX sh r)
                -> AstTensor ms s (TKX (Permutation.PermutePrefix perm sh) r)
  AstReshapeX :: (KnownShX sh, GoodScalar r, KnownShX sh2)
              => IShX sh2 -> AstTensor ms s (TKX sh r)
              -> AstTensor ms s (TKX sh2 r)
    -- beware that the order of type arguments is different than in orthotope
    -- and than the order of value arguments in the ranked version
  AstGatherX :: forall sh2 p sh r s ms.
                ( GoodScalar r, KnownShX sh, KnownShX sh2, KnownNat p
                , KnownShX (Take p sh), KnownShX (Drop p sh)
                , KnownShX (sh2 ++ Drop p sh) )
             => AstTensor ms s (TKX sh r)
             -> (AstIxX sh2, AstIndexX ms (Take p sh))
             -> AstTensor ms s (TKX (sh2 ++ Drop p sh) r)
    -- out of bounds indexing is permitted
  AstProjectX :: (GoodScalar r, KnownShX sh)
              => AstTensor ms s TKUntyped -> Int -> AstTensor ms s (TKX sh r)
  AstXFromR :: (KnownShX sh, KnownNat (Rank sh), GoodScalar r)
            => AstTensor ms s (TKR (Rank sh) r) -> AstTensor ms s (TKX sh r)

  -- Here starts the misc part.
  AstMkHVector :: HVector (AstTensor ms s) -> AstTensor ms s TKUntyped
  AstMapAccumRDer
    :: (TensorKind1 accShs, TensorKind1 bShs, TensorKind1 eShs)
    => SNat k
    -> FullTensorKind accShs
    -> FullTensorKind bShs
    -> FullTensorKind eShs
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
    :: (TensorKind1 accShs, TensorKind1 bShs, TensorKind1 eShs)
    => SNat k
    -> FullTensorKind accShs
    -> FullTensorKind bShs
    -> FullTensorKind eShs
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
            => ~( AstVarName PrimalSpan x, FullTensorKind x
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
