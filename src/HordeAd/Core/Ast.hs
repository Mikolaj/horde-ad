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
import Numeric.LinearAlgebra (Numeric)
import Type.Reflection (Typeable, eqTypeRep, typeRep, (:~~:) (HRefl))

import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape (IShX, IxX, ListX)
import Data.Array.Mixed.Types (Init)
import Data.Array.Nested
  ( IShR
  , IxR
  , IxS (..)
  , KnownShS (..)
  , KnownShX
  , ListR
  , ListS (..)
  , MapJust
  , Rank
  , Replicate
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
  AstPair :: (TensorKind y, TensorKind z)
          => AstTensor ms s y -> AstTensor ms s z
          -> AstTensor ms s (TKProduct y z)
  AstProject1 :: forall x z s ms. (TensorKind x, TensorKind z)
              => AstTensor ms s (TKProduct x z) -> AstTensor ms s x
  AstProject2 :: forall x z s ms. (TensorKind x, TensorKind z)
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
  AstSum :: SNat k -> STensorKindType y
         -> AstTensor ms s (BuildTensorKind k y)
         -> AstTensor ms s y
  AstReplicate :: SNat k -> STensorKindType y
               -> AstTensor ms s y
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

  AstIndex :: forall m n r s ms. (KnownNat m, KnownNat n, TensorKind r)
           => AstTensor ms s (TKR2 (m + n) r) -> AstIxR ms m
           -> AstTensor ms s (TKR2 n r)
    -- first ix is for outermost dimension; empty index means identity,
    -- if index is out of bounds, the result is defined and is 0,
    -- but vectorization is permitted to change the value
  AstScatter :: forall m n p r s ms.
                (KnownNat m, KnownNat n, KnownNat p, TensorKind r)
             => IShR (p + n)
             -> AstTensor ms s (TKR2 (m + n) r)
             -> (AstVarList m, AstIxR ms p)
             -> AstTensor ms s (TKR2 (p + n) r)
  AstFromVector :: (KnownNat n, TensorKind r)
                => Data.Vector.Vector (AstTensor ms s (TKR2 n r))
                -> AstTensor ms s (TKR2 (1 + n) r)
  AstAppend :: (KnownNat n, TensorKind r)
            => AstTensor ms s (TKR2 (1 + n) r) -> AstTensor ms s (TKR2 (1 + n) r)
            -> AstTensor ms s (TKR2 (1 + n) r)
  AstSlice :: (KnownNat n, TensorKind r)
           => Int -> Int -> AstTensor ms s (TKR2 (1 + n) r)
           -> AstTensor ms s (TKR2 (1 + n) r)
  AstReverse :: (KnownNat n, TensorKind r)
             => AstTensor ms s (TKR2 (1 + n) r) -> AstTensor ms s (TKR2 (1 + n) r)
  AstTranspose :: (KnownNat n, TensorKind r)
               => Permutation.PermR -> AstTensor ms s (TKR2 n r)
               -> AstTensor ms s (TKR2 n r)
  AstReshape :: (KnownNat n, KnownNat m, TensorKind r)
             => IShR m -> AstTensor ms s (TKR2 n r) -> AstTensor ms s (TKR2 m r)
  AstGather :: forall m n p r s ms.
               (KnownNat m, KnownNat n, KnownNat p, TensorKind r)
            => IShR (m + n)
            -> AstTensor ms s (TKR2 (p + n) r)
            -> (AstVarList m, AstIxR ms p)
            -> AstTensor ms s (TKR2 (m + n) r)
    -- out of bounds indexing is permitted
  AstProjectR :: (GoodScalar r, KnownNat n)
              => AstTensor ms s TKUntyped -> Int -> AstTensor ms s (TKR n r)
  AstLetHVectorIn :: forall s s2 z. (AstSpan s, TensorKind z)
                  => [AstDynamicVarName] -> AstTensor AstMethodLet s TKUntyped
                  -> AstTensor AstMethodLet s2 z
                  -> AstTensor AstMethodLet s2 z
  AstZipR :: (TensorKind y, TensorKind z, KnownNat n)
          => AstTensor ms s (TKProduct (TKR2 n y) (TKR2 n z))
          -> AstTensor ms s (TKR2 n (TKProduct y z))
  AstUnzipR :: (TensorKind y, TensorKind z, KnownNat n)
            => AstTensor ms s (TKR2 n (TKProduct y z))
            -> AstTensor ms s (TKProduct (TKR2 n y) (TKR2 n z))

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

  AstIndexS :: forall shm shn s x ms.
               (KnownShS shm, KnownShS shn, TensorKind x)
            => AstTensor ms s (TKS2 (shm ++ shn) x) -> AstIxS ms shm
            -> AstTensor ms s (TKS2 shn x)
    -- first ix is for outermost dimension; empty index means identity,
    -- if index is out of bounds, the result is defined and is 0,
    -- but vectorization is permitted to change the value
  AstScatterS :: forall shm shn shp r s ms.
                 (KnownShS shm, KnownShS shn, KnownShS shp, TensorKind r)
              => AstTensor ms s (TKS2 (shm ++ shn) r)
              -> (AstVarListS shm, AstIxS ms shp)
              -> AstTensor ms s (TKS2 (shp ++ shn) r)
  AstFromVectorS :: (KnownNat n, KnownShS sh, TensorKind r)
                 => Data.Vector.Vector (AstTensor ms s (TKS2 sh r))
                 -> AstTensor ms s (TKS2 (n ': sh) r)
  AstAppendS :: (KnownNat m, KnownNat n, KnownShS sh, TensorKind r)
             => AstTensor ms s (TKS2 (m ': sh) r)
             -> AstTensor ms s (TKS2 (n ': sh) r)
             -> AstTensor ms s (TKS2 ((m + n) ': sh) r)
  AstSliceS :: (KnownNat i, KnownNat n, KnownNat k, KnownShS sh, TensorKind r)
            => AstTensor ms s (TKS2 (i + n + k ': sh) r)
            -> AstTensor ms s (TKS2 (n ': sh) r)
  AstReverseS :: (KnownNat n, KnownShS sh, TensorKind r)
              => AstTensor ms s (TKS2 (n ': sh) r)
              -> AstTensor ms s (TKS2 (n ': sh) r)
  AstTransposeS :: forall perm sh r s ms.
                   (PermC perm, KnownShS sh, Rank perm <= Rank sh, TensorKind r)
                => Permutation.Perm perm -> AstTensor ms s (TKS2 sh r)
                -> AstTensor ms s (TKS2 (Permutation.PermutePrefix perm sh) r)
  AstReshapeS :: ( KnownShS sh, Nested.Product sh ~ Nested.Product sh2
                 , TensorKind r, KnownShS sh2 )
              => AstTensor ms s (TKS2 sh r) -> AstTensor ms s (TKS2 sh2 r)
    -- beware that the order of type arguments is different than in orthotope
    -- and than the order of value arguments in the ranked version
  AstGatherS :: forall shm shn shp r s ms.
                (KnownShS shm, KnownShS shn, KnownShS shp, TensorKind r)
             => AstTensor ms s (TKS2 (shp ++ shn) r)
             -> (AstVarListS shm, AstIxS ms shp)
             -> AstTensor ms s (TKS2 (shm ++ shn) r)
    -- out of bounds indexing is permitted
  AstProjectS :: (GoodScalar r, KnownShS sh)
              => AstTensor ms s TKUntyped -> Int -> AstTensor ms s (TKS sh r)
  AstZipS :: (TensorKind y, TensorKind z, KnownShS sh)
          => AstTensor ms s (TKProduct (TKS2 sh y) (TKS2 sh z))
          -> AstTensor ms s (TKS2 sh (TKProduct y z))
  AstUnzipS :: (TensorKind y, TensorKind z, KnownShS sh)
            => AstTensor ms s (TKS2 sh (TKProduct y z))
            -> AstTensor ms s (TKProduct (TKS2 sh y) (TKS2 sh z))

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
               (KnownShX sh1, KnownShX sh2, TensorKind r)
            => AstTensor ms s (TKX2 (sh1 ++ sh2) r) -> AstIndexX ms sh1
            -> AstTensor ms s (TKX2 sh2 r)
    -- first ix is for outermost dimension; empty index means identity,
    -- if index is out of bounds, the result is defined and is 0,
    -- but vectorization is permitted to change the value
  AstScatterX :: forall sh2 p sh r s ms.
                 ( KnownShX sh2, KnownShX sh, KnownNat p
                 , KnownShX (Take p sh), KnownShX (Drop p sh)
                 , KnownShX (sh2 ++ Drop p sh), GoodScalar r )
              => AstTensor ms s (TKX (sh2 ++ Drop p sh) r)
              -> (AstIxX sh2, AstIndexX ms (Take p sh))
              -> AstTensor ms s (TKX sh r)

  AstFromVectorX :: (KnownNat n, KnownShX sh, TensorKind r)
                 => Data.Vector.Vector (AstTensor ms s (TKX2 sh r))
                 -> AstTensor ms s (TKX2 (Just n ': sh) r)
  AstAppendX :: (KnownNat n, KnownNat m, KnownShX sh, TensorKind r)
             => AstTensor ms s (TKX2 (Just m ': sh) r)
             -> AstTensor ms s (TKX2 (Just n ': sh) r)
             -> AstTensor ms s (TKX2 (Just (m + n) ': sh) r)
  AstSliceX :: (KnownNat i, KnownNat n, KnownNat k, KnownShX sh, TensorKind r)
            => AstTensor ms s (TKX2 (Just (i + n + k) ': sh) r)
            -> AstTensor ms s (TKX2 (Just n ': sh) r)
  AstReverseX :: (KnownNat n, KnownShX sh, TensorKind r)
              => AstTensor ms s (TKX2 (Just n ': sh) r)
              -> AstTensor ms s (TKX2 (Just n ': sh) r)
  AstTransposeX :: forall perm sh r s ms.
                   (PermC perm, KnownShX sh, Rank perm <= Rank sh, TensorKind r)
                => Permutation.Perm perm -> AstTensor ms s (TKX2 sh r)
                -> AstTensor ms s (TKX2 (Permutation.PermutePrefix perm sh) r)
  AstReshapeX :: (KnownShX sh, TensorKind r, KnownShX sh2)
              => IShX sh2 -> AstTensor ms s (TKX2 sh r)
              -> AstTensor ms s (TKX2 sh2 r)
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
  AstZipX :: (TensorKind y, TensorKind z, KnownShX sh)
          => AstTensor ms s (TKProduct (TKX2 sh y) (TKX2 sh z))
          -> AstTensor ms s (TKX2 sh (TKProduct y z))
  AstUnzipX :: (TensorKind y, TensorKind z, KnownShX sh)
            => AstTensor ms s (TKX2 sh (TKProduct y z))
            -> AstTensor ms s (TKProduct (TKX2 sh y) (TKX2 sh z))

  -- Ops that involve more than one variant of arrays
  AstRFromS :: (KnownShS sh, TensorKind r)
            => AstTensor ms s (TKS2 sh r) -> AstTensor ms s (TKR2 (Rank sh) r)
  AstRFromX :: (KnownShX sh, TensorKind r)
            => AstTensor ms s (TKX2 sh r) -> AstTensor ms s (TKR2 (Rank sh) r)
  AstSFromR :: (KnownShS sh, KnownNat (Rank sh), TensorKind r)
            => AstTensor ms s (TKR2 (Rank sh) r) -> AstTensor ms s (TKS2 sh r)
  AstSFromX :: (KnownShS sh, KnownShX sh', Rank sh ~ Rank sh', TensorKind r)
            => AstTensor ms s (TKX2 sh' r) -> AstTensor ms s (TKS2 sh r)
  AstXFromR :: (KnownShX sh, KnownNat (Rank sh), TensorKind r)
            => AstTensor ms s (TKR2 (Rank sh) r) -> AstTensor ms s (TKX2 sh r)
  AstXFromS :: (KnownShS sh, KnownShX sh', Rank sh ~ Rank sh', TensorKind r)
            => AstTensor ms s (TKS2 sh r) -> AstTensor ms s (TKX2 sh' r)

  AstXNestR :: forall sh1 m x ms s.
               (TensorKind x, KnownShX sh1, KnownNat m)
            => AstTensor ms s (TKX2 (sh1 ++ Replicate m Nothing) x)
            -> AstTensor ms s (TKX2 sh1 (TKR2 m x))
  AstXNestS :: forall sh1 sh2 x ms s.
               (TensorKind x, KnownShX sh1, KnownShS sh2)
            => AstTensor ms s (TKX2 (sh1 ++ MapJust sh2) x)
            -> AstTensor ms s (TKX2 sh1 (TKS2 sh2 x))
  AstXNest :: forall sh1 sh2 x ms s.
              (TensorKind x, KnownShX sh1, KnownShX sh2)
           => AstTensor ms s (TKX2 (sh1 ++ sh2) x)
           -> AstTensor ms s (TKX2 sh1 (TKX2 sh2 x))

  AstXUnNestR :: forall sh1 m x ms s.
                 (TensorKind x, KnownShX sh1, KnownNat m)
              => AstTensor ms s (TKX2 sh1 (TKR2 m x))
              -> AstTensor ms s (TKX2 (sh1 ++ Replicate m Nothing) x)
  AstXUnNestS :: forall sh1 sh2 x ms s.
                 (TensorKind x, KnownShX sh1, KnownShS sh2)
              => AstTensor ms s (TKX2 sh1 (TKS2 sh2 x))
              -> AstTensor ms s (TKX2 (sh1 ++ MapJust sh2) x)
  AstXUnNest :: forall sh1 sh2 x ms s.
                (TensorKind x, KnownShX sh1, KnownShX sh2)
             => AstTensor ms s (TKX2 sh1 (TKX2 sh2 x))
             -> AstTensor ms s (TKX2 (sh1 ++ sh2) x)

  -- Here starts the misc part.
  AstMkHVector :: HVector (AstTensor ms s) -> AstTensor ms s TKUntyped
  AstMapAccumRDer
    :: (TensorKind accShs, TensorKind bShs, TensorKind eShs)
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
    :: (TensorKind accShs, TensorKind bShs, TensorKind eShs)
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

  -- Here starts the backend-specific primitives part.
  AstReplicate0NR :: IShR n -> STensorKindType x
                  -> AstTensor ms s (TKR2 0 x)
                  -> AstTensor ms s (TKR2 n x)
  AstSum0R :: SNat n -> STensorKindType x
           -> AstTensor ms s (TKR2 n x)
           -> AstTensor ms s (TKR2 0 x)
  AstDot0R :: GoodScalar r
           => SNat n
           -> AstTensor ms s (TKR n r) -> AstTensor ms s (TKR n r)
           -> AstTensor ms s (TKR 0 r)
  AstDot1InR :: GoodScalar r
             => AstTensor ms s (TKR 2 r) -> AstTensor ms s (TKR 2 r)
             -> AstTensor ms s (TKR 1 r)
  AstMatvecmulR :: GoodScalar r
                => AstTensor ms s (TKR 2 r)
                -> AstTensor ms s (TKR 1 r)
                -> AstTensor ms s (TKR 1 r)
  AstMatmul2R :: (GoodScalar r, Numeric r)
              => AstTensor ms s (TKR 2 r)
              -> AstTensor ms s (TKR 2 r)
              -> AstTensor ms s (TKR 2 r)

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
