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
  , AstInt, IntVarName, pattern AstIntVar, isTensorInt
  , AstVarName, mkAstVarName, varNameToAstVarId, tensorKindFromAstVarName
  , AstArtifactRev(..), AstArtifactFwd(..)
  , AstIxR, AstVarList, AstIxS, AstVarListS, AstIndexX
    -- * AstBindingsCase and AstBindings
  , AstBindingsCase, AstBindings
    -- * ASTs
  , AstMethodOfSharing(..), AstTensor(..)
  , AstHFun(..)
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
import Data.Some
import Data.Strict.Vector qualified as Data.Vector
import Data.Type.Equality ((:~:) (Refl))
import GHC.TypeLits (KnownNat, type (+), type (<=))
import Numeric.LinearAlgebra (Numeric)
import Type.Reflection (Typeable, eqTypeRep, typeRep, (:~~:) (HRefl))

import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape (IxX)
import Data.Array.Mixed.Types (Init)
import Data.Array.Nested
  ( IxR
  , IxS (..)
  , KnownShS (..)
  , KnownShX
  , ListR
  , ListS (..)
  , MapJust
  , Rank
  , Replicate
  , ShS (..)
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


-- * AstBindingsCase and AstBindings

type AstBindingsCase y = AstTensor AstMethodLet PrimalSpan y

type AstBindings = DEnumMap (AstVarName PrimalSpan)
                            (AstTensor AstMethodLet PrimalSpan)


-- * ASTs

type data AstMethodOfSharing = AstMethodShare | AstMethodLet

-- | AST for tensors that are meant to be differentiated
type role AstTensor nominal nominal nominal
data AstTensor :: AstMethodOfSharing -> AstSpanType -> TensorKindType
               -> Type where
  -- General operations, for scalar, ranked, shared and other tensors at once
  AstPair :: (TensorKind y, TensorKind z)
          => AstTensor ms s y -> AstTensor ms s z
          -> AstTensor ms s (TKProduct y z)
  AstProject1 :: (TensorKind x, TensorKind z)
              => AstTensor ms s (TKProduct x z) -> AstTensor ms s x
  AstProject2 :: (TensorKind x, TensorKind z)
              => AstTensor ms s (TKProduct x z) -> AstTensor ms s z
  AstFromVector :: TensorKind y
                => SNat k -> Data.Vector.Vector (AstTensor ms s y)
                -> AstTensor ms s (BuildTensorKind k y)
  AstSum :: SNat k -> STensorKindType y
         -> AstTensor ms s (BuildTensorKind k y)
         -> AstTensor ms s y
  AstReplicate :: SNat k -> STensorKindType y
               -> AstTensor ms s y
               -> AstTensor ms s (BuildTensorKind k y)
  AstMapAccumRDer
    :: (TensorKind accShs, TensorKind bShs, TensorKind eShs)
    => SNat k
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
  AstApply :: (TensorKind x, TensorKind z)
            => AstHFun x z -> AstTensor ms s x -> AstTensor ms s z
  AstVar :: TensorKind y
         => FullTensorKind y -> AstVarName s y -> AstTensor ms s y
  AstCond :: TensorKind y
          => AstBool ms -> AstTensor ms s y -> AstTensor ms s y
          -> AstTensor ms s y
  AstBuild1 :: TensorKind y
            => SNat k -> (IntVarName, AstTensor ms s y)
            -> AstTensor ms s (BuildTensorKind k y)
  AstConcrete :: TensorKind y
              => FullTensorKind y -> RepN y -> AstTensor ms PrimalSpan y

  -- Sharing-related operations, mutually exclusive via AstMethodOfSharing
  AstLet :: (TensorKind y, TensorKind z, AstSpan s)
         => AstVarName s y -> AstTensor AstMethodLet s y
         -> AstTensor AstMethodLet s2 z
         -> AstTensor AstMethodLet s2 z
  AstShare :: TensorKind y
           => AstVarName s y -> AstTensor AstMethodShare s y
           -> AstTensor AstMethodShare s y
  AstToShare :: AstTensor AstMethodLet s y
             -> AstTensor AstMethodShare s y

  -- Explicit dual numbers handling, eliminated in interpretation to ADVal
  AstPrimalPart :: TensorKind y
                => AstTensor ms FullSpan y -> AstTensor ms PrimalSpan y
  AstDualPart :: TensorKind y
              => AstTensor ms FullSpan y -> AstTensor ms DualSpan y
  AstFromPrimal :: TensorKind y
                => AstTensor ms PrimalSpan y -> AstTensor ms FullSpan y
  AstD :: TensorKind y
       => AstTensor ms PrimalSpan y -> AstTensor ms DualSpan y
       -> AstTensor ms FullSpan y

  -- Extra constructors for optimization of arithmetic
  AstSumOfList :: STensorKindType y -> [AstTensor ms s y] -> AstTensor ms s y

  -- Scalar arithmetic
  AstN1 :: GoodScalar r
        => OpCodeNum1 -> AstTensor ms s (TKScalar r)
        -> AstTensor ms s (TKScalar r)
  AstN2 :: GoodScalar r
        => OpCodeNum2 -> AstTensor ms s (TKScalar r)
        -> AstTensor ms s (TKScalar r)
        -> AstTensor ms s (TKScalar r)
  AstR1 :: (RealFloatF r, Nested.FloatElt r, GoodScalar r)
        => OpCode1 -> AstTensor ms s (TKScalar r) -> AstTensor ms s (TKScalar r)
  AstR2 :: (RealFloatF r, Nested.FloatElt r, GoodScalar r)
        => OpCode2 -> AstTensor ms s (TKScalar r) -> AstTensor ms s (TKScalar r)
        -> AstTensor ms s (TKScalar r)
  AstI2 :: (IntegralF r, GoodScalar r)
        => OpCodeIntegral2 -> AstTensor ms s (TKScalar r)
        -> AstTensor ms s (TKScalar r)
        -> AstTensor ms s (TKScalar r)
  AstFloor :: (GoodScalar r, RealFrac r, GoodScalar r2, Integral r2)
           => AstTensor ms PrimalSpan (TKScalar r)
           -> AstTensor ms PrimalSpan (TKScalar r2)
  AstFromIntegral :: (GoodScalar r1, Integral r1, GoodScalar r2)
                  => AstTensor ms PrimalSpan (TKScalar r1)
                  -> AstTensor ms PrimalSpan (TKScalar r2)
  AstCast :: (GoodScalar r1, RealFrac r1, RealFrac r2, GoodScalar r2)
          => AstTensor ms s (TKScalar r1) -> AstTensor ms s (TKScalar r2)

  -- Shaped arithmetic
  AstN1S :: (GoodScalar r, KnownShS sh)
         => OpCodeNum1 -> AstTensor ms s (TKS sh r) -> AstTensor ms s (TKS sh r)
  AstN2S :: (GoodScalar r, KnownShS sh)
         => OpCodeNum2 -> AstTensor ms s (TKS sh r) -> AstTensor ms s (TKS sh r)
         -> AstTensor ms s (TKS sh r)
  AstR1S :: (RealFloatF r, Nested.FloatElt r, GoodScalar r, KnownShS sh)
         => OpCode1 -> AstTensor ms s (TKS sh r) -> AstTensor ms s (TKS sh r)
  AstR2S :: (RealFloatF r, Nested.FloatElt r, GoodScalar r, KnownShS sh)
         => OpCode2 -> AstTensor ms s (TKS sh r) -> AstTensor ms s (TKS sh r)
         -> AstTensor ms s (TKS sh r)
  AstI2S :: (IntegralF r, GoodScalar r, KnownShS sh)
         => OpCodeIntegral2 -> AstTensor ms s (TKS sh r)
         -> AstTensor ms s (TKS sh r)
         -> AstTensor ms s (TKS sh r)
  AstFloorS :: ( GoodScalar r, RealFrac r, Integral r2, GoodScalar r2
               , KnownShS sh )
            => AstTensor ms PrimalSpan (TKS sh r)
            -> AstTensor ms PrimalSpan (TKS sh r2)
  AstFromIntegralS :: (GoodScalar r1, Integral r1, GoodScalar r2, KnownShS sh)
                   => AstTensor ms PrimalSpan (TKS sh r1)
                   -> AstTensor ms PrimalSpan (TKS sh r2)
  AstCastS :: ( GoodScalar r1, RealFrac r1, GoodScalar r2, RealFrac r2
              , KnownShS sh )
           => AstTensor ms s (TKS sh r1) -> AstTensor ms s (TKS sh r2)

  -- Shaped tensor operations
  AstMinIndexS :: ( KnownShS sh, KnownNat n, GoodScalar r, GoodScalar r2
                  , GoodScalar r2, KnownShS (Init (n ': sh)) )
               => AstTensor ms PrimalSpan (TKS (n ': sh) r)
               -> AstTensor ms PrimalSpan (TKS (Init (n ': sh)) r2)
  AstMaxIndexS :: ( KnownShS sh, KnownNat n, GoodScalar r, GoodScalar r2
                  , GoodScalar r2, KnownShS (Init (n ': sh)) )
               => AstTensor ms PrimalSpan (TKS (n ': sh) r)
               -> AstTensor ms PrimalSpan (TKS (Init (n ': sh)) r2)
  AstIotaS :: (KnownNat n, GoodScalar r)
           => AstTensor ms PrimalSpan (TKS '[n] r)
  AstIndexS :: forall shm shn x s ms.
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
  AstTransposeS :: (PermC perm, KnownShS sh, TensorKind r, Rank perm <= Rank sh)
                => Permutation.Perm perm -> AstTensor ms s (TKS2 sh r)
                -> AstTensor ms s (TKS2 (Permutation.PermutePrefix perm sh) r)
  AstReshapeS :: ( KnownShS sh, KnownShS sh2
                 , Nested.Product sh ~ Nested.Product sh2, TensorKind r)
              => AstTensor ms s (TKS2 sh r) -> AstTensor ms s (TKS2 sh2 r)
    -- beware that the order of type arguments is different than in orthotope
    -- and than the order of value arguments in the ranked version
  AstGatherS :: forall shm shn shp r s ms.
                (KnownShS shm, KnownShS shn, KnownShS shp, TensorKind r)
             => AstTensor ms s (TKS2 (shp ++ shn) r)
             -> (AstVarListS shm, AstIxS ms shp)
             -> AstTensor ms s (TKS2 (shm ++ shn) r)
    -- out of bounds indexing is permitted
  AstZipS :: (TensorKind y, TensorKind z, KnownShS sh)
          => AstTensor ms s (TKProduct (TKS2 sh y) (TKS2 sh z))
          -> AstTensor ms s (TKS2 sh (TKProduct y z))
  AstUnzipS :: (TensorKind y, TensorKind z, KnownShS sh)
            => AstTensor ms s (TKS2 sh (TKProduct y z))
            -> AstTensor ms s (TKProduct (TKS2 sh y) (TKS2 sh z))

  -- Conversions
  AstFromS :: forall y z ms s.
              STensorKindType z -> AstTensor ms s y -> AstTensor ms s z
  AstFromScalar :: GoodScalar r
                => AstTensor ms s (TKScalar r) -> AstTensor ms s (TKS '[] r)
  AstSFromR :: (KnownShS sh, KnownNat (Rank sh), TensorKind r)
            => AstTensor ms s (TKR2 (Rank sh) r) -> AstTensor ms s (TKS2 sh r)
  AstSFromX :: (KnownShS sh, KnownShX sh', Rank sh ~ Rank sh', TensorKind r)
            => AstTensor ms s (TKX2 sh' r) -> AstTensor ms s (TKS2 sh r)

  AstXNestR :: (KnownShX sh1, KnownNat m, TensorKind x)
            => AstTensor ms s (TKX2 (sh1 ++ Replicate m Nothing) x)
            -> AstTensor ms s (TKX2 sh1 (TKR2 m x))
  AstXNestS :: (KnownShX sh1, KnownShS sh2, TensorKind x)
            => AstTensor ms s (TKX2 (sh1 ++ MapJust sh2) x)
            -> AstTensor ms s (TKX2 sh1 (TKS2 sh2 x))
  AstXNest :: (KnownShX sh1, KnownShX sh2, TensorKind x)
           => AstTensor ms s (TKX2 (sh1 ++ sh2) x)
           -> AstTensor ms s (TKX2 sh1 (TKX2 sh2 x))
  AstXUnNestR :: (KnownShX sh1, KnownNat m, TensorKind x)
              => AstTensor ms s (TKX2 sh1 (TKR2 m x))
              -> AstTensor ms s (TKX2 (sh1 ++ Replicate m Nothing) x)
  AstXUnNestS :: (KnownShX sh1, KnownShS sh2, TensorKind x)
              => AstTensor ms s (TKX2 sh1 (TKS2 sh2 x))
              -> AstTensor ms s (TKX2 (sh1 ++ MapJust sh2) x)
  AstXUnNest :: (KnownShX sh1, KnownShX sh2, TensorKind x)
             => AstTensor ms s (TKX2 sh1 (TKX2 sh2 x))
             -> AstTensor ms s (TKX2 (sh1 ++ sh2) x)

  -- Backend-specific primitives
  AstReplicate0NS :: ShS sh -> STensorKindType x
                  -> AstTensor ms s (TKS2 '[] x)
                  -> AstTensor ms s (TKS2 sh x)
  AstSum0S :: ShS sh -> STensorKindType x
           -> AstTensor ms s (TKS2 sh x)
           -> AstTensor ms s (TKS2 '[] x)
  AstDot0S :: GoodScalar r
           => ShS sh
           -> AstTensor ms s (TKS sh r) -> AstTensor ms s (TKS sh r)
           -> AstTensor ms s (TKS '[] r)
  AstDot1InS :: GoodScalar r
             => SNat m -> SNat n
             -> AstTensor ms s (TKS '[m, n] r) -> AstTensor ms s (TKS '[m, n] r)
             -> AstTensor ms s (TKS '[m] r)
  AstMatvecmulS :: GoodScalar r
                => SNat m -> SNat n
                -> AstTensor ms s (TKS '[m, n] r)
                -> AstTensor ms s (TKS '[n] r)
                -> AstTensor ms s (TKS '[m] r)
  AstMatmul2S :: (GoodScalar r, Numeric r)
              => SNat m -> SNat n -> SNat p
              -> AstTensor ms s (TKS '[m, n] r)
              -> AstTensor ms s (TKS '[n, p] r)
              -> AstTensor ms s (TKS '[m, p] r)

deriving instance Show (AstTensor ms s y)

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
  -- There are existential variables here.
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
