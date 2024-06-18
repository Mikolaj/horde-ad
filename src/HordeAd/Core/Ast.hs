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
  , AstVarName(..), varNameToAstVarId
  , AstArtifact(..), AstIndex, AstVarList, AstIndexS, AstVarListS
    -- * AstBindingsCase and AstBindings
  , AstBindingsCase(..), AstBindings
    -- * ASTs
  , AstRanked(..), AstShaped(..), AstDynamic, AstHVector(..), AstHFun(..)
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
import Data.Functor.Const
import Data.Int (Int64)
import Data.Kind (Type)
import Data.Proxy (Proxy (Proxy))
import Data.Strict.Vector qualified as Data.Vector
import Data.Type.Equality (testEquality, (:~:) (Refl))
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

type instance HVectorOf (AstRanked s) = AstHVector s
-- This can't be just HFun, because they need to be vectorized
-- and vectorization applies such functions to the variable from build1
-- and the variable has to be eliminated via vectorization to preserve
-- the closed form of the function. Just applying a Haskell closure
-- to the build1 variable and then duplicating the result of the function
-- would not eliminate the variable and also would likely results
-- in more costly computations. Also, that would prevent simplification
-- of the instances, especially after applied to arguments that are terms.
type instance HFunOf (AstRanked s) = AstHFun

type instance RankedOf (AstShaped s) = AstRanked s
type instance ShapedOf (AstShaped s) = AstShaped s
type instance PrimalOf (AstShaped s) = AstShaped PrimalSpan
type instance DualOf (AstShaped s) = AstShaped DualSpan


-- * The AstSpan kind

-- | A kind (a type intended to be promoted) marking whether an AST term
-- is supposed to denote the primal part of a dual number, the dual part
-- or the whole dual number. It's mainly used to index the terms
-- of the AstRanked and related GADTs.
type data AstSpanType = PrimalSpan | DualSpan | FullSpan

class Typeable s => AstSpan (s :: AstSpanType) where
  fromPrimal :: AstRanked PrimalSpan r y -> AstRanked s r y
  fromPrimalS :: AstShaped PrimalSpan r y -> AstShaped s r y

instance AstSpan PrimalSpan where
  fromPrimal = id
  fromPrimalS = id

instance AstSpan DualSpan where
  fromPrimal t = AstDualPart $ AstConstant t  -- this is nil (not primal 0)
  fromPrimalS t = AstDualPartS $ AstConstantS t

instance AstSpan FullSpan where
  fromPrimal = AstConstant
  fromPrimalS = AstConstantS

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

type role AstVarName phantom phantom nominal
newtype AstVarName (f :: TensorType ty) (r :: Type) (y :: ty) =
  AstVarName AstVarId
 deriving (Eq, Ord, Enum)

instance Show (AstVarName f r y) where
  showsPrec d (AstVarName varId) =
    showsPrec d varId  -- less verbose, more readable

varNameToAstVarId :: AstVarName f r y -> AstVarId
varNameToAstVarId (AstVarName varId) = varId

-- The reverse derivative artifact from step 6) of our full pipeline.
-- The same type can also hold the forward derivative artifact.
data AstArtifact = AstArtifact
  { artVarsDt     :: [AstDynamicVarName]
  , artVarsPrimal :: [AstDynamicVarName]
  , artDerivative :: HVectorOf (AstRaw PrimalSpan)
  , artPrimal     :: HVectorOf (AstRaw PrimalSpan)
  }

-- | This is the (arbitrarily) chosen representation of terms denoting
-- integers in the indexes of tensor operations.
type AstInt = AstRanked PrimalSpan Int64 0

-- TODO: type IntVarNameF = AstVarName (AstRanked PrimalSpan) Int64
type IntVarName = AstVarName (AstRanked PrimalSpan) Int64 0

pattern AstIntVar :: IntVarName -> AstInt
pattern AstIntVar var = AstVar ZSR var

isRankedInt :: forall s r n. (AstSpan s, GoodScalar r, KnownNat n)
            => AstRanked s r n
            -> Maybe (AstRanked s r n :~: AstInt)
isRankedInt _ = case ( sameAstSpan @s @PrimalSpan
                     , testEquality (typeRep @r) (typeRep @Int64)
                     , sameNat (Proxy @n) (Proxy @0) ) of
                  (Just Refl, Just Refl, Just Refl) -> Just Refl
                  _ -> Nothing

type AstIndex n = Index n AstInt

type AstVarList n = SizedList n IntVarName

type AstIndexS sh = IndexS sh AstInt

type AstVarListS sh = SizedListS sh (Const IntVarName)


-- * AstBindingsCase and AstBindings

type role AstBindingsCase nominal
data AstBindingsCase (s :: AstSpanType) =
    AstBindingsSimple (DynamicTensor (AstRanked s))
  | AstBindingsHVector [AstDynamicVarName] (HVectorOf (AstRanked s))
deriving instance Show (AstBindingsCase s)

type AstBindings (s :: AstSpanType) = [(AstVarId, AstBindingsCase s)]


-- * ASTs

-- | AST for ranked tensors that are meant to be differentiated.
type role AstRanked nominal nominal nominal
  -- r has to be nominal, because type class arguments always are
data AstRanked :: AstSpanType -> RankedTensorType where
  AstVar :: IShR n -> AstVarName (AstRanked s) r n -> AstRanked s r n
  -- The r variable is existential here, so a proper specialization needs
  -- to be picked explicitly at runtime.
  AstLet :: forall n m r r2 s s2.
            (KnownNat n, KnownNat m, GoodScalar r, AstSpan s)
         => AstVarName (AstRanked s) r n -> AstRanked s r n
         -> AstRanked s2 r2 m
         -> AstRanked s2 r2 m
  AstShare :: AstVarName (AstRanked s) r n -> AstRanked s r n
           -> AstRanked s r n
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
             => IShR (p + n)
             -> AstRanked s r (m + n) -> (AstVarList m, AstIndex p)
             -> AstRanked s r (p + n)

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
  AstTranspose :: Permutation.PermR -> AstRanked s r n -> AstRanked s r n
  AstReshape :: KnownNat n
             => IShR m -> AstRanked s r n -> AstRanked s r m
  AstBuild1 :: KnownNat n
            => Int -> (IntVarName, AstRanked s r n)
            -> AstRanked s r (1 + n)
  AstGather :: forall m n p r s. (KnownNat m, KnownNat n, KnownNat p)
            => IShR (m + n)
            -> AstRanked s r (p + n) -> (AstVarList m, AstIndex p)
            -> AstRanked s r (m + n)
    -- out of bounds indexing is permitted
  -- There are existential variables here, as well.
  AstCast :: (GoodScalar r1, RealFrac r1, RealFrac r2)
          => AstRanked s r1 n -> AstRanked s r2 n
  AstFromIntegral :: (GoodScalar r1, Integral r1)
                  => AstRanked PrimalSpan r1 n -> AstRanked PrimalSpan r2 n
  AstConst :: Nested.Ranked n r -> AstRanked PrimalSpan r n
  AstProject :: AstHVector s -> Int -> AstRanked s r n
  AstLetHVectorIn :: AstSpan s
                  => [AstDynamicVarName] -> AstHVector s
                  -> AstRanked s2 r n
                  -> AstRanked s2 r n
  AstLetHFunIn :: AstVarId -> AstHFun
               -> AstRanked s2 r n
               -> AstRanked s2 r n
  AstRFromS :: KnownShS sh
            => AstShaped s r sh -> AstRanked s r (X.Rank sh)

  -- For the forbidden half of the RankedTensor class:
  AstConstant :: AstRanked PrimalSpan r n -> AstRanked FullSpan r n
  AstPrimalPart :: AstRanked FullSpan r n -> AstRanked PrimalSpan r n
  AstDualPart :: AstRanked FullSpan r n -> AstRanked DualSpan r n
  AstD :: AstRanked PrimalSpan r n -> AstRanked DualSpan r n
       -> AstRanked FullSpan r n

deriving instance GoodScalar r => Show (AstRanked s r n)

-- | AST for shaped tensors that are meant to be differentiated.
type role AstShaped nominal nominal nominal
data AstShaped :: AstSpanType -> ShapedTensorType where
  AstVarS :: forall sh r s. AstVarName (AstShaped s) r sh -> AstShaped s r sh
  AstLetS :: forall sh1 sh2 r r2 s s2.
             (KnownShS sh1, KnownShS sh2, GoodScalar r, AstSpan s)
          => AstVarName (AstShaped s) r sh1 -> AstShaped s r sh1
          -> AstShaped s2 r2 sh2
          -> AstShaped s2 r2 sh2
  AstShareS :: AstVarName (AstShaped s) r sh -> AstShaped s r sh
            -> AstShaped s r sh
  AstCondS :: AstBool
           -> AstShaped s r sh -> AstShaped s r sh -> AstShaped s r sh

  AstMinIndexS :: (KnownShS sh, KnownNat n, GoodScalar r, GoodScalar r2)
               => AstShaped PrimalSpan r (n ': sh)
               -> AstShaped PrimalSpan r2 (Sh.Init (n ': sh))
  AstMaxIndexS :: (KnownShS sh, KnownNat n, GoodScalar r, GoodScalar r2)
               => AstShaped PrimalSpan r (n ': sh)
               -> AstShaped PrimalSpan r2 (Sh.Init (n ': sh))
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
               (KnownShS sh1, KnownShS sh2, KnownShS (sh1 X.++ sh2))
            => AstShaped s r (sh1 X.++ sh2) -> AstIndexS sh1
            -> AstShaped s r sh2
    -- first ix is for outermost dimension; empty index means identity,
    -- if index is out of bounds, the result is defined and is 0,
    -- but vectorization is permitted to change the value
  AstSumS :: forall n sh r s. KnownNat n
          => AstShaped s r (n ': sh) -> AstShaped s r sh
  AstScatterS :: forall sh2 p sh r s.
                 ( KnownShS sh2, KnownShS sh
                 , KnownShS (Sh.Take p sh), KnownShS (Sh.Drop p sh)
                 , KnownShS (sh2 X.++ Sh.Drop p sh) )
              => AstShaped s r (sh2 X.++ Sh.Drop p sh)
              -> (AstVarListS sh2, AstIndexS (Sh.Take p sh))
              -> AstShaped s r sh

  AstFromVectorS :: (KnownNat n, KnownShS sh)
                 => Data.Vector.Vector (AstShaped s r sh)
                 -> AstShaped s r (n ': sh)
  AstReplicateS :: (KnownNat n, KnownShS sh)
                => AstShaped s r sh -> AstShaped s r (n ': sh)
  AstAppendS :: (KnownNat n, KnownNat m, KnownShS sh)
             => AstShaped s r (m ': sh) -> AstShaped s r (n ': sh)
             -> AstShaped s r ((m + n) ': sh)
  AstSliceS :: (KnownNat i, KnownNat n, KnownNat k, KnownShS sh)
            => AstShaped s r (i + n + k ': sh) -> AstShaped s r (n ': sh)
  AstReverseS :: (KnownNat n, KnownShS sh)
              => AstShaped s r (n ': sh) -> AstShaped s r (n ': sh)
  AstTransposeS :: forall perm sh r s.
                   (PermC perm, KnownShS sh, X.Rank perm <= X.Rank sh)
                => Permutation.Perm perm -> AstShaped s r sh
                -> AstShaped s r (Permutation.PermutePrefix perm sh)
  AstReshapeS :: (KnownShS sh, Nested.Internal.Shape.Product sh ~ Nested.Internal.Shape.Product sh2)
              => AstShaped s r sh -> AstShaped s r sh2
    -- beware that the order of type arguments is different than in orthotope
    -- and than the order of value arguments in the ranked version
  AstBuild1S :: (KnownNat n, KnownShS sh)
             => (IntVarName, AstShaped s r sh)
             -> AstShaped s r (n ': sh)
  AstGatherS :: forall sh2 p sh r s.
                ( KnownShS sh, KnownShS sh2
                , KnownShS (Sh.Take p sh), KnownShS (Sh.Drop p sh) )
             => AstShaped s r sh
             -> (AstVarListS sh2, AstIndexS (Sh.Take p sh))
             -> AstShaped s r (sh2 X.++ Sh.Drop p sh)
    -- out of bounds indexing is permitted
  AstCastS :: (GoodScalar r1, RealFrac r1, RealFrac r2)
           => AstShaped s r1 sh -> AstShaped s r2 sh
  AstFromIntegralS :: (GoodScalar r1, Integral r1)
                   => AstShaped PrimalSpan r1 sh -> AstShaped PrimalSpan r2 sh
  AstConstS :: Nested.Shaped sh r -> AstShaped PrimalSpan r sh
  AstProjectS :: AstHVector s -> Int -> AstShaped s r sh
  AstLetHVectorInS :: AstSpan s
                   => [AstDynamicVarName] -> AstHVector s
                   -> AstShaped s2 r sh
                   -> AstShaped s2 r sh
  AstLetHFunInS :: AstVarId -> AstHFun
                -> AstShaped s2 r sh
                -> AstShaped s2 r sh
  AstSFromR :: (KnownShS sh, KnownNat (X.Rank sh))
            => AstRanked s r (X.Rank sh) -> AstShaped s r sh

  -- For the forbidden half of the ShapedTensor class:
  AstConstantS :: AstShaped PrimalSpan r sh -> AstShaped FullSpan r sh
  AstPrimalPartS :: AstShaped FullSpan r sh -> AstShaped PrimalSpan r sh
  AstDualPartS :: AstShaped FullSpan r sh -> AstShaped DualSpan r sh
  AstDS :: AstShaped PrimalSpan r sh -> AstShaped DualSpan r sh
        -> AstShaped FullSpan r sh

deriving instance (GoodScalar r, KnownShS sh) => Show (AstShaped s r sh)

type AstDynamic (s :: AstSpanType) = DynamicTensor (AstRanked s)

type role AstHVector nominal
data AstHVector :: AstSpanType -> Type where
  -- There are existential variables inside DynamicTensor here.
  AstMkHVector :: HVector (AstRanked s) -> AstHVector s
  AstHApply :: AstHFun -> [HVector (AstRanked s)] -> AstHVector s
  -- The operations below is why we need AstHVector and so HVectorOf.
  -- If we kept a vector of terms instead, we'd need to let-bind in each
  -- of the terms separately, duplicating the let-bound term.
  AstLetHVectorInHVector
    :: AstSpan s
    => [AstDynamicVarName] -> AstHVector s
    -> AstHVector s2
    -> AstHVector s2
  AstLetHFunInHVector :: AstVarId -> AstHFun
                      -> AstHVector s2
                      -> AstHVector s2
  -- The r variable is existential here, so a proper specialization needs
  -- to be picked explicitly at runtime.
  AstLetInHVector :: (KnownNat n, GoodScalar r, AstSpan s)
                  => AstVarName (AstRanked s) r n -> AstRanked s r n
                  -> AstHVector s2
                  -> AstHVector s2
  AstLetInHVectorS :: (KnownShS sh, GoodScalar r, AstSpan s)
                   => AstVarName (AstShaped s) r sh -> AstShaped s r sh
                   -> AstHVector s2
                   -> AstHVector s2
  AstShareHVector :: [AstDynamicVarName] -> AstHVector s
                  -> AstHVector s
  AstBuildHVector1 :: SNat k -> (IntVarName, AstHVector s) -> AstHVector s
  AstMapAccumRDer
    :: SNat k
    -> VoidHVector
    -> VoidHVector
    -> VoidHVector
    -> AstHFun
    -> AstHFun
    -> AstHFun
    -> AstHVector s
    -> AstHVector s
    -> AstHVector s
  AstMapAccumLDer
    :: SNat k
    -> VoidHVector
    -> VoidHVector
    -> VoidHVector
    -> AstHFun
    -> AstHFun
    -> AstHFun
    -> AstHVector s
    -> AstHVector s
    -> AstHVector s

deriving instance Show (AstHVector s)

data AstHFun where
  AstLambda :: ~([[AstDynamicVarName]], AstHVector PrimalSpan) -> AstHFun
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
  AstVarHFun :: [VoidHVector] -> VoidHVector -> AstVarId -> AstHFun

deriving instance Show AstHFun

data AstBool where
  AstBoolNot :: AstBool -> AstBool
  AstB2 :: OpCodeBool -> AstBool -> AstBool -> AstBool
  AstBoolConst :: Bool -> AstBool
  -- There are existential variables here, as well.
  AstRel :: (KnownNat n, GoodScalar r)
         => OpCodeRel -> AstRanked PrimalSpan r n -> AstRanked PrimalSpan r n
         -> AstBool
  AstRelS :: (KnownShS sh, GoodScalar r)
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

instance (Num (Nested.Ranked n r), AstSpan s, KnownNat n)
         => Num (AstRanked s r n) where
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
  fromInteger :: Integer -> AstRanked s r n
  fromInteger i = case sameNat (Proxy @n) (Proxy @0) of
    Just Refl -> fromPrimal . AstConst . fromInteger $ i
    Nothing -> error $ "fromInteger not defined for AstRanked of non-zero ranks: "
                       ++ show (i, valueOf @n :: Int)
    -- it's crucial that there is no AstConstant in fromInteger code
    -- so that we don't need 4 times the simplification rules

instance (Real (Nested.Ranked n r), AstSpan s, KnownNat n)
         => Real (AstRanked s r n) where
  toRational = undefined
    -- very low priority, since these are all extremely not continuous

-- Warning: div and mod operations are very costly (simplifying them
-- requires constructing conditionals, etc). If this error is removed,
-- they are going to work, but slowly.
instance Integral r => IntegralF (AstRanked s r n) where
  quotF = AstI2 QuotOp
  remF = AstI2 RemOp

instance (GoodScalar r, Differentiable r, Fractional (Nested.Ranked n r), AstSpan s, KnownNat n)
         => Fractional (AstRanked s r n) where
  u / v = AstR2 DivideOp u v
  recip = AstR1 RecipOp
  fromRational r = error $ "fromRational not defined for AstRanked: "
                           ++ show r

instance (GoodScalar r, Differentiable r, Floating (Nested.Ranked n r), AstSpan s, KnownNat n)
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

instance (GoodScalar r, Differentiable r, RealFrac (Nested.Ranked n r), AstSpan s, KnownNat n)
         => RealFrac (AstRanked s r n) where
  properFraction = undefined
    -- The integral type doesn't have a Storable constraint,
    -- so we can't implement this (nor RealFracB from Boolean package).

instance (GoodScalar r, Differentiable r, Floating (Nested.Ranked n r), AstSpan s, KnownNat n)
         => RealFloatF (AstRanked s r n) where
  atan2F = AstR2 Atan2Op


-- * Unlawful numeric instances of shaped AST; they are lawful modulo evaluation

instance Eq (AstShaped s r sh) where
  (==) = error "AST requires that EqF be used instead"
  (/=) = error "AST requires that EqF be used instead"

instance Ord (AstShaped s r sh) where
  (<=) = error "AST requires that OrdF be used instead"

instance (GoodScalar r, Num (Nested.Shaped sh r))
         => Num (AstShaped s r sh) where
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
instance Integral r => IntegralF (AstShaped s r sh) where
  quotF = AstI2S QuotOp
  remF = AstI2S RemOp

instance (GoodScalar r, Differentiable r, Fractional (Nested.Shaped sh r))
         => Fractional (AstShaped s r sh) where
  u / v = AstR2S DivideOp u v
  recip = AstR1S RecipOp
  fromRational r = error $ "fromRational not defined for AstShaped: "
                           ++ show r

instance (GoodScalar r, Differentiable r, KnownShS sh, Floating (Nested.Shaped sh r), AstSpan s)
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

instance (GoodScalar r, Differentiable r, KnownShS sh, Floating (Nested.Shaped sh r), AstSpan s)
         => RealFloatF (AstShaped s r sh) where
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
type instance HVectorOf (AstRaw s) = AstRawWrap (AstHVector s)
type instance HFunOf (AstRaw s) = AstHFun
type instance RankedOf (AstRawS s) = AstRaw s
type instance ShapedOf (AstRawS s) = AstRawS s
type instance PrimalOf (AstRawS s) = AstRawS PrimalSpan
type instance DualOf (AstRawS s) = AstRawS DualSpan

type instance RankedOf (AstNoVectorize s) = AstNoVectorize s
type instance ShapedOf (AstNoVectorize s) = AstNoVectorizeS s
type instance PrimalOf (AstNoVectorize s) = AstNoVectorize PrimalSpan
type instance DualOf (AstNoVectorize s) = AstNoVectorize DualSpan
type instance HVectorOf (AstNoVectorize s) = AstNoVectorizeWrap (AstHVector s)
type instance HFunOf (AstNoVectorize s) = AstHFun
type instance RankedOf (AstNoVectorizeS s) = AstNoVectorize s
type instance ShapedOf (AstNoVectorizeS s) = AstNoVectorizeS s
type instance PrimalOf (AstNoVectorizeS s) = AstNoVectorizeS PrimalSpan
type instance DualOf (AstNoVectorizeS s) = AstNoVectorizeS DualSpan

type instance RankedOf (AstNoSimplify s) = AstNoSimplify s
type instance ShapedOf (AstNoSimplify s) = AstNoSimplifyS s
type instance PrimalOf (AstNoSimplify s) = AstNoSimplify PrimalSpan
type instance DualOf (AstNoSimplify s) = AstNoSimplify DualSpan
type instance HVectorOf (AstNoSimplify s) = AstNoSimplifyWrap (AstHVector s)
type instance HFunOf (AstNoSimplify s) = AstHFun
type instance RankedOf (AstNoSimplifyS s) = AstNoSimplify s
type instance ShapedOf (AstNoSimplifyS s) = AstNoSimplifyS s
type instance PrimalOf (AstNoSimplifyS s) = AstNoSimplifyS PrimalSpan
type instance DualOf (AstNoSimplifyS s) = AstNoSimplifyS DualSpan

type role AstRaw nominal nominal nominal
newtype AstRaw s r n =
  AstRaw {unAstRaw :: AstRanked s r n}
deriving instance GoodScalar r => Show (AstRaw s r n)

type role AstRawS nominal nominal nominal
newtype AstRawS s r sh =
  AstRawS {unAstRawS :: AstShaped s r sh}
deriving instance (GoodScalar r, KnownShS sh) => Show (AstRawS s r sh)

type role AstRawWrap nominal
newtype AstRawWrap t = AstRawWrap {unAstRawWrap :: t}
 deriving Show

type role AstNoVectorize nominal nominal nominal
newtype AstNoVectorize s r n =
  AstNoVectorize {unAstNoVectorize :: AstRanked s r n}
deriving instance GoodScalar r => Show (AstNoVectorize s r n)

type role AstNoVectorizeS nominal nominal nominal
newtype AstNoVectorizeS s r sh =
  AstNoVectorizeS {unAstNoVectorizeS :: AstShaped s r sh}
deriving instance (GoodScalar r, KnownShS sh) => Show (AstNoVectorizeS s r sh)

type role AstNoVectorizeWrap nominal
newtype AstNoVectorizeWrap t = AstNoVectorizeWrap {unAstNoVectorizeWrap :: t}
 deriving Show

type role AstNoSimplify nominal nominal nominal
newtype AstNoSimplify s r n =
  AstNoSimplify {unAstNoSimplify :: AstRanked s r n}
deriving instance GoodScalar r => Show (AstNoSimplify s r n)

type role AstNoSimplifyS nominal nominal nominal
newtype AstNoSimplifyS s r sh =
  AstNoSimplifyS {unAstNoSimplifyS :: AstShaped s r sh}
deriving instance (GoodScalar r, KnownShS sh) => Show (AstNoSimplifyS s r sh)

type role AstNoSimplifyWrap nominal
newtype AstNoSimplifyWrap t = AstNoSimplifyWrap {unAstNoSimplifyWrap :: t}
 deriving Show
