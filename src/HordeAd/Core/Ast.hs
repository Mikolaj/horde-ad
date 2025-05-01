{-# LANGUAGE ViewPatterns #-}
-- | AST of corresponding to the horde-ad operations specified
-- in the 'BaseTensor' class and others.
-- The AST is essential for efficient handling of second order operations
-- such as build and map via BOT (bulk-operation transformation),
-- and fold and mapAccum via symbolic nested derivatives.
-- It also permits producing reusable reverse derivative terms,
-- which can be simplified, fused, inlined once and then
-- interpreted many times.
--
-- Note that @Ast*@ modules rarely depend on @Ops*@ and @Carriers*@ modules
-- (except for "HordeAd.Core.AstInterpret" and "HordeAd.Core.AstEnv"
-- that describe how to go from @Ast*@ to @Ops*@). Similarly, @Ops*@
-- and @Carriers*@ modules rarely depend on @Ast*@ modules
-- (except for "HordeAd.Core.OpsAst" and "HordeAd.Core.CarriersAst"
-- that describe how to define @Ops*@ in terms of @Ast*@).
-- Syntax is relatively separated from semantics and they meet
-- in the interpreter ("HordeAd.Core.AstInterpret")
-- and in the semantic model constructed from syntax ("HordeAd.Core.OpsAst").
--
-- (A copy of the text above is in "HordeAd.Core.Ops".)
module HordeAd.Core.Ast
  ( -- * The AstSpan tags and class
    AstSpanType(..), AstSpan(..), sameAstSpan
    -- * Variables and related types
  , AstVarId, intToAstVarId
  , AstInt, IntVarName, pattern AstIntVar
  , AstVarName, mkAstVarName, varNameToAstVarId, varNameToFTK, varNameToBounds
  , AstArtifactRev(..), AstArtifactFwd(..)
  , AstIxS, AstVarListS, pattern AstLeqInt
    -- * AST
  , AstMethodOfSharing(..), AstTensor(..)
  , AstHFun(..)
  , AstBool(..), OpCodeNum1(..), OpCode1(..), OpCode2(..), OpCodeIntegral2(..)
  ) where

import Prelude hiding (foldl')

import Data.Dependent.EnumMap.Strict qualified as DMap
import Data.Functor.Const
import Data.Int (Int64)
import Data.Kind (Type)
import Data.Some
import Data.Type.Equality (TestEquality (..), (:~:) (Refl))
import Data.Vector.Strict qualified as Data.Vector
import GHC.TypeLits (type (+), type (<=))
import Type.Reflection (Typeable, typeRep)

import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape
import Data.Array.Mixed.Types (Init)
import Data.Array.Nested (type (++))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape

import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- * The AstSpan tags and class

-- | A kind (a type intended to be promoted) marking whether an AST term
-- is supposed to denote the primal part of a dual number, the dual part
-- or the whole dual number. It's mainly used to index the terms
-- of the AstTensor type  and related GADTs.
type data AstSpanType = PrimalSpan | DualSpan | FullSpan

class Typeable s => AstSpan (s :: AstSpanType) where
  fromPrimal :: AstTensor ms PrimalSpan y -> AstTensor ms s y
  fromDual :: AstTensor ms DualSpan y -> AstTensor ms s y
  primalPart :: AstTensor ms s y -> AstTensor ms PrimalSpan y
  dualPart :: AstTensor ms s y -> AstTensor ms DualSpan y

-- These are weak instance and we can't move them to AstSimplify,
-- because it's too late and also astPrimalPart only works on AstMethodLet.
instance {-# OVERLAPPABLE #-} AstSpan PrimalSpan where
  fromPrimal = id
  fromDual t = AstPrimalPart $ AstFromDual t  -- this is primal zero
  primalPart t = t
  dualPart t = AstDualPart $ AstFromPrimal t  -- this is dual zero

instance {-# OVERLAPPABLE #-} AstSpan DualSpan where
  fromPrimal t = AstDualPart $ AstFromPrimal t  -- this is dual zero
  fromDual = id
  primalPart t = AstPrimalPart $ AstFromDual t  -- this is primal zero
  dualPart t = t

instance {-# OVERLAPPABLE #-} AstSpan FullSpan where
  fromPrimal = AstFromPrimal
  fromDual = AstFromDual
  primalPart (AstFromPrimal t) = t
  primalPart t = AstPrimalPart t
  dualPart (AstFromDual t) = t
  dualPart t = AstDualPart t

sameAstSpan :: forall s1 s2. (AstSpan s1, AstSpan s2) => Maybe (s1 :~: s2)
sameAstSpan = testEquality (typeRep @s1) (typeRep @s2)


-- * Variables and related types

newtype AstVarId = AstVarId Int
 deriving (Eq, Ord, Show, Enum)

intToAstVarId :: Int -> AstVarId
intToAstVarId = AstVarId

type role AstVarName phantom nominal
data AstVarName :: AstSpanType -> TK -> Type where
  AstVarName :: forall s y.
                FullShapeTK y -> Int64 -> Int64 -> AstVarId
             -> AstVarName s y

instance Eq (AstVarName s y) where
  AstVarName _ _ _ varId1 == AstVarName _ _ _ varId2 = varId1 == varId2

instance Show (AstVarName s y) where
  showsPrec d (AstVarName _ _ _ varId) =
    showsPrec d varId  -- less verbose, more readable

instance DMap.Enum1 (AstVarName s) where
  type Enum1Info (AstVarName s) = Some FtkAndBounds
  fromEnum1 (AstVarName ftk minb maxb varId) =
    (fromEnum varId, Some (FtkAndBounds ftk minb maxb))
  toEnum1 varIdInt (Some (FtkAndBounds ftk minb maxb)) =
    Some $ AstVarName ftk minb maxb $ toEnum varIdInt

type role FtkAndBounds nominal
data FtkAndBounds y = FtkAndBounds (FullShapeTK y) Int64 Int64

instance TestEquality (AstVarName s) where
  testEquality (AstVarName ftk1 _ _ _) (AstVarName ftk2 _ _ _) =
    matchingFTK ftk1 ftk2

mkAstVarName :: forall s y.
                FullShapeTK y -> Maybe (Int64, Int64) -> AstVarId
             -> AstVarName s y
mkAstVarName ftk Nothing = AstVarName ftk (-1000000000) 1000000000
mkAstVarName ftk (Just (minb, maxb)) = AstVarName ftk minb maxb

varNameToAstVarId :: AstVarName s y -> AstVarId
varNameToAstVarId (AstVarName _ _ _ varId) = varId

varNameToFTK :: AstVarName s y -> FullShapeTK y
varNameToFTK (AstVarName ftk _ _ _) = ftk

varNameToBounds :: AstVarName s y -> Maybe (Int64, Int64)
varNameToBounds (AstVarName _ minb maxb _) =
  if minb == -1000000000 && maxb == 1000000000
  then Nothing
  else Just (minb, maxb)

-- | The reverse derivative artifact.
type role AstArtifactRev nominal nominal
data AstArtifactRev x z = AstArtifactRev
  { artVarDtRev      :: AstVarName PrimalSpan (ADTensorKind z)
  , artVarDomainRev  :: AstVarName PrimalSpan x
  , artDerivativeRev :: AstTensor AstMethodLet PrimalSpan (ADTensorKind x)
  , artPrimalRev     :: AstTensor AstMethodLet PrimalSpan z
  }
 deriving Show

-- | The forward derivative artifact.
type role AstArtifactFwd nominal nominal
data AstArtifactFwd x z = AstArtifactFwd
  { artVarDsFwd      :: AstVarName PrimalSpan (ADTensorKind x)
  , artVarDomainFwd  :: AstVarName PrimalSpan x
  , artDerivativeFwd :: AstTensor AstMethodLet PrimalSpan (ADTensorKind z)
  , artPrimalFwd     :: AstTensor AstMethodLet PrimalSpan z
  }
 deriving Show

-- | This is the (arbitrarily) chosen representation of terms denoting
-- integers in the indexes of tensor operations.
type AstInt ms = AstTensor ms PrimalSpan (TKScalar Int64)
-- ~ IntOf (AstTensor ms FullSpan)

type IntVarName = AstVarName PrimalSpan (TKScalar Int64)

pattern AstIntVar :: IntVarName -> AstInt ms
pattern AstIntVar var = AstVar var

-- Data invariant: the var names have bounds of the form (0, k - 1),
-- where the corresponding dimension in sh is k. This is never checked.
type AstVarListS sh = ListS sh (Const IntVarName)

-- There's no data invariant here. The shape matches rather the argument
-- of indexing (or gather) than the indexes.
type AstIxS ms sh = IxS sh (AstInt ms)

pattern AstLeqInt :: AstInt ms -> AstInt ms -> AstBool ms
pattern AstLeqInt t u <- (matchAstLeqInt -> Just (t, u))
  where AstLeqInt t u = AstLeqK t u

matchAstLeqInt :: AstBool ms -> Maybe (AstInt ms, AstInt ms)
matchAstLeqInt (AstLeqK @r t u)
  | Just Refl <- testEquality (typeRep @r) (typeRep @Int64) =
      Just (t, u)
matchAstLeqInt _ = Nothing


-- * AST

type data AstMethodOfSharing = AstMethodShare | AstMethodLet

-- | AST for tensors that are meant to be differentiated.
type role AstTensor nominal nominal nominal
data AstTensor :: AstMethodOfSharing -> AstSpanType -> Target where
  -- General operations, for scalar, ranked, shared and other tensors at once
  AstPair :: forall y z ms s.
             AstTensor ms s y -> AstTensor ms s z
          -> AstTensor ms s (TKProduct y z)
  AstProject1 :: forall y z ms s.
                 AstTensor ms s (TKProduct y z) -> AstTensor ms s y
  AstProject2 :: forall y z ms s.
                 AstTensor ms s (TKProduct y z) -> AstTensor ms s z
  AstFromVector :: forall y k ms s.
                   SNat k -> SingletonTK y
                -> Data.Vector.Vector (AstTensor ms s y)
                -> AstTensor ms s (BuildTensorKind k y)
  AstSum :: forall y k ms s.
            SNat k -> SingletonTK y
         -> AstTensor ms s (BuildTensorKind k y)
         -> AstTensor ms s y
  AstReplicate :: forall y k ms s.
                  SNat k -> SingletonTK y
               -> AstTensor ms s y
               -> AstTensor ms s (BuildTensorKind k y)
  AstMapAccumRDer
    :: forall accy by ey k ms s.
       SNat k
    -> FullShapeTK by
    -> FullShapeTK ey
    -> AstHFun s s
               (TKProduct accy ey) (TKProduct accy by)
    -> AstHFun s s
               (TKProduct (ADTensorKind (TKProduct accy ey))
                          (TKProduct accy ey))
               (ADTensorKind (TKProduct accy by))
    -> AstHFun s s
               (TKProduct (ADTensorKind (TKProduct accy by))
                          (TKProduct accy ey))
               (ADTensorKind (TKProduct accy ey))
    -> AstTensor ms s accy
    -> AstTensor ms s (BuildTensorKind k ey)
    -> AstTensor ms s (TKProduct accy (BuildTensorKind k by))
  AstMapAccumLDer
    :: forall accy by ey k ms s.
       SNat k
    -> FullShapeTK by
    -> FullShapeTK ey
    -> AstHFun s s
               (TKProduct accy ey) (TKProduct accy by)
    -> AstHFun s s
               (TKProduct (ADTensorKind (TKProduct accy ey))
                          (TKProduct accy ey))
               (ADTensorKind (TKProduct accy by))
    -> AstHFun s s
               (TKProduct (ADTensorKind (TKProduct accy by))
                          (TKProduct accy ey))
               (ADTensorKind (TKProduct accy ey))
    -> AstTensor ms s accy
    -> AstTensor ms s (BuildTensorKind k ey)
    -> AstTensor ms s (TKProduct accy (BuildTensorKind k by))
  AstApply :: (AstSpan s1, AstSpan s)
           => AstHFun s1 s x z -> AstTensor ms s1 x -> AstTensor ms s z
  AstVar :: AstVarName s y -> AstTensor ms s y
  AstCond :: forall y ms s.
             AstBool ms -> AstTensor ms s y -> AstTensor ms s y
          -> AstTensor ms s y
  AstBuild1 :: forall y k ms s.
               SNat k -> SingletonTK y
            -> (IntVarName, AstTensor ms s y)
            -> AstTensor ms s (BuildTensorKind k y)

  -- Sharing-related operations, mutually exclusive via AstMethodOfSharing
  AstLet :: forall y z s s2. AstSpan s
         => AstVarName s y -> AstTensor AstMethodLet s y
         -> AstTensor AstMethodLet s2 z
         -> AstTensor AstMethodLet s2 z
  AstShare :: AstVarName s y -> AstTensor AstMethodShare s y
           -> AstTensor AstMethodShare s y
  AstToShare :: AstTensor AstMethodLet s y
             -> AstTensor AstMethodShare s y

  -- Explicit dual numbers handling, eliminated in interpretation to ADVal
  AstPrimalPart :: forall y ms.
                   AstTensor ms FullSpan y -> AstTensor ms PrimalSpan y
  AstDualPart :: forall y ms.
                 AstTensor ms FullSpan y -> AstTensor ms DualSpan y
  AstFromPrimal :: forall y ms.
                   AstTensor ms PrimalSpan y -> AstTensor ms FullSpan y
  AstFromDual :: forall y ms.
                 AstTensor ms DualSpan y -> AstTensor ms FullSpan y

  -- Scalar arithmetic (to avoid the slowness of indexes as 1-element tensors)
  AstPlusK :: GoodScalar r
           => AstTensor ms s (TKScalar r)
           -> AstTensor ms s (TKScalar r)
           -> AstTensor ms s (TKScalar r)
  AstTimesK :: GoodScalar r
            => AstTensor ms s (TKScalar r)
            -> AstTensor ms s (TKScalar r)
            -> AstTensor ms s (TKScalar r)
  AstN1K :: GoodScalar r
         => OpCodeNum1 -> AstTensor ms s (TKScalar r)
         -> AstTensor ms s (TKScalar r)
  AstR1K :: (RealFloatH r, Nested.FloatElt r, GoodScalar r)
         => OpCode1 -> AstTensor ms s (TKScalar r)
         -> AstTensor ms s (TKScalar r)
  AstR2K :: (RealFloatH r, Nested.FloatElt r, GoodScalar r)
         => OpCode2 -> AstTensor ms s (TKScalar r)
         -> AstTensor ms s (TKScalar r)
         -> AstTensor ms s (TKScalar r)
  AstI2K :: (IntegralH r, Nested.IntElt r, GoodScalar r)
         => OpCodeIntegral2 -> AstTensor ms s (TKScalar r)
         -> AstTensor ms s (TKScalar r)
         -> AstTensor ms s (TKScalar r)
  AstConcreteK :: GoodScalar r
               => r -> AstTensor ms PrimalSpan (TKScalar r)
  AstFloorK :: (GoodScalar r1, RealFrac r1, GoodScalar r2, Integral r2)
            => AstTensor ms PrimalSpan (TKScalar r1)
            -> AstTensor ms PrimalSpan (TKScalar r2)
  AstFromIntegralK :: (GoodScalar r1, Integral r1, GoodScalar r2)
                   => AstTensor ms PrimalSpan (TKScalar r1)
                   -> AstTensor ms PrimalSpan (TKScalar r2)
  AstCastK :: (GoodScalar r1, RealFrac r1, RealFrac r2, GoodScalar r2)
           => AstTensor ms s (TKScalar r1) -> AstTensor ms s (TKScalar r2)

  -- Shaped arithmetic
  AstPlusS :: GoodScalar r
           => AstTensor ms s (TKS sh r)
           -> AstTensor ms s (TKS sh r)
           -> AstTensor ms s (TKS sh r)
  AstTimesS :: GoodScalar r
            => AstTensor ms s (TKS sh r)
            -> AstTensor ms s (TKS sh r)
            -> AstTensor ms s (TKS sh r)
  AstN1S :: GoodScalar r
         => OpCodeNum1 -> AstTensor ms s (TKS sh r)
         -> AstTensor ms s (TKS sh r)
  AstR1S :: (RealFloatH r, Nested.FloatElt r, GoodScalar r)
         => OpCode1 -> AstTensor ms s (TKS sh r)
         -> AstTensor ms s (TKS sh r)
  AstR2S :: (RealFloatH r, Nested.FloatElt r, GoodScalar r)
         => OpCode2 -> AstTensor ms s (TKS sh r)
         -> AstTensor ms s (TKS sh r)
         -> AstTensor ms s (TKS sh r)
  AstI2S :: (IntegralH r, Nested.IntElt r, GoodScalar r)
         => OpCodeIntegral2 -> AstTensor ms s (TKS sh r)
         -> AstTensor ms s (TKS sh r)
         -> AstTensor ms s (TKS sh r)
  AstConcreteS :: GoodScalar r
               => Nested.Shaped sh r -> AstTensor ms PrimalSpan (TKS sh r)
  AstFloorS :: (GoodScalar r1, RealFrac r1, Integral r2, GoodScalar r2)
            => AstTensor ms PrimalSpan (TKS sh r1)
            -> AstTensor ms PrimalSpan (TKS sh r2)
  AstFromIntegralS :: (GoodScalar r1, Integral r1, GoodScalar r2)
                   => AstTensor ms PrimalSpan (TKS sh r1)
                   -> AstTensor ms PrimalSpan (TKS sh r2)
  AstCastS :: (GoodScalar r1, RealFrac r1, GoodScalar r2, RealFrac r2)
           => AstTensor ms s (TKS sh r1)
           -> AstTensor ms s (TKS sh r2)

  -- Shaped tensor operations
  AstIndexS :: forall shm shn x s ms.
               ShS shn
            -> AstTensor ms s (TKS2 (shm ++ shn) x) -> AstIxS ms shm
            -> AstTensor ms s (TKS2 shn x)
    -- out of bounds indexing is permitted and the results is def
  AstScatterS :: forall shm shn shp x s ms.
                 ShS shn -> AstTensor ms s (TKS2 (shm ++ shn) x)
              -> (AstVarListS shm, AstIxS ms shp)
              -> AstTensor ms s (TKS2 (shp ++ shn) x)
    -- out of bounds indexing is permitted and the results is def or 0
  AstGatherS :: forall shm shn shp x s ms.
                ShS shn -> AstTensor ms s (TKS2 (shp ++ shn) x)
             -> (AstVarListS shm, AstIxS ms shp)
             -> AstTensor ms s (TKS2 (shm ++ shn) x)
    -- out of bounds indexing is permitted and the results is def
  AstMinIndexS :: forall n sh r r2 ms. (GoodScalar r, GoodScalar r2)
               => AstTensor ms PrimalSpan (TKS (n ': sh) r)
               -> AstTensor ms PrimalSpan (TKS (Init (n ': sh)) r2)
  AstMaxIndexS :: forall n sh r r2 ms. (GoodScalar r, GoodScalar r2)
               => AstTensor ms PrimalSpan (TKS (n ': sh) r)
               -> AstTensor ms PrimalSpan (TKS (Init (n ': sh)) r2)
  AstIotaS :: forall n r ms. GoodScalar r
           => SNat n -> AstTensor ms PrimalSpan (TKS '[n] r)
  AstAppendS :: forall m n sh x ms s.
                AstTensor ms s (TKS2 (m ': sh) x)
             -> AstTensor ms s (TKS2 (n ': sh) x)
             -> AstTensor ms s (TKS2 ((m + n) ': sh) x)
  AstSliceS :: SNat i -> SNat n -> SNat k
            -> AstTensor ms s (TKS2 (i + n + k ': sh) x)
            -> AstTensor ms s (TKS2 (n ': sh) x)
  AstReverseS :: forall n sh x ms s.
                 AstTensor ms s (TKS2 (n ': sh) x)
              -> AstTensor ms s (TKS2 (n ': sh) x)
  AstTransposeS :: (Permutation.IsPermutation perm, Rank perm <= Rank sh)
                => Permutation.Perm perm -> AstTensor ms s (TKS2 sh x)
                -> AstTensor ms s (TKS2 (Permutation.PermutePrefix perm sh) x)
  AstReshapeS :: Product sh ~ Product sh2
              => ShS sh2
              -> AstTensor ms s (TKS2 sh x) -> AstTensor ms s (TKS2 sh2 x)
  AstZipS :: AstTensor ms s (TKProduct (TKS2 sh y) (TKS2 sh z))
          -> AstTensor ms s (TKS2 sh (TKProduct y z))
  AstUnzipS :: AstTensor ms s (TKS2 sh (TKProduct y z))
            -> AstTensor ms s (TKProduct (TKS2 sh y) (TKS2 sh z))
  AstNestS :: forall sh1 sh2 x ms s.
              ShS sh1 -> ShS sh2
           -> AstTensor ms s (TKS2 (sh1 ++ sh2) x)
           -> AstTensor ms s (TKS2 sh1 (TKS2 sh2 x))
  AstUnNestS :: forall sh1 sh2 x ms s.
                AstTensor ms s (TKS2 sh1 (TKS2 sh2 x))
             -> AstTensor ms s (TKS2 (sh1 ++ sh2) x)

  -- Conversions
  AstFromS :: forall y z ms s.
              SingletonTK z
           -> AstTensor ms s y -> AstTensor ms s z
  AstSFromK :: GoodScalar r
            => AstTensor ms s (TKScalar r) -> AstTensor ms s (TKS '[] r)
  AstSFromR :: forall sh x ms s.
               ShS sh -> AstTensor ms s (TKR2 (Rank sh) x)
            -> AstTensor ms s (TKS2 sh x)
  AstSFromX :: forall sh sh' x ms s. Rank sh ~ Rank sh'
            => ShS sh -> AstTensor ms s (TKX2 sh' x)
            -> AstTensor ms s (TKS2 sh x)

  -- Backend-specific primitives
  AstSum0S :: AstTensor ms s (TKS2 sh x)
           -> AstTensor ms s (TKS2 '[] x)
  AstDot0S :: GoodScalar r
           => AstTensor ms s (TKS sh r) -> AstTensor ms s (TKS sh r)
           -> AstTensor ms s (TKS '[] r)
  AstDot1InS :: forall sh n r ms s. GoodScalar r
             => ShS sh -> SNat n
             -> AstTensor ms s (TKS (sh ++ '[n]) r)
             -> AstTensor ms s (TKS (sh ++ '[n]) r)
             -> AstTensor ms s (TKS sh r)
  AstMatmul2S :: GoodScalar r
              => SNat m -> SNat n -> SNat p
              -> AstTensor ms s (TKS '[m, n] r)
              -> AstTensor ms s (TKS '[n, p] r)
              -> AstTensor ms s (TKS '[m, p] r)

deriving instance Show (AstTensor ms s y)
  -- for this to work, AstConcreteS can't take a Concrete

type role AstHFun nominal nominal nominal nominal
data AstHFun s s2 x z where
  AstLambda :: ~(AstVarName s x)
            -> ~(AstTensor AstMethodLet s2 z)
            -> AstHFun s s2 x z
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
    -- to under 2^n (old experimental results). Note, however,
    -- that if the n-th forward and reverse derivative is taken,
    -- the laziness is defeated.

deriving instance Show (AstHFun s s2 x z)

type role AstBool nominal
data AstBool ms where
  AstBoolConst :: Bool -> AstBool ms
  AstBoolNot :: AstBool ms -> AstBool ms
  AstBoolAnd :: AstBool ms -> AstBool ms -> AstBool ms
  -- There are existential variables here.
  AstLeqK :: forall r ms. GoodScalar r
          => AstTensor ms PrimalSpan (TKScalar r)
          -> AstTensor ms PrimalSpan (TKScalar r)
          -> AstBool ms
  AstLeqS :: forall sh r ms. GoodScalar r
          => AstTensor ms PrimalSpan (TKS sh r)
          -> AstTensor ms PrimalSpan (TKS sh r)
          -> AstBool ms
deriving instance Show (AstBool ms)

data OpCodeNum1 =
    NegateOp | AbsOp | SignumOp
 deriving (Show, Eq)

data OpCode1 =
    RecipOp
  | ExpOp | LogOp | SqrtOp
  | SinOp | CosOp | TanOp | AsinOp | AcosOp | AtanOp
  | SinhOp | CoshOp | TanhOp | AsinhOp | AcoshOp | AtanhOp
 deriving (Show, Eq)

data OpCode2 =
    DivideOp
  | PowerOp | LogBaseOp
  | Atan2Op
 deriving (Show, Eq)

data OpCodeIntegral2 =
    QuotOp | RemOp
 deriving (Show, Eq)
