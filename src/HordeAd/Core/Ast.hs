{-# LANGUAGE ViewPatterns #-}
-- | AST of corresponding to the horde-ad operations specified
-- in the 'HordeAd.Core.Ops.BaseTensor' class and others.
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
    AstSpanType(..), PrimalSpan, AstSpan(..), sameAstSpan
    -- * Variables and related types
  , AstVarId, intToAstVarId
  , AstInt, IntVarName, pattern AstIntVar
  , AstVarName, mkAstVarName, varNameToAstVarId, varNameToFTK, varNameToBounds
  , astVar
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

import Data.Array.Nested (type (++))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Permutation qualified as Permutation
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types (Init)

import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- * The AstSpan tags and class

-- | A kind (a type intended to be promoted) marking whether an AST term
-- is supposed to denote the (n-th iteration of taking the) primal part
-- of a dual number, the dual part or the whole dual number.
-- It's mainly used to index the terms of the AstTensor type
-- and related GADTs.
type data AstSpanType =
  PrimalStepSpan AstSpanType | DualSpan | FullSpan | PlainSpan
type PrimalSpan = PrimalStepSpan FullSpan

-- | A singleton type for `AstSpanType`.
type role SAstSpanType nominal
data SAstSpanType s where
  SPrimalStepSpan :: AstSpan s0
                  => SAstSpanType s0 -> SAstSpanType (PrimalStepSpan s0)
  SDualSpan :: SAstSpanType DualSpan
  SFullSpan :: SAstSpanType FullSpan
  SPlainSpan :: SAstSpanType PlainSpan

class KnownSpan (s :: AstSpanType) where
  knownSpan :: SAstSpanType s

-- These are weak instances rewriting-wise and we can't move them
-- to AstSimplify to improve this, because it's too late
-- and also astPrimalPart only works on AstMethodLet.
instance (KnownSpan s, AstSpan s) => KnownSpan (PrimalStepSpan s) where
  knownSpan = SPrimalStepSpan (knownSpan @s)

instance KnownSpan DualSpan where
  knownSpan = SDualSpan

instance KnownSpan FullSpan where
  knownSpan = SFullSpan

instance KnownSpan PlainSpan where
  knownSpan = SPlainSpan

class (KnownSpan s, Typeable s) => AstSpan (s :: AstSpanType) where
  fromPrimal :: AstTensor ms PrimalSpan y -> AstTensor ms s y
  fromDual :: AstTensor ms DualSpan y -> AstTensor ms s y
  fromPlain :: AstTensor ms PlainSpan y -> AstTensor ms s y
  primalPart :: AstTensor ms s y -> AstTensor ms PrimalSpan y
  dualPart :: AstTensor ms s y -> AstTensor ms DualSpan y
  plainPart :: AstTensor ms s y -> AstTensor ms PlainSpan y

-- These are weak instances rewriting-wise and we can't move them
-- to AstSimplify to improve this, because it's too late
-- and also astPrimalPart only works on AstMethodLet.
instance AstSpan s => AstSpan (PrimalStepSpan s) where
  fromPrimal = primalSpanToStep (knownSpan @s)
  fromDual t = dualSpanToStep (knownSpan @s) t  -- this is primal zero
  fromPlain t = plainSpanToStep (knownSpan @s) t
  primalPart = stepToPrimalSpan (knownSpan @s)
  dualPart t = stepToDualSpan (knownSpan @s) t  -- this is dual zero
  plainPart t = stepToPlainSpan (knownSpan @s) t

instance AstSpan DualSpan where
  fromPrimal t = AstDualPart $ AstFromPrimal t  -- this is dual zero
  fromDual = id
  fromPlain t = AstDualPart $ AstFromPlain t  -- this is dual zero
  primalPart t = AstPrimalPart $ AstFromDual t  -- this is primal zero
  dualPart = id
  plainPart t = AstPlainPart $ AstFromDual t  -- this is primal zero

instance AstSpan FullSpan where
  fromPrimal = AstFromPrimal
  fromDual = AstFromDual
  fromPlain = AstFromPlain
  primalPart = cAstPrimalPart
  dualPart = cAstDualPart
  plainPart = cAstPlainPart

instance AstSpan PlainSpan where
  fromPrimal = cAstPlainPart . AstFromPrimal
  fromDual t = AstPlainPart $ AstFromDual t  -- this is plain zero
  fromPlain = id
  primalPart = AstPrimalPart . AstFromPlain
  dualPart t = AstDualPart $ AstFromPlain t  -- this is dual zero
  plainPart = id

primalSpanToStep :: SAstSpanType s
                 -> AstTensor ms PrimalSpan y
                 -> AstTensor ms (PrimalStepSpan s) y
primalSpanToStep = \case
  SPrimalStepSpan sspan -> AstPrimalPart . primalSpanToStep sspan
  SDualSpan -> AstPrimalPart . AstDualPart . AstFromPrimal
  SFullSpan -> id
  SPlainSpan -> AstPrimalPart . cAstPlainPart . AstFromPrimal

dualSpanToStep :: SAstSpanType s
               -> AstTensor ms DualSpan y
               -> AstTensor ms (PrimalStepSpan s) y
dualSpanToStep = \case
  SPrimalStepSpan sspan -> AstPrimalPart . dualSpanToStep sspan
  SDualSpan -> AstPrimalPart
  SFullSpan -> AstPrimalPart . AstFromDual
  SPlainSpan -> AstPrimalPart . AstPlainPart . AstFromDual

plainSpanToStep :: SAstSpanType s
                -> AstTensor ms PlainSpan y
                -> AstTensor ms (PrimalStepSpan s) y
plainSpanToStep = \case
  SPrimalStepSpan sspan -> AstPrimalPart . plainSpanToStep sspan
  SDualSpan -> AstPrimalPart . AstDualPart . AstFromPlain
  SFullSpan -> AstPrimalPart . AstFromPlain
  SPlainSpan -> AstPrimalPart

stepToPrimalSpan :: SAstSpanType s
                 -> AstTensor ms (PrimalStepSpan s) y
                 -> AstTensor ms PrimalSpan y
stepToPrimalSpan = \case
  SPrimalStepSpan sspan -> stepToPrimalSpan sspan . AstFromPrimal
  SDualSpan -> AstPrimalPart . AstFromDual . AstFromPrimal
  SFullSpan -> id
  SPlainSpan -> AstPrimalPart . AstFromPlain . AstFromPrimal

stepToDualSpan :: SAstSpanType s
               -> AstTensor ms (PrimalStepSpan s) y
               -> AstTensor ms DualSpan y
stepToDualSpan = \case
  SPrimalStepSpan sspan -> stepToDualSpan sspan . AstFromPrimal
  SDualSpan -> AstFromPrimal
  SFullSpan -> AstDualPart . AstFromPrimal
  SPlainSpan -> AstDualPart . AstFromPlain . AstFromPrimal

stepToPlainSpan :: SAstSpanType s
                -> AstTensor ms (PrimalStepSpan s) y
                -> AstTensor ms PlainSpan y
stepToPlainSpan = \case
  SPrimalStepSpan sspan -> stepToPlainSpan sspan . AstFromPrimal
  SDualSpan -> AstPlainPart . AstFromDual . AstFromPrimal
  SFullSpan -> cAstPlainPart . AstFromPrimal
  SPlainSpan -> AstFromPrimal

sameAstSpan :: forall s1 s2. (AstSpan s1, AstSpan s2) => Maybe (s1 :~: s2)
sameAstSpan = testEquality (typeRep @s1) (typeRep @s2)

cAstPrimalPart :: forall y s ms. AstSpan s
               => AstTensor ms s y -> AstTensor ms (PrimalStepSpan s) y
cAstPrimalPart (AstFromPrimal t) = t
cAstPrimalPart t = AstPrimalPart t

cAstDualPart :: forall y ms.
                AstTensor ms FullSpan y -> AstTensor ms DualSpan y
cAstDualPart (AstFromDual t) = t
cAstDualPart t = AstDualPart t

cAstPlainPart :: forall y ms.
                 AstTensor ms FullSpan y -> AstTensor ms PlainSpan y
cAstPlainPart (AstFromPrimal (AstPrimalPart v)) = cAstPlainPart v
cAstPlainPart (AstFromPlain t) = t
cAstPlainPart t = AstPlainPart t


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

astVar :: AstSpan s
       => AstVarName s y -> AstTensor ms s y
astVar (AstVarName (FTKScalar @r) lb ub _)
  | lb == ub
  , Just Refl <- testEquality (typeRep @r) (typeRep @Int64) =
    fromPlain $ AstConcreteK lb
astVar varName = AstVar varName

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
type AstInt ms = AstTensor ms PlainSpan (TKScalar Int64)
-- ~ IntOf (AstTensor ms FullSpan)

type IntVarName = AstVarName PlainSpan (TKScalar Int64)

pattern AstIntVar :: IntVarName -> AstInt ms
pattern AstIntVar var <- AstVar var

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
  AstSum :: forall y k ms s. TKAllNum y
         => SNat k -> SingletonTK y
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
  AstPrimalPart :: forall y s ms. AstSpan s
                => AstTensor ms s y -> AstTensor ms (PrimalStepSpan s) y
  AstDualPart :: forall y ms.
                 AstTensor ms FullSpan y -> AstTensor ms DualSpan y
  AstPlainPart :: forall y ms.
                  AstTensor ms FullSpan y -> AstTensor ms PlainSpan y
  AstFromPrimal :: forall y s ms.
                   AstTensor ms (PrimalStepSpan s) y -> AstTensor ms s y
  AstFromDual :: forall y ms.
                 AstTensor ms DualSpan y -> AstTensor ms FullSpan y
  AstFromPlain :: forall y ms.
                  AstTensor ms PlainSpan y -> AstTensor ms FullSpan y

  -- Scalar arithmetic (to avoid the slowness of indexes as 1-element tensors)
  AstPlusK :: NumScalar r
           => AstTensor ms s (TKScalar r)
           -> AstTensor ms s (TKScalar r)
           -> AstTensor ms s (TKScalar r)
  AstTimesK :: NumScalar r
            => AstTensor ms s (TKScalar r)
            -> AstTensor ms s (TKScalar r)
            -> AstTensor ms s (TKScalar r)
  AstN1K :: NumScalar r
         => OpCodeNum1 -> AstTensor ms s (TKScalar r)
         -> AstTensor ms s (TKScalar r)
  AstR1K :: (RealFloatH r, Nested.FloatElt r, NumScalar r)
         => OpCode1 -> AstTensor ms s (TKScalar r)
         -> AstTensor ms s (TKScalar r)
  AstR2K :: (RealFloatH r, Nested.FloatElt r, NumScalar r)
         => OpCode2 -> AstTensor ms s (TKScalar r)
         -> AstTensor ms s (TKScalar r)
         -> AstTensor ms s (TKScalar r)
  AstI2K :: (IntegralH r, Nested.IntElt r, NumScalar r)
         => OpCodeIntegral2 -> AstTensor ms s (TKScalar r)
         -> AstTensor ms s (TKScalar r)
         -> AstTensor ms s (TKScalar r)
  AstConcreteK :: GoodScalar r
               => r -> AstTensor ms PlainSpan (TKScalar r)
  AstFloorK :: (GoodScalar r1, RealFrac r1, NumScalar r2, Integral r2)
            => AstTensor ms PrimalSpan (TKScalar r1)
            -> AstTensor ms PrimalSpan (TKScalar r2)
  AstFromIntegralK :: (GoodScalar r1, Integral r1, NumScalar r2)
                   => AstTensor ms PrimalSpan (TKScalar r1)
                   -> AstTensor ms PrimalSpan (TKScalar r2)
  AstCastK :: (NumScalar r1, RealFrac r1, RealFrac r2, NumScalar r2)
           => AstTensor ms s (TKScalar r1) -> AstTensor ms s (TKScalar r2)

  -- Shaped arithmetic
  AstPlusS :: NumScalar r
           => AstTensor ms s (TKS sh r)
           -> AstTensor ms s (TKS sh r)
           -> AstTensor ms s (TKS sh r)
  AstTimesS :: NumScalar r
            => AstTensor ms s (TKS sh r)
            -> AstTensor ms s (TKS sh r)
            -> AstTensor ms s (TKS sh r)
  AstN1S :: NumScalar r
         => OpCodeNum1 -> AstTensor ms s (TKS sh r)
         -> AstTensor ms s (TKS sh r)
  AstR1S :: (RealFloatH r, Nested.FloatElt r, NumScalar r)
         => OpCode1 -> AstTensor ms s (TKS sh r)
         -> AstTensor ms s (TKS sh r)
  AstR2S :: (RealFloatH r, Nested.FloatElt r, NumScalar r)
         => OpCode2 -> AstTensor ms s (TKS sh r)
         -> AstTensor ms s (TKS sh r)
         -> AstTensor ms s (TKS sh r)
  AstI2S :: (IntegralH r, Nested.IntElt r, NumScalar r)
         => OpCodeIntegral2 -> AstTensor ms s (TKS sh r)
         -> AstTensor ms s (TKS sh r)
         -> AstTensor ms s (TKS sh r)
  AstConcreteS :: GoodScalar r
               => Nested.Shaped sh r -> AstTensor ms PrimalSpan (TKS sh r)
  AstFloorS :: (GoodScalar r1, RealFrac r1, Integral r2, NumScalar r2)
            => AstTensor ms PrimalSpan (TKS sh r1)
            -> AstTensor ms PrimalSpan (TKS sh r2)
  AstFromIntegralS :: (GoodScalar r1, Integral r1, NumScalar r2)
                   => AstTensor ms PrimalSpan (TKS sh r1)
                   -> AstTensor ms PrimalSpan (TKS sh r2)
  AstCastS :: (NumScalar r1, RealFrac r1, NumScalar r2, RealFrac r2)
           => AstTensor ms s (TKS sh r1)
           -> AstTensor ms s (TKS sh r2)

  -- Shaped tensor operations
  AstIndexS :: forall shm shn x s ms.
               ShS shn
            -> AstTensor ms s (TKS2 (shm ++ shn) x) -> AstIxS ms shm
            -> AstTensor ms s (TKS2 shn x)
    -- out of bounds indexing is permitted and the results is def (==0)
  AstScatterS :: forall shm shn shp x s ms. TKAllNum x
              => ShS shn -> AstTensor ms s (TKS2 (shm ++ shn) x)
              -> (AstVarListS shm, AstIxS ms shp)
              -> AstTensor ms s (TKS2 (shp ++ shn) x)
    -- out of bounds indexing is permitted and the results is def (==0)
  AstGatherS :: forall shm shn shp x s ms.
                ShS shn -> AstTensor ms s (TKS2 (shp ++ shn) x)
             -> (AstVarListS shm, AstIxS ms shp)
             -> AstTensor ms s (TKS2 (shm ++ shn) x)
    -- out of bounds indexing is permitted and the results is def (==0)
  AstMinIndexS :: forall n sh r r2 ms. (NumScalar r, NumScalar r2)
               => AstTensor ms PrimalSpan (TKS (n ': sh) r)
               -> AstTensor ms PrimalSpan (TKS (Init (n ': sh)) r2)
  AstMaxIndexS :: forall n sh r r2 ms. (NumScalar r, NumScalar r2)
               => AstTensor ms PrimalSpan (TKS (n ': sh) r)
               -> AstTensor ms PrimalSpan (TKS (Init (n ': sh)) r2)
  AstIotaS :: forall n r ms. NumScalar r
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

  -- Conversions
  AstConvert :: TKConversion a b -> AstTensor ms s a -> AstTensor ms s b

  -- Backend-specific primitives
  AstSum0S :: TKAllNum x
           => AstTensor ms s (TKS2 sh x)
           -> AstTensor ms s (TKS2 '[] x)
  AstDot0S :: NumScalar r
           => AstTensor ms s (TKS sh r) -> AstTensor ms s (TKS sh r)
           -> AstTensor ms s (TKS '[] r)
  AstDot1InS :: forall sh n r ms s. NumScalar r
             => ShS sh -> SNat n
             -> AstTensor ms s (TKS (sh ++ '[n]) r)
             -> AstTensor ms s (TKS (sh ++ '[n]) r)
             -> AstTensor ms s (TKS sh r)
  AstMatmul2S :: NumScalar r
              => SNat m -> SNat n -> SNat p
              -> AstTensor ms s (TKS '[m, n] r)
              -> AstTensor ms s (TKS '[n, p] r)
              -> AstTensor ms s (TKS '[m, p] r)

deriving instance Show (AstTensor ms s y)
  -- for this to work, AstConcreteS can't take a Concrete;
  -- an alternative might be @Has Show (AstTensor ms s)@, but then we'd need
  -- to write @has@ before we apply @show@ and we'd weaken @AllTargetShow@

type role AstHFun nominal nominal nominal nominal
data AstHFun s s2 x z where
  AstLambda :: ~(AstVarName s x)
            -> ~(AstTensor AstMethodLet s2 z)
            -> AstHFun s s2 x z
    -- ^ The function body can't have any free variables outside those
    -- listed in the first component of the pair; this reflects
    -- the quantification in 'HordeAd.Core.Ops.rrev'
    -- and prevents "perturbation confusion".
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
  AstLeqK :: forall r ms. NumScalar r
          => AstTensor ms PlainSpan (TKScalar r)
          -> AstTensor ms PlainSpan (TKScalar r)
          -> AstBool ms
  AstLeqS :: forall sh r ms. NumScalar r
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
