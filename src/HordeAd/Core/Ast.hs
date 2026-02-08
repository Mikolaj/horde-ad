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
  ( -- * The AstSpan tags, singletons and operations
    AstSpan(..), PrimalSpan, SAstSpan(..), KnownSpan(..), withKnownSpan
  , primalPart, dualPart, plainPart, fromPrimal, fromDual, fromPlain
    -- * Variables and related types
  , AstVarId, intToAstVarId
  , AstInt, IntVarName, pattern AstIntVar, AstBool
  , AstVarName(..), FtkAndBounds(..)
  , mkAstVarName, mkAstVarNameBounds
  , reshapeVarName, respanVarName, reboundsVarName
  , varNameToAstVarId, varNameToSpan, varNameToFTK, varNameToBounds
  , AstArtifactRev(..), AstArtifactFwd(..)
  , AstIxS, AstVarListS, pattern AstLeqInt
    -- * AST
  , AstMethodOfSharing(..), AstTensor(..), AstHFun(..)
  , OpCodeNum1(..), OpCode1(..), OpCode2(..), OpCodeIntegral2(..)
  ) where

import Prelude

import Data.Dependent.EnumMap.Strict qualified as DMap
import Data.Kind (Type)
import Data.Type.Equality (TestEquality (..), (:~:) (Refl))
import Data.Vector.Strict qualified as Data.Vector
import GHC.Exts (withDict)
import GHC.TypeLits (type (+), type (<=))
import Type.Reflection (typeRep)

import Data.Array.Nested (type (++))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Permutation qualified as Permutation
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types (Init)

import HordeAd.Core.Conversion
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- * The AstSpan tags, singletons and operations

-- | A type intended to be promoted that marks whether an AST term
-- is supposed to denote the (n-th iteration of taking the) primal part
-- of a dual number, the dual part, the whole dual number or a plain value.
-- It's mainly used to index the terms of the AstTensor type
-- and related GADTs.
type data AstSpan =
  FullSpan | PrimalStepSpan AstSpan | DualSpan | PlainSpan
type PrimalSpan = PrimalStepSpan FullSpan

-- | The singleton type for `AstSpan`.
type role SAstSpan nominal
data SAstSpan s where
  SFullSpan :: SAstSpan FullSpan
  SPrimalStepSpan :: SAstSpan s -> SAstSpan (PrimalStepSpan s)
  SDualSpan :: SAstSpan DualSpan
  SPlainSpan :: SAstSpan PlainSpan

instance TestEquality SAstSpan where
  testEquality SFullSpan SFullSpan = Just Refl
  testEquality (SPrimalStepSpan s1) (SPrimalStepSpan s2)
    | Just Refl <- testEquality s1 s2 = Just Refl
  testEquality SDualSpan SDualSpan = Just Refl
  testEquality SPlainSpan SPlainSpan = Just Refl
  testEquality _ _ = Nothing

-- These are weak definitions rewriting-wise and we can't move them
-- to AstSimplify to improve this, because it's too late
-- and also astPrimalPart only works on AstMethodLet.
primalPart :: forall s ms y. KnownSpan s
           => AstTensor ms s y -> AstTensor ms (PrimalStepSpan s) y
primalPart t = case knownSpan @s of
  SFullSpan -> cAstPrimalPart t
  SPrimalStepSpan{} -> cAstPrimalPart t
  SDualSpan -> fullSpanToStep knownSpan $ AstFromDual t  -- this is primal zero
  SPlainSpan -> cAstPrimalPart t

dualPart :: forall s ms y. KnownSpan s
         => AstTensor ms s y -> AstTensor ms DualSpan y
dualPart t = case knownSpan @s of
  SFullSpan -> cAstDualPart t
  SPrimalStepSpan s -> cAstDualPart $ stepToFullSpan s t  -- this is dual zero
  SDualSpan -> t
  SPlainSpan -> AstDualPart $ AstFromPlain t  -- this is dual zero

plainPart :: forall s ms y. KnownSpan s
          => AstTensor ms s y -> AstTensor ms PlainSpan y
plainPart t = case knownSpan @s of
  SFullSpan -> cAstPlainPart t
  SPrimalStepSpan{} -> cAstPlainPart t
  SDualSpan -> AstPlainPart $ AstFromDual t  -- this is plain zero
  SPlainSpan -> t

fromPrimal :: forall s ms y. KnownSpan s
           => AstTensor ms (PrimalStepSpan s) y -> AstTensor ms s y
fromPrimal t = case knownSpan @s of
  SFullSpan -> cAstFromPrimal t
  SPrimalStepSpan{} -> cAstFromPrimal t
  SDualSpan -> cAstDualPart $ stepToFullSpan knownSpan t  -- this is dual zero
  SPlainSpan -> cAstPlainPart t

fromDual :: forall s ms y. KnownSpan s
         => AstTensor ms DualSpan y -> AstTensor ms s y
fromDual t = case knownSpan @s of
  SFullSpan -> AstFromDual t
  SPrimalStepSpan s -> fullSpanToStep s $ AstFromDual t  -- this is primal zero
  SDualSpan -> t
  SPlainSpan -> AstPlainPart $ AstFromDual t  -- this is plain zero

fromPlain :: forall s ms y. KnownSpan s
          => AstTensor ms PlainSpan y -> AstTensor ms s y
fromPlain t = case knownSpan @s of
  SFullSpan -> AstFromPlain t
  SPrimalStepSpan{} -> AstFromPlain t
  SDualSpan -> AstDualPart $ AstFromPlain t  -- this is dual zero
  SPlainSpan -> t

class KnownSpan (s :: AstSpan) where
  knownSpan :: SAstSpan s

instance KnownSpan FullSpan where
  knownSpan = SFullSpan

instance KnownSpan s => KnownSpan (PrimalStepSpan s) where
  knownSpan = SPrimalStepSpan (knownSpan @s)

instance KnownSpan DualSpan where
  knownSpan = SDualSpan

instance KnownSpan PlainSpan where
  knownSpan = SPlainSpan

-- | Turn a singleton into a constraint via a continuation.
withKnownSpan :: forall s r. SAstSpan s -> (KnownSpan s => r) -> r
withKnownSpan = withDict @(KnownSpan s)

fullSpanToStep :: SAstSpan s
               -> AstTensor ms FullSpan y
               -> AstTensor ms (PrimalStepSpan s) y
fullSpanToStep = \case
  SFullSpan -> cAstPrimalPart
  SPrimalStepSpan sspan -> withKnownSpan sspan
                           $ cAstPrimalPart . fullSpanToStep sspan
  SDualSpan -> cAstPrimalPart . cAstDualPart
  SPlainSpan -> cAstPrimalPart . cAstPlainPart

stepToFullSpan :: SAstSpan s
               -> AstTensor ms (PrimalStepSpan s) y
               -> AstTensor ms FullSpan y
stepToFullSpan = \case
  SFullSpan -> cAstFromPrimal
  SPrimalStepSpan sspan -> withKnownSpan sspan
                           $ stepToFullSpan sspan . cAstFromPrimal
  SDualSpan -> AstFromDual . cAstFromPrimal
  SPlainSpan -> AstFromPlain . cAstFromPrimal

cAstPrimalPart :: forall y s ms. KnownSpan s
               => AstTensor ms s y -> AstTensor ms (PrimalStepSpan s) y
cAstPrimalPart (AstFromPrimal t) = t
cAstPrimalPart (AstFromPlain t) = AstFromPlain t
cAstPrimalPart t = AstPrimalPart t

cAstDualPart :: forall y ms.
                AstTensor ms FullSpan y -> AstTensor ms DualSpan y
cAstDualPart (AstFromDual t) = t
cAstDualPart t = AstDualPart t

cAstPlainPart :: forall y s ms. KnownSpan s
              => AstTensor ms s y -> AstTensor ms PlainSpan y
cAstPlainPart (AstFromPlain v) = v
cAstPlainPart (AstPrimalPart v) = cAstPlainPart v
cAstPlainPart (AstFromPrimal v) = cAstPlainPart v
cAstPlainPart t | SPlainSpan <- knownSpan @s = t
cAstPlainPart t = AstPlainPart t

cAstFromPrimal :: forall y s ms. KnownSpan s
               => AstTensor ms (PrimalStepSpan s) y -> AstTensor ms s y
cAstFromPrimal (AstFromPlain t) = cAstFromPlain t
cAstFromPrimal t = AstFromPrimal t

cAstFromPlain :: forall y s ms. KnownSpan s
              => AstTensor ms PlainSpan y -> AstTensor ms s y
cAstFromPlain t | SPlainSpan <- knownSpan @s = t
cAstFromPlain t = AstFromPlain t


-- * Variables and related types

newtype AstVarId = AstVarId Int
 deriving (Eq, Ord, Show, Enum)

intToAstVarId :: Int -> AstVarId
intToAstVarId = AstVarId

type role AstVarName nominal
data AstVarName :: (AstSpan, TK) -> Type where
  AstVarName :: AstVarId -> FtkAndBounds s_y -> AstVarName s_y

instance Eq (AstVarName '(s, y)) where
  AstVarName varId1 _ == AstVarName varId2 _ = varId1 == varId2

instance Show (AstVarName '(s, y)) where
  showsPrec d (AstVarName varId _) =
    showsPrec d varId  -- less verbose, more readable

instance TestEquality AstVarName where
  testEquality (AstVarName _ ftkBounds1) (AstVarName _ ftkBounds2)
    | Just Refl <- testEquality ftkBounds1 ftkBounds2 =
      Just Refl
  testEquality _ _ = Nothing

instance DMap.Enum1 AstVarName where
  type Enum1Info AstVarName = FtkAndBounds
  fromEnum1 (AstVarName varId ftkBounds) = (fromEnum varId, ftkBounds)
  toEnum1 varIdInt ftkBounds = AstVarName (toEnum varIdInt) ftkBounds

type role FtkAndBounds nominal
data FtkAndBounds :: (AstSpan, TK) -> Type where
  FtkAndBoundsFull :: FullShapeTK y
                   -> FtkAndBounds '(FullSpan, y)
  FtkAndBoundsPrimal :: FullShapeTK y -> SAstSpan s
                     -> FtkAndBounds '(PrimalStepSpan s, y)
  FtkAndBoundsDual :: FullShapeTK y
                   -> FtkAndBounds '(DualSpan, y)
  FtkAndBoundsPlain :: FullShapeTK y
                    -> FtkAndBounds '(PlainSpan, y)
  FtkAndBoundsBounds :: Int -> Int
                     -> FtkAndBounds '(PlainSpan, TKScalar Int)

instance TestEquality FtkAndBounds where
  testEquality ftkBounds1 ftkBounds2 = case (ftkBounds1, ftkBounds2) of
    (FtkAndBoundsFull ftk1, FtkAndBoundsFull ftk2)
      | Just Refl <- matchingFTK ftk1 ftk2 ->
        Just Refl
    (FtkAndBoundsPrimal ftk1 sspan1, FtkAndBoundsPrimal ftk2 sspan2)
      | Just Refl <- testEquality sspan1 sspan2
      , Just Refl <- matchingFTK ftk1 ftk2 ->
        Just Refl
    (FtkAndBoundsDual ftk1, FtkAndBoundsDual ftk2)
      | Just Refl <- matchingFTK ftk1 ftk2 ->
        Just Refl
    (FtkAndBoundsPlain ftk1, FtkAndBoundsPlain ftk2)
      | Just Refl <- matchingFTK ftk1 ftk2 ->
        Just Refl
    (FtkAndBoundsBounds _ _ , FtkAndBoundsBounds _ _) ->
      Just Refl
    _ -> Nothing

mkAstVarName :: forall s y. KnownSpan s
             => FullShapeTK y -> AstVarId -> AstVarName '(s, y)
mkAstVarName ftk varId =
  let ftkBounds = case knownSpan @s of
        SFullSpan -> FtkAndBoundsFull ftk
        SPrimalStepSpan sspan -> FtkAndBoundsPrimal ftk sspan
        SDualSpan -> FtkAndBoundsDual ftk
        SPlainSpan -> FtkAndBoundsPlain ftk
  in AstVarName varId ftkBounds

mkAstVarNameBounds :: (Int, Int) -> AstVarId
                   -> AstVarName '(PlainSpan, TKScalar Int)
{-# INLINE mkAstVarNameBounds #-}
mkAstVarNameBounds (lb, ub) varId = AstVarName varId $ FtkAndBoundsBounds lb ub

reshapeVarName :: FullShapeTK z -> AstVarName '(s, y) -> AstVarName '(s, z)
reshapeVarName ftk (AstVarName varId ftkBounds) =
  AstVarName varId $ case ftkBounds of
    FtkAndBoundsFull{} -> FtkAndBoundsFull ftk
    (FtkAndBoundsPrimal _ sspan) -> FtkAndBoundsPrimal ftk sspan
    FtkAndBoundsDual{} -> FtkAndBoundsDual ftk
    FtkAndBoundsPlain{} -> FtkAndBoundsPlain ftk
    FtkAndBoundsBounds{}
      | FTKScalar @r <- ftk
      , Just Refl <- testEquality (typeRep @r) (typeRep @Int) -> ftkBounds
    FtkAndBoundsBounds{} -> FtkAndBoundsPlain ftk

-- | This fails if the variable had bounds (that would be now lost,
-- unless the new span is the same as old, which is just as irregular).
respanVarName :: forall s s2 y. KnownSpan s2
              => AstVarName '(s, y) -> AstVarName '(s2, y)
respanVarName var@(AstVarName varId ftkBounds) = case ftkBounds of
  FtkAndBoundsBounds{} -> error "respanVarName: bounds lost"
  _ -> mkAstVarName (varNameToFTK var) varId

reboundsVarName :: (Int, Int) -> AstVarName '(PlainSpan, TKScalar Int)
                -> AstVarName '(PlainSpan, TKScalar Int)
reboundsVarName (lb, ub) (AstVarName varId _) =
  mkAstVarNameBounds (lb, ub) varId

varNameToAstVarId :: AstVarName s_y -> AstVarId
varNameToAstVarId (AstVarName varId _) = varId

varNameToSpan :: AstVarName '(s, y) -> SAstSpan s
varNameToSpan (AstVarName _ ftkBounds) = case ftkBounds of
  FtkAndBoundsFull{} -> SFullSpan
  (FtkAndBoundsPrimal _ sspan) -> SPrimalStepSpan sspan
  FtkAndBoundsDual{} -> SDualSpan
  FtkAndBoundsPlain{} -> SPlainSpan
  FtkAndBoundsBounds{} -> SPlainSpan

varNameToFTK :: AstVarName '(s, y) -> FullShapeTK y
varNameToFTK (AstVarName _ ftkBounds) = case ftkBounds of
  (FtkAndBoundsFull ftk) -> ftk
  (FtkAndBoundsPrimal ftk _) -> ftk
  (FtkAndBoundsDual ftk) -> ftk
  (FtkAndBoundsPlain ftk) -> ftk
  FtkAndBoundsBounds{} -> FTKScalar

varNameToBounds :: AstVarName '(s, y) -> Maybe (Int, Int)
varNameToBounds (AstVarName _ (FtkAndBoundsBounds lb ub)) = Just (lb, ub)
varNameToBounds _ = Nothing

-- | The reverse derivative artifact.
type role AstArtifactRev nominal nominal
data AstArtifactRev x z = AstArtifactRev
  { artVarDtRev      :: AstVarName '(FullSpan, ADTensorKind z)
  , artVarDomainRev  :: AstVarName '(FullSpan, x)
  , artDerivativeRev :: AstTensor AstMethodLet FullSpan (ADTensorKind x)
  , artPrimalRev     :: ~(AstTensor AstMethodLet FullSpan z)
      -- rarely used, so not forced
  }
 deriving Show

-- | The forward derivative artifact.
type role AstArtifactFwd nominal nominal
data AstArtifactFwd x z = AstArtifactFwd
  { artVarDsFwd      :: AstVarName '(FullSpan, ADTensorKind x)
  , artVarDomainFwd  :: AstVarName '(FullSpan, x)
  , artDerivativeFwd :: AstTensor AstMethodLet FullSpan (ADTensorKind z)
  , artPrimalFwd     :: ~(AstTensor AstMethodLet FullSpan z)
      -- rarely used, so not forced
  }
 deriving Show

-- | This is the (arbitrarily) chosen representation of terms denoting
-- integers in the indexes of tensor operations.
type AstInt ms = AstTensor ms PlainSpan (TKScalar Int)
-- ~ IntOf (AstTensor ms s)

type IntVarName = AstVarName '(PlainSpan, TKScalar Int)

pattern AstIntVar :: IntVarName -> AstInt ms
pattern AstIntVar var <- AstVar var

-- Data invariant: the var names have bounds of the form (0, k - 1),
-- where the corresponding dimension in sh is k. This is never checked.
type AstVarListS sh = ListS sh IntVarName

-- There's no data invariant here. The shape matches rather the argument
-- of indexing (or gather) than the indexes.
type AstIxS ms sh = IxS sh (AstInt ms)

pattern AstLeqInt :: AstInt ms -> AstInt ms -> AstBool ms
pattern AstLeqInt t u <- (matchAstLeqInt -> Just (t, u))
  where AstLeqInt t u = AstLeqK t u

matchAstLeqInt :: AstBool ms -> Maybe (AstInt ms, AstInt ms)
matchAstLeqInt (AstLeqK @r t u)
  | Just Refl <- testEquality (typeRep @r) (typeRep @Int) =
      Just (t, u)
matchAstLeqInt _ = Nothing

type AstBool ms = AstTensor ms PlainSpan (TKScalar Bool)
-- ~ BoolOf (AstTensor ms s)


-- * AST

type data AstMethodOfSharing = AstMethodShare | AstMethodLet

-- | AST for tensors that are meant to be differentiated.
--
-- Some terms have no semantics, e.g., currently terms with nested primal span.
type role AstTensor nominal nominal nominal
data AstTensor :: AstMethodOfSharing -> AstSpan -> Target where
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
  AstMapAccumLDer
    :: forall accy by ey k ms s.
       SNat k
    -> FullShapeTK by
    -> FullShapeTK ey
    -> AstHFun s
               (TKProduct accy ey) (TKProduct accy by)
    -> AstHFun s
               (TKProduct (ADTensorKind (TKProduct accy ey))
                          (TKProduct accy ey))
               (ADTensorKind (TKProduct accy by))
    -> AstHFun s
               (TKProduct (ADTensorKind (TKProduct accy by))
                          (TKProduct accy ey))
               (ADTensorKind (TKProduct accy ey))
    -> AstTensor ms s accy
    -> AstTensor ms s (BuildTensorKind k ey)
    -> AstTensor ms s (TKProduct accy (BuildTensorKind k by))
  AstApply :: AstHFun s x z -> AstTensor ms s x -> AstTensor ms s z
  AstVar :: AstVarName '(s, y) -> AstTensor ms s y
  AstCond :: forall y ms s.
             AstBool ms -> AstTensor ms s y -> AstTensor ms s y
          -> AstTensor ms s y
  AstBuild1 :: forall y k ms s.
               SNat k -> SingletonTK y
            -> (IntVarName, AstTensor ms s y)
            -> AstTensor ms s (BuildTensorKind k y)

  -- Sharing-related operations, mutually exclusive via AstMethodOfSharing
  AstLet :: forall y z s s2.
            AstVarName '(s, y) -> AstTensor AstMethodLet s y
         -> AstTensor AstMethodLet s2 z
         -> AstTensor AstMethodLet s2 z
  AstShare :: AstVarName '(s, y) -> AstTensor AstMethodShare s y
           -> AstTensor AstMethodShare s y
  AstToShare :: AstTensor AstMethodLet s y
             -> AstTensor AstMethodShare s y

  -- Explicit dual numbers handling, eliminated in interpretation to ADVal
  AstPrimalPart :: forall y s ms. KnownSpan s
                => AstTensor ms s y -> AstTensor ms (PrimalStepSpan s) y
  AstDualPart :: forall y ms.
                 AstTensor ms FullSpan y -> AstTensor ms DualSpan y
  AstPlainPart :: forall y s ms. KnownSpan s
               => AstTensor ms s y -> AstTensor ms PlainSpan y
  AstFromPrimal :: forall y s ms.
                   AstTensor ms (PrimalStepSpan s) y -> AstTensor ms s y
  AstFromDual :: forall y ms.
                 AstTensor ms DualSpan y -> AstTensor ms FullSpan y
  AstFromPlain :: forall y s ms.
                  AstTensor ms PlainSpan y -> AstTensor ms s y

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
  AstR1K :: (NumScalar r, Differentiable r)
         => OpCode1 -> AstTensor ms s (TKScalar r)
         -> AstTensor ms s (TKScalar r)
  AstR2K :: (NumScalar r, Differentiable r)
         => OpCode2 -> AstTensor ms s (TKScalar r)
         -> AstTensor ms s (TKScalar r)
         -> AstTensor ms s (TKScalar r)
  AstI2K :: (NumScalar r, IntegralH r, Nested.IntElt r)
         => OpCodeIntegral2 -> AstTensor ms s (TKScalar r)
         -> AstTensor ms s (TKScalar r)
         -> AstTensor ms s (TKScalar r)
  AstConcreteK :: GoodScalar r
               => r -> AstTensor ms PlainSpan (TKScalar r)
  AstFloorK :: (GoodScalar r1, Differentiable r1, NumScalar r2, Integral r2)
            => AstTensor ms PlainSpan (TKScalar r1)
            -> AstTensor ms PlainSpan (TKScalar r2)
  AstFromIntegralK :: (NumScalar r1, Integral r1, NumScalar r2)
                   => AstTensor ms PlainSpan (TKScalar r1)
                   -> AstTensor ms PlainSpan (TKScalar r2)
  AstCastK :: (NumScalar r1, Differentiable r1, NumScalar r2, Differentiable r2)
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
  AstR1S :: (NumScalar r, Differentiable r)
         => OpCode1 -> AstTensor ms s (TKS sh r)
         -> AstTensor ms s (TKS sh r)
  AstR2S :: (NumScalar r, Differentiable r)
         => OpCode2 -> AstTensor ms s (TKS sh r)
         -> AstTensor ms s (TKS sh r)
         -> AstTensor ms s (TKS sh r)
  AstI2S :: (NumScalar r, IntegralH r, Nested.IntElt r)
         => OpCodeIntegral2 -> AstTensor ms s (TKS sh r)
         -> AstTensor ms s (TKS sh r)
         -> AstTensor ms s (TKS sh r)
  AstConcreteS :: GoodScalar r
               => Nested.Shaped sh r -> AstTensor ms PlainSpan (TKS sh r)
  AstFloorS :: (GoodScalar r1, Differentiable r1, NumScalar r2, Integral r2)
            => AstTensor ms PlainSpan (TKS sh r1)
            -> AstTensor ms PlainSpan (TKS sh r2)
  AstFromIntegralS :: (NumScalar r1, Integral r1, NumScalar r2)
                   => AstTensor ms PlainSpan (TKS sh r1)
                   -> AstTensor ms PlainSpan (TKS sh r2)
  AstCastS :: (NumScalar r1, Differentiable r1, NumScalar r2, Differentiable r2)
           => AstTensor ms s (TKS sh r1)
           -> AstTensor ms s (TKS sh r2)

  -- Shaped tensor operations
  AstIndexS :: forall shm shn x s ms.
               ShS shn
            -> AstTensor ms s (TKS2 (shm ++ shn) x) -> AstIxS ms shm
            -> AstTensor ms s (TKS2 shn x)
    -- out of bounds indexing is permitted and the results is def (==0)
  AstScatterS :: forall shm shn shp x s ms. TKAllNum x
              => ShS shm -> ShS shn -> ShS shp
              -> AstTensor ms s (TKS2 (shm ++ shn) x)
              -> (AstVarListS shm, AstIxS ms shp)
              -> AstTensor ms s (TKS2 (shp ++ shn) x)
    -- out of bounds indexing is permitted and the results is def (==0)
  AstGatherS :: forall shm shn shp x s ms.
                ShS shm -> ShS shn -> ShS shp
             -> AstTensor ms s (TKS2 (shp ++ shn) x)
             -> (AstVarListS shm, AstIxS ms shp)
             -> AstTensor ms s (TKS2 (shm ++ shn) x)
    -- out of bounds indexing is permitted and the results is def (==0)
  AstMinIndexS :: forall n sh r ms. NumScalar r
               => AstTensor ms PlainSpan (TKS (n ': sh) r)
               -> AstTensor ms PlainSpan (TKS (Init (n ': sh)) Int)
  AstMaxIndexS :: forall n sh r ms. NumScalar r
               => AstTensor ms PlainSpan (TKS (n ': sh) r)
               -> AstTensor ms PlainSpan (TKS (Init (n ': sh)) Int)
  AstIotaS :: forall n r ms. NumScalar r
           => SNat n -> AstTensor ms PlainSpan (TKS '[n] r)
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
  AstIndex0S :: forall shm r s ms. GoodScalar r
             => AstTensor ms s (TKS shm r) -> AstIxS ms shm
             -> AstTensor ms s (TKScalar r)
  AstSum0S :: NumScalar r
           => AstTensor ms s (TKS sh r)
           -> AstTensor ms s (TKScalar r)
  AstDot0S :: NumScalar r
           => AstTensor ms s (TKS sh r) -> AstTensor ms s (TKS sh r)
           -> AstTensor ms s (TKScalar r)
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

  -- Booleans
  AstBoolNot :: AstBool ms -> AstBool ms
  AstBoolNotA :: AstTensor ms PlainSpan (TKS sh Bool)
              -> AstTensor ms PlainSpan (TKS sh Bool)
  AstBoolAnd :: AstBool ms -> AstBool ms -> AstBool ms
  AstBoolAndA :: AstTensor ms PlainSpan (TKS sh Bool)
              -> AstTensor ms PlainSpan (TKS sh Bool)
              -> AstTensor ms PlainSpan (TKS sh Bool)
  -- There are existential variables here.
  AstLeqK :: forall r ms. NumScalar r
          => AstTensor ms PlainSpan (TKScalar r)
          -> AstTensor ms PlainSpan (TKScalar r)
          -> AstBool ms
  AstLeqS :: forall sh r ms. NumScalar r
          => AstTensor ms PlainSpan (TKS sh r)
          -> AstTensor ms PlainSpan (TKS sh r)
          -> AstBool ms
  AstLeqA :: forall shb sh r ms. NumScalar r
          => ShS shb -> ShS sh
          -> AstTensor ms PlainSpan (TKS (shb ++ sh) r)
          -> AstTensor ms PlainSpan (TKS (shb ++ sh) r)
          -> AstTensor ms PlainSpan (TKS shb Bool)

deriving instance Show (AstTensor ms s y)
  -- for this to work, AstConcreteS can't take a Concrete;
  -- an alternative might be @Has Show (AstTensor ms s)@, but then we'd need
  -- to write @has@ before we apply @show@ and we'd weaken @AllTargetShow@

type role AstHFun nominal nominal nominal
data AstHFun s x z where
  AstLambda :: ~(AstVarName '(s, x))
            -> ~(AstTensor AstMethodLet s z)
            -> AstHFun s x z
    -- ^ The function body can't have any free variables outside those
    -- listed in the first component of the pair; this reflects
    -- the quantification in 'HordeAd.Core.Ops.rrev'
    -- and prevents "perturbation confusion".
    --
    -- The constructor is non-strict in order not to pre-compute
    -- higher derivatives (e.g., inside folds) that are never going to be used.
    -- As a side effect, all lambdas (closed functions) are processed
    -- lazily, which causes no harm, since they have no outside free variables
    -- and so can't easiliy induce leaks by retaining outside values (e.g.,
    -- big environments from which values for the variables would be drawn).
    -- The cost of computing a reverse derivative of a fold nested inside
    -- the function argument n times is reduced by the laziness from 20^n
    -- to under 2^n (old experimental results). Note, however,
    -- that if the n-th forward and reverse derivative is taken,
    -- the laziness is defeated. To make the variable argument strict
    -- we'd need to modify some other code fragments, while the performance
    -- impact seems mixed.

deriving instance Show (AstHFun s x z)

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
