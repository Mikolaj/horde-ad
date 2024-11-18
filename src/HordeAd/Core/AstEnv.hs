{-# LANGUAGE AllowAmbiguousTypes, QuantifiedConstraints,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | The environment and some helper operations for AST interpretation.
module HordeAd.Core.AstEnv
  ( -- * The environment and operations for extending it
    AstEnv, AstEnvElem(..), emptyEnv, showsPrecAstEnv
  , extendEnv, extendEnvHVector
  , extendEnvD, extendEnvI
    -- * The operations for interpreting bindings
  , interpretLambdaIHVector, interpretLambdaIndex, interpretLambdaIndexS
  , interpretLambdaIndexToIndex, interpretLambdaIndexToIndexS
  , interpretLambdaHsH
    -- * Interpretation of arithmetic, boolean and relation operations
  , interpretAstN1, interpretAstN2, interpretAstR1, interpretAstR2
  , interpretAstR2F
  , interpretAstI2F, interpretAstB2, interpretAstRelOp
  ) where

import Prelude

import Control.Exception.Assert.Sugar
import Data.Dependent.EnumMap.Strict (DEnumMap)
import Data.Dependent.EnumMap.Strict qualified as DMap
import Data.Dependent.Sum
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (Nat)
import Text.Show (showListWith)
import Type.Reflection (typeRep)

import Data.Array.Nested (Rank)

import HordeAd.Core.Ast
import HordeAd.Core.HVector
import HordeAd.Core.HVectorOps
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.Util.ShapedList qualified as ShapedList
import HordeAd.Util.SizedList

-- * The environment and operations for extending it

-- | The environment that keeps variables values during interpretation
type AstEnv target = DEnumMap (AstVarName FullSpan) (AstEnvElem target)
  -- the FullSpan is a lie

type role AstEnvElem nominal nominal
data AstEnvElem (target :: Target) (y :: TensorKindType) where
  AstEnvElemRep :: target y -> AstEnvElem target y

deriving instance Show (target y) => Show (AstEnvElem target y)

emptyEnv :: AstEnv target
emptyEnv = DMap.empty

showsPrecAstEnv
  :: (forall y. TensorKind y => Show (target y))
  => Int -> AstEnv target -> ShowS
showsPrecAstEnv d demap =
  showParen (d > 10) $
    showString "fromList "
    . showListWith
        (\(k :=> target) ->
          case tensorKindFromAstVarName k of
            Dict -> showsPrec 2 k . showString " :=> " . showsPrec 1 target)
        (DMap.toList demap)

-- An informal invariant: if s is FullSpan, target is dual numbers,
-- and if s is PrimalSpan, target is their primal part.
-- The same for all functions below.
extendEnv :: forall target s y. TensorKind y
          => AstVarName s y -> target y -> AstEnv target
          -> AstEnv target
extendEnv var !t !env =
  let var2 :: AstVarName FullSpan y
      var2 = mkAstVarName (varNameToAstVarId var)
        -- to uphold the lie about FullSpan
  in DMap.insertWithKey (\_ _ _ -> error $ "extendEnv: duplicate " ++ show var)
                        var2 (AstEnvElemRep t) env

extendEnvHVector :: forall target. ADReady target
                 => [AstDynamicVarName] -> HVector target -> AstEnv target
                 -> AstEnv target
extendEnvHVector vars !pars !env = assert (length vars == V.length pars) $
  foldr extendEnvD env $ zip vars (V.toList pars)

extendEnvD :: forall target. ADReady target
           => (AstDynamicVarName, DynamicTensor target)
           -> AstEnv target
           -> AstEnv target
extendEnvD vd@(AstDynamicVarName @ty @r @sh varId, d) !env = case d of
  DynamicRanked @r3 @n3 u
    | Just Refl <- testEquality (typeRep @ty) (typeRep @Nat)
    , Just Refl <- matchingRank @sh @n3
    , Just Refl <- testEquality (typeRep @r) (typeRep @r3) ->
      extendEnv @_ @_ @(TKR n3 r) (mkAstVarName varId) u env
  DynamicShaped @r3 @sh3 u
    | Just Refl <- testEquality (typeRep @ty) (typeRep @[Nat])
    , Just Refl <- sameShape @sh3 @sh
    , Just Refl <- testEquality (typeRep @r) (typeRep @r3) ->
      extendEnv @_ @_ @(TKS sh r) (mkAstVarName varId) u env
  DynamicRankedDummy @r3 @sh3 _ _
    | Just Refl <- testEquality (typeRep @ty) (typeRep @Nat)
    , Just Refl <- sameShape @sh3 @sh
    , Just Refl <- testEquality (typeRep @r) (typeRep @r3) ->
      withListSh (Proxy @sh) $ \sh4 ->
        extendEnv @target @_ @(TKR (Rank sh) r) (mkAstVarName varId) (rzero sh4) env
  DynamicShapedDummy @r3 @sh3 _ _
    | Just Refl <- testEquality (typeRep @ty) (typeRep @[Nat])
    , Just Refl <- sameShape @sh3 @sh
    , Just Refl <- testEquality (typeRep @r) (typeRep @r3) ->
      extendEnv @target @_ @(TKS sh r) (mkAstVarName varId) (srepl 0) env
  _ -> error $ "extendEnvD: impossible type"
               `showFailure`
               ( vd, typeRep @ty, typeRep @r, shapeT @sh
               , scalarDynamic d, shapeDynamic d )

extendEnvI :: BaseTensor target
           => IntVarName -> IntOf target -> AstEnv target
           -> AstEnv target
extendEnvI var !i !env = extendEnv var (sfromPrimal i) env

extendEnvVars :: forall target m. BaseTensor target
              => AstVarList m -> IxROf target m
              -> AstEnv target
              -> AstEnv target
extendEnvVars vars !ix !env =
  let assocs = zip (sizedToList vars) (indexToList ix)
  in foldr (uncurry extendEnvI) env assocs

extendEnvVarsS :: forall target sh. BaseTensor target
               => AstVarListS sh -> IxSOf target sh
               -> AstEnv target
               -> AstEnv target
extendEnvVarsS vars !ix !env =
  let assocs = zip (ShapedList.sizedToList vars)
                   (ShapedList.indexToList ix)
  in foldr (uncurry extendEnvI) env assocs


-- * The operations for interpreting bindings

interpretLambdaIHVector
  :: forall target s ms. BaseTensor target
  => (AstEnv target -> AstTensor ms s TKUntyped -> target TKUntyped)
  -> AstEnv target -> (IntVarName, AstTensor ms s TKUntyped)
  -> IntOf target
  -> target TKUntyped
{-# INLINE interpretLambdaIHVector #-}
interpretLambdaIHVector f !env (!var, !ast) =
  \i -> f (extendEnvI var i env) ast

interpretLambdaIndex
  :: forall target s r m n ms. BaseTensor target
  => (AstEnv target -> AstTensor ms s (TKR n r) -> target (TKR n r))
  -> AstEnv target -> (AstVarList m, AstTensor ms s (TKR n r))
  -> IxROf target m
  -> target (TKR n r)
{-# INLINE interpretLambdaIndex #-}
interpretLambdaIndex f !env (!vars, !ast) =
  \ix -> f (extendEnvVars vars ix env) ast

interpretLambdaIndexS
  :: forall sh sh2 target s r ms. BaseTensor target
  => (AstEnv target -> AstTensor ms s (TKS sh r) -> target (TKS sh r))
  -> AstEnv target -> (AstVarListS sh2, AstTensor ms s (TKS sh r))
  -> IxSOf target sh2
  -> target (TKS sh r)
{-# INLINE interpretLambdaIndexS #-}
interpretLambdaIndexS f !env (!vars, !ast) =
  \ix -> f (extendEnvVarsS vars ix env) ast

interpretLambdaIndexToIndex
  :: forall target m n ms. BaseTensor target
  => (AstEnv target -> AstInt ms -> IntOf target)
  -> AstEnv target -> (AstVarList m, AstIndex ms n)
  -> IxROf target m
  -> IxROf target n
{-# INLINE interpretLambdaIndexToIndex #-}
interpretLambdaIndexToIndex f !env (!vars, !asts) =
  \ix -> f (extendEnvVars vars ix env) <$> asts

interpretLambdaIndexToIndexS
  :: forall target sh sh2 ms. BaseTensor target
  => (AstEnv target -> AstInt ms -> IntOf target)
  -> AstEnv target -> (AstVarListS sh, AstIxS ms sh2)
  -> IxSOf target sh
  -> IxSOf target sh2
{-# INLINE interpretLambdaIndexToIndexS #-}
interpretLambdaIndexToIndexS f !env (!vars, !asts) =
  \ix -> f (extendEnvVarsS vars ix env) <$> asts

interpretLambdaHsH
  :: TensorKind x
  => (forall target z. ADReady target
      => AstEnv target -> AstTensor ms s z
      -> target z)
  -> (AstVarName s x, AstTensor ms s y)
  -> HFun x y
{-# INLINE interpretLambdaHsH #-}
interpretLambdaHsH interpret ~(var, ast) =
  HFun $ \ws -> interpret (extendEnv var ws emptyEnv) ast


-- * Interpretation of arithmetic, boolean and relation operations

-- TODO: when the code again tests with GHC >= 9.6, check whether
-- these INLINEs are still needed (removal causes 10% slowdown ATM).
interpretAstN1 :: Num a
               => OpCodeNum1 -> a -> a
{-# INLINE interpretAstN1 #-}
interpretAstN1 NegateOp u = negate u
interpretAstN1 AbsOp u = abs u
interpretAstN1 SignumOp u = signum u

interpretAstN2 :: Num a
               => OpCodeNum2 -> a -> a -> a
{-# INLINE interpretAstN2 #-}
interpretAstN2 MinusOp u v = u - v
interpretAstN2 TimesOp u v = u * v

interpretAstR1 :: Floating a
               => OpCode1 -> a -> a
{-# INLINE interpretAstR1 #-}
interpretAstR1 RecipOp u = recip u
interpretAstR1 ExpOp u = exp u
interpretAstR1 LogOp u = log u
interpretAstR1 SqrtOp u = sqrt u
interpretAstR1 SinOp u = sin u
interpretAstR1 CosOp u = cos u
interpretAstR1 TanOp u = tan u
interpretAstR1 AsinOp u = asin u
interpretAstR1 AcosOp u = acos u
interpretAstR1 AtanOp u = atan u
interpretAstR1 SinhOp u = sinh u
interpretAstR1 CoshOp u = cosh u
interpretAstR1 TanhOp u = tanh u
interpretAstR1 AsinhOp u = asinh u
interpretAstR1 AcoshOp u = acosh u
interpretAstR1 AtanhOp u = atanh u

interpretAstR2 :: RealFloatF a
               => OpCode2 -> a -> a -> a
{-# INLINE interpretAstR2 #-}
interpretAstR2 DivideOp u v = u / v
interpretAstR2 PowerOp u v = u ** v
interpretAstR2 LogBaseOp u v = logBase u v
interpretAstR2 Atan2Op u v = atan2F u v

interpretAstR2F :: RealFloatF a
                => OpCode2 -> a -> a -> a
{-# INLINE interpretAstR2F #-}
interpretAstR2F DivideOp u v = u / v
interpretAstR2F PowerOp u v = u ** v
interpretAstR2F LogBaseOp u v = logBase u v
interpretAstR2F Atan2Op u v = atan2F u v

interpretAstI2F :: IntegralF a
                => OpCodeIntegral2 -> a -> a -> a
{-# INLINE interpretAstI2F #-}
interpretAstI2F QuotOp u v = quotF u v
interpretAstI2F RemOp u v = remF u v

interpretAstB2 :: Boolean b
               => OpCodeBool -> b -> b -> b
{-# INLINE interpretAstB2 #-}
interpretAstB2 AndOp u v = u &&* v
interpretAstB2 OrOp u v = u ||* v

interpretAstRelOp :: (EqF f, OrdF f, TensorKind y)
                  => OpCodeRel -> f y -> f y -> BoolOf f
{-# INLINE interpretAstRelOp #-}
interpretAstRelOp EqOp u v = u ==. v
interpretAstRelOp NeqOp u v = u /=. v
interpretAstRelOp LeqOp u v = u <=. v
interpretAstRelOp GeqOp u v = u >=. v
interpretAstRelOp LsOp u v = u <. v
interpretAstRelOp GtOp u v = u >. v
