{-# LANGUAGE AllowAmbiguousTypes, QuantifiedConstraints,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | The environment and some helper operations for AST interpretation.
module HordeAd.Core.AstEnv
  ( -- * The environment and operations for extending it
    AstEnv, AstEnvElem(..), emptyEnv, showsPrecAstEnv
  , extendEnv, extendEnvHVector, extendEnvHFun
  , extendEnvD, extendEnvI
    -- * The operations for interpreting bindings
  , interpretLambdaI, interpretLambdaIS, interpretLambdaIHVector
  , interpretLambdaIndex, interpretLambdaIndexS
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
import HordeAd.Internal.OrthotopeOrphanInstances
  (IntegralF (..), RealFloatF (..))
import HordeAd.Util.ShapedList (IndexSh)
import HordeAd.Util.ShapedList qualified as ShapedList
import HordeAd.Util.SizedList

-- * The environment and operations for extending it

-- | The environment that keeps variables values during interpretation
type AstEnv ranked = DEnumMap (AstVarName FullSpan) (AstEnvElem ranked)
  -- the FullSpan is a lie

type role AstEnvElem nominal nominal
data AstEnvElem (ranked :: RankedTensorType) (y :: TensorKindType) where
  AstEnvElemRep :: RepN ranked y -> AstEnvElem ranked y
  AstEnvElemHFun :: forall ranked x y. TensorKind x
                 => HFunOf ranked x y -> AstEnvElem ranked y
    -- the "y" is a lie; it should be "TKFun x y"; BTW, Proxy would not help

deriving instance ( Show (RepN ranked y)
                  , CHFun ranked Show y )
                  => Show (AstEnvElem ranked y)

emptyEnv :: AstEnv ranked
emptyEnv = DMap.empty

showsPrecAstEnv
  :: ( forall y. TensorKind y => Show (RepN ranked y)
     , forall y. CHFun ranked Show y )
  => Int -> AstEnv ranked -> ShowS
showsPrecAstEnv d demap =
  showParen (d > 10) $
    showString "fromList "
    . showListWith
        (\(k :=> target) ->
          case tensorKindFromAstVarName k of
            Dict -> showsPrec 2 k . showString " :=> " . showsPrec 1 target)
        (DMap.toList demap)

-- An informal invariant: if s is FullSpan, ranked is dual numbers,
-- and if s is PrimalSpan, ranked is their primal part.
-- The same for all functions below.
extendEnv :: forall ranked s y. TensorKind y
          => AstVarName s y -> Rep ranked y -> AstEnv ranked
          -> AstEnv ranked
extendEnv var !t !env =
  let var2 :: AstVarName FullSpan y
      var2 = mkAstVarName (varNameToAstVarId var)
        -- to uphold the lie about FullSpan
  in DMap.insertWithKey (\_ _ _ -> error $ "extendEnv: duplicate " ++ show var)
                        var2 (AstEnvElemRep $ RepN t) env

extendEnvHVector :: forall ranked. ADReady ranked
                 => [AstDynamicVarName] -> HVector ranked -> AstEnv ranked
                 -> AstEnv ranked
extendEnvHVector vars !pars !env = assert (length vars == V.length pars) $
  foldr extendEnvD env $ zip vars (V.toList pars)

extendEnvHFun :: forall ranked x y. (TensorKind x, TensorKind y)
              => Proxy x -> Proxy y
              -> AstVarId -> HFunOf ranked x y -> AstEnv ranked
              -> AstEnv ranked
extendEnvHFun _ _ !varId !t !env =
  let var2 :: AstVarName FullSpan y
      var2 = mkAstVarName varId
  in DMap.insertWithKey (\_ _ _ -> error
                                   $ "extendEnvHFun: duplicate " ++ show varId)
                        var2 (AstEnvElemHFun @_ @x t) env

extendEnvD :: forall ranked. ADReady ranked
           => (AstDynamicVarName, DynamicTensor ranked)
           -> AstEnv ranked
           -> AstEnv ranked
extendEnvD vd@(AstDynamicVarName @ty @r @sh varId, d) !env = case d of
  DynamicRanked @r3 @n3 u
    | Just Refl <- testEquality (typeRep @ty) (typeRep @Nat)
    , Just Refl <- matchingRank @sh @n3
    , Just Refl <- testEquality (typeRep @r) (typeRep @r3) ->
      extendEnv @_ @_ @(TKR r n3) (mkAstVarName varId) u env
  DynamicShaped @r3 @sh3 u
    | Just Refl <- testEquality (typeRep @ty) (typeRep @[Nat])
    , Just Refl <- sameShape @sh3 @sh
    , Just Refl <- testEquality (typeRep @r) (typeRep @r3) ->
      extendEnv @_ @_ @(TKS r sh) (mkAstVarName varId) u env
  DynamicRankedDummy @r3 @sh3 _ _
    | Just Refl <- testEquality (typeRep @ty) (typeRep @Nat)
    , Just Refl <- sameShape @sh3 @sh
    , Just Refl <- testEquality (typeRep @r) (typeRep @r3) ->
      withListSh (Proxy @sh) $ \sh4 ->
        extendEnv @ranked @_ @(TKR r (Rank sh)) (mkAstVarName varId) (rzero sh4) env
  DynamicShapedDummy @r3 @sh3 _ _
    | Just Refl <- testEquality (typeRep @ty) (typeRep @[Nat])
    , Just Refl <- sameShape @sh3 @sh
    , Just Refl <- testEquality (typeRep @r) (typeRep @r3) ->
      extendEnv @ranked @_ @(TKS r sh) (mkAstVarName varId) (srepl 0) env
  _ -> error $ "extendEnvD: impossible type"
               `showFailure`
               ( vd, typeRep @ty, typeRep @r, shapeT @sh
               , scalarDynamic d, shapeDynamic d )

extendEnvI :: ( RankedTensor ranked
              , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
           => IntVarName -> IntOf ranked -> AstEnv ranked
           -> AstEnv ranked
extendEnvI var !i !env = extendEnv var (rconstant i) env

extendEnvVars :: forall ranked m.
                 ( RankedTensor ranked
                 , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
              => AstVarList m -> IndexOf ranked m
              -> AstEnv ranked
              -> AstEnv ranked
extendEnvVars vars !ix !env =
  let assocs = zip (sizedToList vars) (indexToList ix)
  in foldr (uncurry extendEnvI) env assocs

extendEnvVarsS :: forall ranked sh.
                  ( RankedTensor ranked
                  , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
               => AstVarListS sh -> IndexSh ranked sh
               -> AstEnv ranked
               -> AstEnv ranked
extendEnvVarsS vars !ix !env =
  let assocs = zip (ShapedList.sizedToList vars)
                   (ShapedList.indexToList ix)
  in foldr (uncurry extendEnvI) env assocs


-- * The operations for interpreting bindings

interpretLambdaI
  :: forall ranked n s r ms.
     (RankedTensor ranked, RankedOf (PrimalOf ranked) ~ PrimalOf ranked)
  => (AstEnv ranked -> AstTensor ms s (TKR r n) -> ranked r n)
  -> AstEnv ranked -> (IntVarName, AstTensor ms s (TKR r n))
  -> IntOf ranked
  -> ranked r n
{-# INLINE interpretLambdaI #-}
interpretLambdaI f !env (!var, !ast) =
  \i -> f (extendEnvI var i env) ast

interpretLambdaIS
  :: forall ranked sh s r ms.
     (RankedTensor ranked, RankedOf (PrimalOf ranked) ~ PrimalOf ranked)
  => (AstEnv ranked -> AstTensor ms s (TKS r sh) -> ShapedOf ranked r sh)
  -> AstEnv ranked -> (IntVarName, AstTensor ms s (TKS r sh))
  -> IntOf ranked
  -> ShapedOf ranked r sh
{-# INLINE interpretLambdaIS #-}
interpretLambdaIS f !env (!var, ast) =
  \i -> f (extendEnvI var i env) ast

interpretLambdaIHVector
  :: forall ranked s ms.
     (RankedTensor ranked, RankedOf (PrimalOf ranked) ~ PrimalOf ranked)
  => (AstEnv ranked -> AstTensor ms s TKUntyped
      -> HVectorPseudoTensor ranked Float '())
  -> AstEnv ranked -> (IntVarName, AstTensor ms s TKUntyped)
  -> IntOf ranked
  -> HVectorOf ranked
{-# INLINE interpretLambdaIHVector #-}
interpretLambdaIHVector f !env (!var, !ast) =
  \i -> unHVectorPseudoTensor $ f (extendEnvI var i env) ast

interpretLambdaIndex
  :: forall ranked s r m n ms.
     (RankedTensor ranked, RankedOf (PrimalOf ranked) ~ PrimalOf ranked)
  => (AstEnv ranked -> AstTensor ms s (TKR r n) -> ranked r n)
  -> AstEnv ranked -> (AstVarList m, AstTensor ms s (TKR r n))
  -> IndexOf ranked m
  -> ranked r n
{-# INLINE interpretLambdaIndex #-}
interpretLambdaIndex f !env (!vars, !ast) =
  \ix -> f (extendEnvVars vars ix env) ast

interpretLambdaIndexS
  :: forall sh sh2 ranked s r ms.
     (RankedTensor ranked, RankedOf (PrimalOf ranked) ~ PrimalOf ranked)
  => (AstEnv ranked -> AstTensor ms s (TKS r sh) -> ShapedOf ranked r sh)
  -> AstEnv ranked -> (AstVarListS sh2, AstTensor ms s (TKS r sh))
  -> IndexSh ranked sh2
  -> ShapedOf ranked r sh
{-# INLINE interpretLambdaIndexS #-}
interpretLambdaIndexS f !env (!vars, !ast) =
  \ix -> f (extendEnvVarsS vars ix env) ast

interpretLambdaIndexToIndex
  :: forall ranked m n ms.
     (RankedTensor ranked, RankedOf (PrimalOf ranked) ~ PrimalOf ranked)
  => (AstEnv ranked -> AstInt ms -> IntOf ranked)
  -> AstEnv ranked -> (AstVarList m, AstIndex ms n)
  -> IndexOf ranked m
  -> IndexOf ranked n
{-# INLINE interpretLambdaIndexToIndex #-}
interpretLambdaIndexToIndex f !env (!vars, !asts) =
  \ix -> f (extendEnvVars vars ix env) <$> asts

interpretLambdaIndexToIndexS
  :: forall ranked sh sh2 ms.
     (RankedTensor ranked, RankedOf (PrimalOf ranked) ~ PrimalOf ranked)
  => (AstEnv ranked -> AstInt ms -> IntOf ranked)
  -> AstEnv ranked -> (AstVarListS sh, AstIndexS ms sh2)
  -> IndexSh ranked sh
  -> IndexSh ranked sh2
{-# INLINE interpretLambdaIndexToIndexS #-}
interpretLambdaIndexToIndexS f !env (!vars, !asts) =
  \ix -> f (extendEnvVarsS vars ix env) <$> asts

interpretLambdaHsH
  :: TensorKind x
  => (forall ranked z. ADReady ranked
      => AstEnv ranked -> AstTensor ms s z
      -> Rep ranked z)
  -> (AstVarName s x, AstTensor ms s y)
  -> HFun x y
{-# INLINE interpretLambdaHsH #-}
interpretLambdaHsH interpret ~(var, ast) =
  HFun $ \Proxy ws -> interpret (extendEnv var ws emptyEnv) ast


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

interpretAstRelOp :: (EqF f, OrdF f, GoodScalar r, HasSingletonDict y)
                  => OpCodeRel -> f r y -> f r y -> BoolOf f
{-# INLINE interpretAstRelOp #-}
interpretAstRelOp EqOp u v = u ==. v
interpretAstRelOp NeqOp u v = u /=. v
interpretAstRelOp LeqOp u v = u <=. v
interpretAstRelOp GeqOp u v = u >=. v
interpretAstRelOp LsOp u v = u <. v
interpretAstRelOp GtOp u v = u >. v
