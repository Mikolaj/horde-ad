{-# LANGUAGE AllowAmbiguousTypes, QuantifiedConstraints,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | The environment and some helper operations for AST interpretation.
module HordeAd.Core.AstEnv
  ( -- * The environment and operations for extending it
    AstEnv, AstEnvElem(..), emptyEnv, showsPrecAstEnv
  , extendEnv, extendEnvI
    -- * The operations for interpreting bindings
  , interpretLambdaIndexToIndexS, interpretLambdaHFun
    -- * Interpretation of arithmetic, boolean and relation operations
  , interpretAstN1, interpretAstN2, interpretAstR1, interpretAstR2
  , interpretAstR2F
  , interpretAstI2F, interpretAstB2, interpretAstRelOp
  ) where

import Prelude

import Data.Dependent.EnumMap.Strict (DEnumMap)
import Data.Dependent.EnumMap.Strict qualified as DMap
import Data.Dependent.Sum
import Data.Foldable qualified as Foldable
import Text.Show (showListWith)

import Data.Array.Nested.Internal.Shape (listsToList)

import HordeAd.Core.Ast
import HordeAd.Core.Ops
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- * The environment and operations for extending it

-- | The environment that keeps variables values during interpretation
type AstEnv target = DEnumMap (AstVarName FullSpan) (AstEnvElem target)
  -- the FullSpan is a lie

type role AstEnvElem nominal nominal
data AstEnvElem (target :: Target) (y :: TensorKindType) where
  AstEnvElem :: target y -> AstEnvElem target y

deriving instance Show (target y) => Show (AstEnvElem target y)

emptyEnv :: AstEnv target
emptyEnv = DMap.empty

showsPrecAstEnv
  :: (forall y. KnownSTK y => Show (target y))
  => Int -> AstEnv target -> ShowS
showsPrecAstEnv d demap =
  showParen (d > 10) $
    showString "fromList "
    . showListWith
        (\(k :=> target) ->
           withKnownSTK (varNameToSTK k) $
           showsPrec 2 k . showString " :=> " . showsPrec 1 target)
        (DMap.toList demap)

-- An informal invariant: if s is FullSpan, target is dual numbers,
-- and if s is PrimalSpan, target is their primal part.
-- The same for all functions below.
extendEnv :: forall target s y.
             AstVarName s y -> target y -> AstEnv target
          -> AstEnv target
extendEnv var !t !env =
  let var2 :: AstVarName FullSpan y
      var2 = mkAstVarName (varNameToSTK var) (varNameToAstVarId var)
        -- to uphold the lie about FullSpan
  in DMap.insertWithKey (\_ _ _ -> error $ "extendEnv: duplicate " ++ show var)
                        var2 (AstEnvElem t) env

extendEnvI :: BaseTensor target
           => IntVarName -> IntOf target -> AstEnv target
           -> AstEnv target
extendEnvI var !i !env = extendEnv var (tfromPrimal STKScalar i) env

extendEnvVarsS :: forall target sh. BaseTensor target
               => AstVarListS sh -> IxSOf target sh
               -> AstEnv target
               -> AstEnv target
extendEnvVarsS vars !ix !env =
  let assocs = zip (listsToList vars) (Foldable.toList ix)
  in foldr (uncurry extendEnvI) env assocs


-- * The operations for interpreting bindings

interpretLambdaIndexToIndexS
  :: forall target sh sh2 ms. BaseTensor target
  => (AstEnv target -> AstInt ms -> IntOf target)
  -> AstEnv target -> (AstVarListS sh, AstIxS ms sh2)
  -> IxSOf target sh
  -> IxSOf target sh2
{-# INLINE interpretLambdaIndexToIndexS #-}
interpretLambdaIndexToIndexS f !env (!vars, !asts) =
  \ix -> f (extendEnvVarsS vars ix env) <$> asts

interpretLambdaHFun
  :: (forall target z. ADReady target
      => AstEnv target -> AstTensor ms s z
      -> target z)
  -> (AstVarName s x, AstTensor ms s y)
  -> HFun x y
{-# INLINE interpretLambdaHFun #-}
interpretLambdaHFun interpret ~(var, ast) =
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

interpretAstRelOp :: (EqF f, OrdF f, KnownSTK y)
                  => OpCodeRel -> f y -> f y -> BoolOf f
{-# INLINE interpretAstRelOp #-}
interpretAstRelOp EqOp u v = u ==. v
interpretAstRelOp NeqOp u v = u /=. v
interpretAstRelOp LeqOp u v = u <=. v
interpretAstRelOp GeqOp u v = u >=. v
interpretAstRelOp LsOp u v = u <. v
interpretAstRelOp GtOp u v = u >. v
