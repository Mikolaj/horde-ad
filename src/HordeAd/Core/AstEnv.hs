{-# LANGUAGE UndecidableInstances #-}
-- | The environment datatype and operations for creating and accessing it.
module HordeAd.Core.AstEnv
  ( AstEnv, SpanTargetFam, SpanTarget(..)
  , lemPlainOfSpan, dictSpanFam, toFromFullSpan, toFullSpan, fromFullSpan
  , emptyEnv  -- TODO: showsPrecAstEnv
  , extendEnv, extendEnvI, extendEnvVarsS
  ) where

import Prelude

import Data.Dependent.EnumMap.Strict (DEnumMap)
import Data.Dependent.EnumMap.Strict qualified as DMap
import Data.Kind (Type)
import Data.Proxy (Proxy)
import Data.Type.Equality ((:~:) (Refl))

import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types (unsafeCoerceRefl)

import HordeAd.Core.Ast
import HordeAd.Core.Ops
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- | The environment that keeps values assigned to variables
-- during interpretation.
type AstEnv :: Target -> Type
type AstEnv target = DEnumMap AstVarName (SpanTarget target)

type family SpanTargetFam target s :: Target where
--SpanTargetFam target (PrimalStepSpan s2) = SpanTargetFam (PrimalOf target) s2
  SpanTargetFam target (PrimalStepSpan s2) = PrimalOf (SpanTargetFam target s2)
  SpanTargetFam target DualSpan = DualOf target
  SpanTargetFam target FullSpan = target
  SpanTargetFam target PlainSpan = PlainOf target

-- This is needed, because type families can't yet be partially applied.
type role SpanTarget nominal nominal
data SpanTarget :: Target -> (AstSpan, TK) -> Type where
  SpanTarget :: SpanTargetFam target s y -> SpanTarget target '(s, y)

lemPlainOfSpan :: ADReady target
               => Proxy target -> SAstSpan s
               -> PlainOf (SpanTargetFam target s) :~: PlainOf target
{-# INLINE lemPlainOfSpan #-}
lemPlainOfSpan _ = \case
  SFullSpan -> Refl
  SPrimalStepSpan SFullSpan -> Refl
  -- This is true morally and in all instances, even though it's
  -- not derivable.
  SPrimalStepSpan _ -> unsafeCoerceRefl
  SDualSpan -> unsafeCoerceRefl  -- illegal and zero anyway; TODO
  SPlainSpan -> Refl

dictSpanFam :: ADReady target
            => Proxy target -> SAstSpan s
            -> Dict0 (ADReadyClasses (SpanTargetFam target s))
{-# INLINE dictSpanFam #-}
dictSpanFam _ = \case
  SFullSpan -> Dict0
  SPrimalStepSpan SFullSpan -> Dict0
  SPrimalStepSpan _ ->
    error "dictSpanFam: these operations on nested primal terms are illegal"
  SDualSpan ->
    error "dictSpanFam: these operations on DualSpan terms are illegal"
  SPlainSpan -> Dict0

toFromFullSpan
  :: BaseTensor target
  => SingletonTK y -> SAstSpan s
  -> ( SpanTargetFam target s y -> SpanTargetFam target FullSpan y
     , SpanTargetFam target FullSpan y -> SpanTargetFam target s y )
{-# INLINE toFromFullSpan #-}
toFromFullSpan stk = \case
  SFullSpan -> (id, id)
  SPrimalStepSpan SFullSpan -> (tfromPrimal stk, tprimalPart)
  SPrimalStepSpan _ ->
    error "toFromFullSpan: nested primal numbers are not converted to full dual numbers"
  {- This would require an arbitrarily large number of dictionaries
     for PrimalOf (PrimalOf (... (PrimalOf target)))
     or equating the type of primal numbers and dual numbers with
     a zero dual part, after a finite number of steps, which is troublesome,
     or at step zero, which is crude and gives too few typing hints.
  SPrimalStepSpan s4 ->
    let (toFull, fromFull) = toFromFull stk s4
    in (toFull . tfromPrimal stk, tprimalPart . fromFull)
  -}
  SDualSpan ->
    error "toFromFullSpan: can't convert a dual part to a full dual number"
  SPlainSpan -> (tfromPlain stk, tplainPart)

toFullSpan :: BaseTensor target
           => SingletonTK y -> SAstSpan s
           -> SpanTargetFam target s y -> SpanTargetFam target FullSpan y
{-# INLINE toFullSpan #-}
toFullSpan stk = \case
  SFullSpan -> id
  SPrimalStepSpan SFullSpan -> tfromPrimal stk
  SPrimalStepSpan _ ->
    error "toFullSpan: nested primal numbers are not converted to full dual numbers"
  SDualSpan ->
    error "toFullSpan: can't convert a dual part to a full dual number"
  SPlainSpan -> tfromPlain stk

fromFullSpan :: BaseTensor target
             => SAstSpan s
             -> SpanTargetFam target FullSpan y -> SpanTargetFam target s y
{-# INLINE fromFullSpan #-}
fromFullSpan = \case
  SFullSpan -> id
  SPrimalStepSpan SFullSpan -> tprimalPart
  SPrimalStepSpan _ ->
    error "fromFullSpan: nested primal numbers are not converted to full dual numbers"
  SDualSpan ->
    error "fromFullSpan: can't convert a dual part to a full dual number"
  SPlainSpan -> tplainPart

emptyEnv :: AstEnv target
emptyEnv = DMap.empty

{- TODO:
showsPrecAstEnv
  :: AllTargetShow target
  => Int -> AstEnv target -> ShowS
showsPrecAstEnv d demap =
  showParen (d > 10) $
    showString "fromList "
    . showListWith
        (\(k :=> SpanTarget target) ->
           withKnownSTK (ftkToSTK $ varNameToFTK k) $
           showsPrec 2 k . showString " :=> " . showsPrec 1 target)
        (DMap.toList demap)
-}

extendEnv :: forall target s y.
             AstVarName '(s, y) -> SpanTargetFam target s y -> AstEnv target
          -> AstEnv target
extendEnv !var !t !env =
  if DMap.member var env
  then error $ "extendEnv: duplicate " ++ show var
  else DMap.insert var (SpanTarget t) env

extendEnvI :: IntVarName -> IntOf target -> AstEnv target
           -> AstEnv target
extendEnvI !var !i !env = extendEnv var i env

extendEnvVarsS :: forall target sh.
                  AstVarListS sh -> IxSOf target sh -> AstEnv target
               -> AstEnv target
extendEnvVarsS ZS ZIS !env = env
extendEnvVarsS (var ::$ vars) (i :.$ ix) env =
  extendEnvVarsS vars ix (extendEnvI var i env)
