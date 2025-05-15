{-# LANGUAGE QuantifiedConstraints #-}
-- | The environment datatype and operations for creating and accessing it.
module HordeAd.Core.AstEnv
  ( AstEnv, emptyEnv, showsPrecAstEnv
  , extendEnv, extendEnvI, extendEnvVarsS
  ) where

import Prelude

import Data.Coerce (coerce)
import Data.Dependent.EnumMap.Strict (DEnumMap)
import Data.Dependent.EnumMap.Strict qualified as DMap
import Data.Dependent.Sum
import Data.Foldable qualified as Foldable
import Data.Kind (Type)
import Text.Show (showListWith)

import Data.Array.Nested.Shaped.Shape

import HordeAd.Core.Ast
import HordeAd.Core.Ops
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- | The environment that keeps values assigned to variables
-- during interpretation.
type AstEnv :: Target -> Type
type AstEnv target = DEnumMap (AstVarName FullSpan) target
  -- We can't easily index over span and tensor kind at once,
  -- so instead we represent PrimalSpan values as FullSpan
  -- (dual number) values with zero dual component and DualSpan values
  -- as FullSpan values with zero primal component.

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
           withKnownSTK (ftkToSTK $ varNameToFTK k) $
           showsPrec 2 k . showString " :=> " . showsPrec 1 target)
        (DMap.toList demap)

extendEnv :: forall target s y.
             AstVarName s y -> target y -> AstEnv target
          -> AstEnv target
extendEnv var !t !env =
  let var2 :: AstVarName FullSpan y
      var2 = coerce var  -- only FullSpan variables permitted in env; see above
  in DMap.insertWithKey (\_ _ _ -> error $ "extendEnv: duplicate " ++ show var)
                        var2 t env

extendEnvI :: BaseTensor target
           => IntVarName -> IntOf target -> AstEnv target
           -> AstEnv target
extendEnvI var !i !env = extendEnv var (tfromPrimal STKScalar i) env

extendEnvVarsS :: forall target sh. BaseTensor target
               => AstVarListS sh -> IxSOf target sh -> AstEnv target
               -> AstEnv target
extendEnvVarsS vars !ix !env =
  let assocs = zip (listsToList vars) (Foldable.toList ix)
  in foldr (uncurry extendEnvI) env assocs
