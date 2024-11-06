module HordeAd.Core.AstInterpret
  ( interpretAst
  ) where

import Prelude

import HordeAd.Core.Ast
import HordeAd.Core.HVector
import HordeAd.Core.TensorClass
import HordeAd.Core.Types

interpretAst
  :: forall target y. BaseTensor target
  => target TKUnit
  -> AstTensor AstMethodLet FullSpan y
  -> target y
interpretAst env = \case
  AstBuildHVector1{} ->
    {- dmkHVector0 $ -} dbuild1 undefined (interpretLambdaIHVector env)

interpretLambdaIHVector
  :: target TKUnit
  -> IntOf target
  -> HVectorOf target
interpretLambdaIHVector = undefined
