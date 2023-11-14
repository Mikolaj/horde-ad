-- | Testing harness that differentiates a single objective function using
-- over a twenty different pipeline variants and compares the results.
module CrossTesting
  ( revShort
  ) where

import Prelude

import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import           Data.Bifunctor.Flip
import qualified Data.EnumMap.Strict as EM

import HordeAd.Core.Adaptor
import HordeAd.Core.Ast
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstInterpret
import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.TensorADVal
import HordeAd.Core.TensorClass
import HordeAd.Core.Types

revShort :: forall r. GoodScalar r
     => (AstRanked PrimalSpan r 15 -> AstRanked PrimalSpan r 17)
     -> Flip OR.Array r 15
     -> Flip OR.Array r 17
revShort f vals =
  let parameters = toDomains vals
      dt = Nothing
      h :: Domains (ADValClown OD.Array) -> ADVal (Flip OR.Array) r 17
      h inputs =
        let (var, ast) = funToAstR (tshape vals) f
            env = extendEnvR var (parseDomains vals inputs) EM.empty
        in interpretAst env ast
      (_, value2) = crevOnDomains dt h parameters
  in value2
