-- | Testing harness that differentiates a single objective function using
-- over a twenty different pipeline variants and compares the results.
module CrossTesting
  ( revShort, t48
  ) where

import Prelude

import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import           Data.Bifunctor.Flip
import qualified Data.EnumMap.Strict as EM
import           Numeric.LinearAlgebra (Numeric)

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

-- moving this to TestHighRankSimplified resolves the problem
revShort :: forall r v a.
        ( GoodScalar r
        , v ~ Flip OR.Array r 9, a ~ Flip OR.Array r 7 )
     => (forall f. ADReady f => f r 7 -> f r 9)
     -> a
     -> v
revShort f vals =
  let parameters = toDomains vals
      dt = Nothing
      h :: ADReady f1
        => (f1 r 9 -> AstRanked PrimalSpan r 9)
        -> (AstRanked PrimalSpan r 7 -> f1 r 7)
        -> (AstRanked PrimalSpan r 9 -> AstRanked PrimalSpan r 9)
        -> Domains (ADValClown OD.Array)
        -> ADVal (Flip OR.Array) r 9
      h fx1 fx2 gx inputs =
        let (var, ast) = funToAstR (tshape vals) (fx1 . f . fx2)
            env = extendEnvR var (parseDomains vals inputs) EM.empty
        in interpretAst env (gx ast)
      (_, value2) =
        crevOnDomains dt (h id id id) parameters
  in value2

t48 :: (Numeric r, Fractional r) => Flip OR.Array r 7
t48 = Flip $ OR.fromList [3, 1, 2, 2, 1, 2, 2] [18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001, 5, 2, 6, 1, -2, 0.92, 0.1, -0.2, 13.1, 9, 8, -4, 34, 2.99432, -33, 26, 2, 2, 2, 2, -0.2,-0.2,-0.2,-0.2,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003]
