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

-- * moving this to TestHighRankSimplified resolves the problem
-- * replacing 'r' with 'Double' resolves the problem
-- * with profiling on (cabal test simplifiedOnlyTest --enable-optimization -w ~/r/ghc.head/_build/stage1/bin/ghc --constraint="ghc-typelits-knownnat==0.7.10" --constraint="ghc-typelits-natnormalise==0.7.9" --test-options='+RTS -xc' --ghc-options=-fprof-auto-calls --enable-profiling) the test fails both with and without -fspecialise-aggressively, but no stack trace is printed in either case and that's because we get `Segmentation fault (core dumped)`; the same without `--ghc-options=-fprof-auto-calls`
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
