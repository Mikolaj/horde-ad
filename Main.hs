{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -fspecialise-aggressively #-}
-- | Assorted mostly high rank tensor tests.
module Main (main) where

import Prelude

import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import           Data.Bifunctor.Flip
import qualified Data.EnumMap.Strict as EM

import HordeAd
import HordeAd.Core.Adaptor
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId
import HordeAd.Core.TensorADVal

t48 :: Flip OR.Array Double 15
t48 = Flip $ OR.fromList [3, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2] [18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001, 5, 2, 6, 1, -2, 0.92, 0.1, -0.2, 13.1, 9, 8, -4, 34, 2.99432, -33, 26, 2, 2, 2, 2, -0.2,-0.2,-0.2,-0.2,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003]

-- * with profiling on (cabal test simplifiedOnlyTest --enable-optimization -w ~/r/ghc.head/_build/stage1/bin/ghc --constraint="ghc-typelits-knownnat==0.7.10" --constraint="ghc-typelits-natnormalise==0.7.9" --test-options='+RTS -xc' --ghc-options=-fprof-auto-calls --enable-profiling) the test fails both with and without -fspecialise-aggressively, but no stack trace is printed in either case and that's because we get `Segmentation fault (core dumped)`; the same without `--ghc-options=-fprof-auto-calls`
revShort ::
     (AstRanked PrimalSpan Double 15 -> AstRanked PrimalSpan Double 17)
     -> Flip OR.Array Double 15
     -> Flip OR.Array Double 17
revShort f vals =
  let parameters = toDomains vals
      dt = Nothing
      h :: Domains (ADValClown OD.Array) -> ADVal (Flip OR.Array) Double 17
      h inputs =
        let (var, ast) = funToAstR (tshape vals) f
            env = extendEnvR var (parseDomains vals inputs) EM.empty
        in interpretAst env ast
      (_, value2) = crevOnDomains dt h parameters
  in value2

concatBuild2 :: AstRanked PrimalSpan Double 15 -> AstRanked PrimalSpan Double 17
concatBuild2 r =
  tbuild1 5 (\i ->
    tbuild1 2 (\j -> tmap0N (* tfromIndex0 (maxF j (i `quot` (j + 1)))) r))

main :: IO ()
main = print $ revShort concatBuild2 t48
