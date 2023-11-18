{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -ddump-prep -dsuppress-all #-}
{-# OPTIONS_GHC -fspecialise-aggressively #-}
-- | Assorted mostly high rank tensor tests.
module Main (main) where

import Prelude

import qualified Data.Array.RankedS as OR
import           Data.Bifunctor.Flip
import qualified Data.EnumMap.Strict as EM

import HordeAd
import HordeAd.Core.Adaptor
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId

import Debug.Trace

t48 :: Flip OR.Array Double 75
t48 = Flip $ OR.fromList [3, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] [18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001, 5, 2, 6, 1, -2, 0.92, 0.1, -0.2, 13.1, 9, 8, -4, 34, 2.99432, -33, 26, 2, 2, 2, 2, -0.2,-0.2,-0.2,-0.2,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003]

revShort ::
     (AstRanked PrimalSpan Double 75 -> AstRanked PrimalSpan Double 77)
     -> Flip OR.Array Double 75
     -> ADVal (Flip OR.Array) Double 77
revShort f vals =
  let !parameters = toDomains vals in
  let !deltaInputs = traceShow ("parameters", parameters) $ generateDeltaInputsOD parameters in
  let !inputs = traceShow ("deltaInputs", deltaInputs) $ makeADInputs parameters deltaInputs in
  let !(!var, !ast) = traceShow ("inputs", inputs) $ funToAstR (tshape vals) f in
  let !env = traceShow ("var", var) $ traceShow ("ast", ast) $ extendEnvR var (parseDomains vals inputs) EM.empty in
  let adval :: ADVal (Flip OR.Array) Double 77
      !adval = traceShow ("env", env) $ interpretAst env ast
  in adval

concatBuild2 :: AstRanked PrimalSpan Double 75 -> AstRanked PrimalSpan Double 77
concatBuild2 r =
  tbuild1 5 (\i ->
    tbuild1 2 (\j -> tmap0N (* tfromIndex0 (maxF j (i `quot` (j + 1)))) r))

main :: IO ()
main = print $ revShort concatBuild2 t48
