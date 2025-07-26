module Main (main) where

import Prelude

import Criterion.Main
import System.Random

import MnistData

import BenchMnistTools

main :: IO ()
main = defaultMain
         [ mnistBGroup1VTA 4000
-- TODO: re-enable when it doesn't take longer than all the others taken together:         , mnistBGroup1VTO 4000
         , mnistBGroup2VTA 4000
         , mnistBGroup2VTC 4000
         , mnistBGroup2VTO 4000
         , mnistBGroup2VTOZ 4000
         , mnistBGroup2VTOX 4000
         ]
