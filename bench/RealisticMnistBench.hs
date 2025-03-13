module Main (main) where

import Prelude

import Criterion.Main
import System.Random

import MnistData

import BenchMnistTools

main :: IO ()
main = do
  defaultMain
    [ mnistBGroup1VTA 4000
    , mnistBGroup1VTO 4000
    , mnistBGroup2VTA 4000
    , mnistBGroup2VTC 4000
    , mnistBGroup2VTO 4000
    ]
