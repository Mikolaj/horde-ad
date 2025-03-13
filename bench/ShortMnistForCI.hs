module Main (main) where

import Prelude

import Criterion.Main

import BenchMnistTools

main :: IO ()
main = defaultMain
         [ mnistBGroup1VTA 40
         , mnistBGroup1VTO 40
         , mnistBGroup2VTA 40
         , mnistBGroup2VTC 40
         , mnistBGroup2VTO 40
         , mnistBGroup2VTOZ 40
         ]
