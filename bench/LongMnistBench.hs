module Main (main) where

import Prelude

import Criterion.Main

import BenchMnistTools

main :: IO ()
main = defaultMain
         [ mnistBGroup1VTA 400
         , mnistBGroup1VTO 400
         , mnistBGroup2VTA 400
         , mnistBGroup2VTC 400
         , mnistBGroup2VTO 400
         ]
