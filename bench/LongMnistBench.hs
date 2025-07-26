module Main (main) where

import Prelude

import Criterion.Main

import BenchMnistTools

main :: IO ()
main = defaultMain
         [ mnistBGroup1VTA 400
-- TODO: re-enable when it doesn't take longer than all the others taken together:                  , mnistBGroup1VTO 400
         , mnistBGroup2VTA 400
         , mnistBGroup2VTC 400
         , mnistBGroup2VTO 400
         , mnistBGroup2VTOZ 400
         , mnistBGroup2VTOX 400
         ]
