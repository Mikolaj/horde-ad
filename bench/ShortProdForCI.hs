module Main (main) where

import Prelude

import Control.DeepSeq
import Criterion.Main
import System.Random

import BenchProdTools

allxs :: [Double]
allxs = let xs = map (+ 0.55) $ randoms (mkStdGen 42)
        in deepseq (take 50000000 xs) xs

main :: IO ()
main =
  defaultMain
    [ bgroup100 allxs
    , bgroup1000 allxs
    ]
