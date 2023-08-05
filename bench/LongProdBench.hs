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
  defaultMain  -- skips the tiny benchmarks
    [ bgroup1e4 allxs
    , bgroup1e5 allxs
    , bgroup1e6 allxs
    , bgroup1e7 allxs
    , bgroup5e7 allxs
    ]
