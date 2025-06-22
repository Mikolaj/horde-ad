module Main (main) where

import Prelude

import Control.DeepSeq
import Criterion.Main
import System.Random

import BenchProdTools

allxs :: [Double]
allxs = let xs = map (+ 0.55) $ randoms (mkStdGen 42)
        in deepseq (take 1000000 xs) xs

main :: IO ()
main =
  defaultMain  -- skips the tiny benchmarks
    [ bgroup1e4 allxs
-- TODO: re-enable once https://github.com/Mikolaj/horde-ad/issues/117 fixed
--  , bgroup1e5 allxs
{- heat death of the universe ATM:
    , bgroup1e6 allxs
    , bgroup1e7 allxs
    , bgroup5e7 allxs -}
    ]
