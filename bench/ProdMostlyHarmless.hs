module Main (main) where

import Prelude

import Criterion.Main

import ProdMostlyHarmlessTools

main :: IO ()
main =
  defaultMain
    [ bgroup100
    , bgroup200
    , bgroup1000
    , bgroup1e4
    , bgroup1e5
    , bgroup1e6
    , bgroup1e7
    , bgroup5e7
    ]
