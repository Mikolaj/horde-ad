module Main (main) where

import Prelude

import Criterion.Main

import qualified ProdAdTools
import qualified ProdBackpropTools
import qualified ProdManualTools
import qualified ProdMostlyHarmlessTools

main :: IO ()
main = defaultMain
  [ bgroup "1000"
      [ bgroup "manual"
          [ ProdManualTools.bgroup1000
          ]
      , bgroup "ours"
          [ ProdMostlyHarmlessTools.bgroup1000
          ]
      , bgroup "ad"
          [ ProdAdTools.bgroup1000
          ]
      , bgroup "backprop"
          [ ProdBackpropTools.bgroup1000
          ]
      ]
  , bgroup "1e6"
      [ bgroup "manual"
          [ ProdManualTools.bgroup1e6
          ]
      , bgroup "ours"
          [ ProdMostlyHarmlessTools.bgroup1e6
          ]
      , bgroup "ad"
          [ ProdAdTools.bgroup1e6
          ]
      , bgroup "backprop"
          [ ProdBackpropTools.bgroup1e6
          ]
      ]
  , bgroup "5e7"
      [ bgroup "manual"
          [ ProdManualTools.bgroupHalf1e8
          ]
      , bgroup "ours"
          [ ProdMostlyHarmlessTools.bgroupHalf1e8
          ]
      , bgroup "ad"
          [ ProdAdTools.bgroupHalf1e8
          ]
      , bgroup "backprop"
          [ ProdBackpropTools.bgroupHalf1e8
          ]
      ]
  ]
