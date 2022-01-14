module Main (main) where

import Prelude

import Criterion.Main

import qualified ProdAdTools
import qualified ProdBackpropTools
import qualified ProdManualTools
import qualified ProdMostlyHarmlessTools

main :: IO ()
main =
  defaultMain
    [ ProdManualTools.bgroup1000
    , ProdManualTools.bgroup1e6
    , ProdManualTools.bgroupHalf1e8
    , ProdMostlyHarmlessTools.bgroup1000
    , ProdMostlyHarmlessTools.bgroup1e6
    , ProdMostlyHarmlessTools.bgroupHalf1e8
    , ProdAdTools.bgroup1000
    , ProdAdTools.bgroup1e6
    , ProdAdTools.bgroupHalf1e8
    , ProdBackpropTools.bgroup1000
    , ProdBackpropTools.bgroup1e6
    , ProdBackpropTools.bgroupHalf1e8
    ]
