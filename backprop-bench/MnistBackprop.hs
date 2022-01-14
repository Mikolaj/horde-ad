{-# LANGUAGE DataKinds #-}
module Main (main) where

import Prelude

import           Criterion.Main
import           Data.Char
import qualified Data.Vector as V
import           Numeric.LinearAlgebra.Static
import qualified System.Random.MWC as MWC

import MnistBackpropTools

main :: IO ()
main = do
  g <- MWC.initialize
       . V.fromList
       . map (fromIntegral . ord)
       $ "hello world"
  test0 <- MWC.uniformR @(R 784, R 10) ((0,0),(1,1)) g
  defaultMain
     [ bgroup "1"
        [backpropBgroup [test0] 1]
     , bgroup "5"
        [backpropBgroup (replicate 5 test0) 5]
     , bgroup "50"
        [backpropBgroup (replicate 50 test0) 50]
     ]
