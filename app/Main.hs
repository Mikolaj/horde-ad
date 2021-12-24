module Main (main) where

import Prelude

import qualified MyLib (someFunc)

main :: IO ()
main = MyLib.someFunc
