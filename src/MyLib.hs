module MyLib (someFunc) where

import Prelude

import AD

someFunc :: IO ()
someFunc = do
  r <- result
  print r
