module MyLib (someFunc) where

import Prelude

import AD

someFunc :: IO ()
someFunc = mapM_ print result
