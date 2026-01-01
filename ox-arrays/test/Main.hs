{-# LANGUAGE ImportQualifiedPost #-}
module Main where

import Test.Tasty

import Tests.C qualified
import Tests.Permutation qualified


main :: IO ()
main = defaultMain $
  testGroup "Tests"
    [Tests.C.tests
    ,Tests.Permutation.tests
    ]
