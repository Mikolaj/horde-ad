{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
module Main where

import Data.Array.Nested


arr :: Ranked 2 (Shaped [2, 3] (Double, Int))
arr = rgenerate (3 :$: 4 :$: ZSR) $ \(i :.: j :.: ZIR) ->
        sgenerate (SNat @2 :$$ SNat @3 :$$ ZSS) $ \(k :.$ l :.$ ZIS) ->
          let s = 24*i + 6*j + 3*k + l
          in (fromIntegral s, s)

foo :: (Double, Int)
foo = arr `rindex` (2 :.: 1 :.: ZIR) `sindex` (1 :.$ 1 :.$ ZIS)

bad :: Ranked 2 (Ranked 1 Double)
bad = rgenerate (3 :$: 4 :$: ZSR) $ \(i :.: j :.: ZIR) ->
        rgenerate (i :$: ZSR) $ \(k :.: ZIR) ->
          let s = 24*i + 6*j + 3*k
          in fromIntegral s

main :: IO ()
main = do
  print arr
  print foo
  print (rtranspose [1,0] arr)
  -- print bad
