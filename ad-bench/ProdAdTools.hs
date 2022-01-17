{-# OPTIONS_GHC -Wno-missing-export-lists #-}
module ProdAdTools where

import Prelude

import           Criterion.Main
import qualified Data.Vector
import qualified Data.Vector.Generic as V

import Numeric.AD.Mode.Reverse.Double hiding (diff)

bgroup100, bgroup200, bgroup1000, bgroup1e4, bgroup1e5, bgroup1e6, bgroup1e7, bgroup5e7 :: [Double] -> Benchmark

bgroup100 allxs =
      env (return (take 100 allxs, V.fromList $ take 100 allxs)) $
      \ ~(list, vec) ->
      bgroup "100"
        [ bench "func" $ nf prod list
        , bench "grad" $ nf grad_prod list
        , bench "func_vec" $ nf vec_prod vec
        , bench "grad_vec" $ nf grad_vec_prod vec
        ]

bgroup200 allxs =
      env (return (take 200 allxs, V.fromList $ take 200 allxs)) $
      \ ~(list, vec) ->
      bgroup "200"
        [ bench "func" $ nf prod list
        , bench "grad" $ nf grad_prod list
        , bench "func_vec" $ nf vec_prod vec
        , bench "grad_vec" $ nf grad_vec_prod vec
        ]

bgroup1000 allxs =
      env (return (take 1000 allxs, V.fromList $ take 1000 allxs)) $
      \ ~(list, vec) ->
      bgroup "1000"
        [ bench "func" $ nf prod list
        , bench "grad" $ nf grad_prod list
        , bench "func_vec" $ nf vec_prod vec
        , bench "grad_vec" $ nf grad_vec_prod vec
        ]

bgroup1e4 allxs =
      env (return (take 10000 allxs, V.fromList $ take 10000 allxs)) $
      \ ~(list, vec) ->
      bgroup "1e4"
        [ bench "func" $ nf prod list
        , bench "grad" $ nf grad_prod list
        , bench "func_vec" $ nf vec_prod vec
        , bench "grad_vec" $ nf grad_vec_prod vec
        ]

bgroup1e5 allxs =
      env (return (take 100000 allxs, V.fromList $ take 100000 allxs)) $
      \ ~(list, vec) ->
      bgroup "1e5"
        [ bench "func" $ nf prod list
        , bench "grad" $ nf grad_prod list
        , bench "func_vec" $ nf vec_prod vec
        , bench "grad_vec" $ nf grad_vec_prod vec
        ]

bgroup1e6 allxs =
     env (return (take 1000000 allxs, V.fromList $ take 1000000 allxs)) $
      \ ~(list, vec) ->
      bgroup "1e6"
        [ bench "func" $ nf prod list
        , bench "grad" $ nf grad_prod list
        , bench "func_vec" $ nf vec_prod vec
        , bench "grad_vec" $ nf grad_vec_prod vec
        ]

bgroup1e7 allxs =
      env (return (take 10000000 allxs, V.fromList $ take 10000000 allxs)) $
      \ ~(list, vec) ->
      bgroup "1e7"
        [ bench "func" $ nf prod list
        , bench "grad" $ nf grad_prod list
        , bench "func_vec" $ nf vec_prod vec
        , bench "grad_vec" $ nf grad_vec_prod vec
        ]

bgroup5e7 allxs =
      env (return $ take 50000000 allxs) $
      \ list ->
      bgroup "5e7"  -- 5e7 == 5 * 10^7 == 0.5 * 10^8 == 0.5e8
        [ bench "func" $ nf prod list
        , bench "grad" $ nf grad_prod list
-- this already takes 20G with 'ffi' flag, so the worse variants not attempted:
--        , bench "func_vec" $ nf vec_prod vec
--        , bench "grad_vec" $ nf grad_vec_prod vec
        ]

prod :: Num r => [r] -> r
prod [x] = x
prod (x : xs) = x * prod xs

grad_prod :: [Double] -> [Double]
grad_prod = grad prod

-- This benchmark shows that there is slowdown from using vectors
-- with the ad library. The Traversable data structure is probably
-- converted to a list ASAP. Conversion of lists to lists is free,
-- so that's probably the best structure to use.
vec_prod :: forall r. Num r
         => Data.Vector.Vector r -> r
vec_prod = V.foldl1' (*)

grad_vec_prod :: Data.Vector.Vector Double -> Data.Vector.Vector Double
grad_vec_prod = grad vec_prod
