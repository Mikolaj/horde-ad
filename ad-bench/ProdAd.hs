module Main (main) where

import Prelude

import           Criterion.Main
import qualified Data.Vector
import qualified Data.Vector.Generic as V
import           System.Random

import Numeric.AD.Mode.Reverse.Double hiding (diff)

main :: IO ()
main = do
  let allxs = map (+ 0.55) $ randoms (mkStdGen 42) :: [Double]
  defaultMain
    [ env (return (take 100 allxs, V.fromList $ take 100 allxs)) $
      \ ~(list, vec) ->
      bgroup "100"
        [ bench "func" $ nf prod list
        , bench "grad" $ nf grad_prod list
        , bench "vec_func" $ nf vec_prod vec
        , bench "vec_grad" $ nf vec_grad_prod vec
        ]
    , env (return (take 200 allxs, V.fromList $ take 200 allxs)) $
      \ ~(list, vec) ->
      bgroup "200"
        [ bench "func" $ nf prod list
        , bench "grad" $ nf grad_prod list
        , bench "vec_func" $ nf vec_prod vec
        , bench "vec_grad" $ nf vec_grad_prod vec
        ]
    , env (return (take 1000 allxs, V.fromList $ take 1000 allxs)) $
      \ ~(list, vec) ->
      bgroup "1000"
        [ bench "func" $ nf prod list
        , bench "grad" $ nf grad_prod list
        , bench "vec_func" $ nf vec_prod vec
        , bench "vec_grad" $ nf vec_grad_prod vec
        ]
    , env (return (take 10000 allxs, V.fromList $ take 10000 allxs)) $
      \ ~(list, vec) ->
      bgroup "1e4"
        [ bench "func" $ nf prod list
        , bench "grad" $ nf grad_prod list
        , bench "vec_func" $ nf vec_prod vec
        , bench "vec_grad" $ nf vec_grad_prod vec
        ]
    , env (return (take 100000 allxs, V.fromList $ take 100000 allxs)) $
      \ ~(list, vec) ->
      bgroup "1e5"
        [ bench "func" $ nf prod list
        , bench "grad" $ nf grad_prod list
        , bench "vec_func" $ nf vec_prod vec
        , bench "vec_grad" $ nf vec_grad_prod vec
        ]
    , env (return (take 1000000 allxs, V.fromList $ take 1000000 allxs)) $
      \ ~(list, vec) ->
      bgroup "1e6"
        [ bench "func" $ nf prod list
        , bench "grad" $ nf grad_prod list
        , bench "vec_func" $ nf vec_prod vec
        , bench "vec_grad" $ nf vec_grad_prod vec
        ]
    , env (return (take 10000000 allxs, V.fromList $ take 10000000 allxs)) $
      \ ~(list, vec) ->
      bgroup "1e7"
        [ bench "func" $ nf prod list
        , bench "grad" $ nf grad_prod list
        , bench "vec_func" $ nf vec_prod vec
        , bench "vec_grad" $ nf vec_grad_prod vec
        ]
    , env (return $ take 50000000 allxs) $
      \ ~list ->
      bgroup "Half1e8"  -- 5e7 == 5 * 10^7 == 0.5 * 10^8 == 0.5e8
        [ bench "func" $ nf prod list
        , bench "grad" $ nf grad_prod list
-- this already takes 20G with 'ffi' flag, so the worse variants not attempted:
--        , bench "vec_func" $ nf vec_prod vec
--        , bench "vec_grad" $ nf vec_grad_prod vec
        ]
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

vec_grad_prod :: Data.Vector.Vector Double -> Data.Vector.Vector Double
vec_grad_prod = grad vec_prod
