-- Copyright (c) Microsoft Corporation.
-- Licensed under the MIT license.
import Criterion.Main
import System.Random


-- Product of list of numbers
prod :: Fractional a => [a] -> a
prod [x] = x
prod (x:xs) = x * prod xs

-- Product of list of numbers
-- Quadratic time, as recurses twice
grad_prod_slow :: Fractional a => [a] -> [a]
grad_prod_slow [_] = [1.0]
grad_prod_slow (x:xs) =
    (prod xs : map (* x) (grad_prod_slow xs))

-- Gradient of prod
-- Computed in linear time
grad_prod_aux :: Fractional a => a -> [a] -> (a, [a])
grad_prod_aux _ [] = (1.0, [])
grad_prod_aux q (x:xs) =
    let (p1,out) = grad_prod_aux (q * x) xs
    in (x * p1, q * p1 : out)

grad_prod :: Fractional a => [a] -> [a]
grad_prod xs = snd $ grad_prod_aux 1.0 xs

del :: Num a => a -> [a] -> [a] -> [[a]]
del d pref [x] = [pref ++ [x + d]]
del d pref (x:xs) =
    (pref ++ ((x+d) : xs)) :
    del d (pref ++ [x]) xs

go :: Int -> IO ()
go seed = do
    let x = [-2.0, 3.0, 5.0, -7.0]
    let fx = prod x
    let delta = 0.0001
    let x_plus_dxs = del delta [] x
    let f_x_plus_dxs = map prod x_plus_dxs
    let grad_f_fd = map (\ v -> (v - fx) / delta) f_x_plus_dxs
    let grad_f_ad = grad_prod x
    putStrLn $ ("x         = " ++ show x)
    putStrLn $ ("fx        = " ++ show fx)
    putStrLn $ ("x+dx      = " ++ show x_plus_dxs)
    putStrLn $ ("f(x+dx)   = " ++ show f_x_plus_dxs)
    putStrLn $ ("grad_f_fd = " ++ show grad_f_fd)
    putStrLn $ ("grad_f_ad = " ++ show grad_f_ad)
    putStrLn $ ("grad_f_slow = " ++ show (grad_prod_slow x))
    putStrLn $ ("dif       = " ++ show (maximum $ map abs $ zipWith (-) grad_f_ad grad_f_fd))
    let xs = (map (\ x -> x + 0.55) $ take 10000 (randoms (mkStdGen seed) :: [Double]))
    putStrLn $ ("prod        = " ++ show (prod xs))

main :: IO ()
main =
  let allxs = map (\ x -> x + 0.55) $ randoms (mkStdGen 42) :: [Double] in
  defaultMain
    [ env (return (take 100 allxs)) $
      \ ~list ->
      bgroup "100"
        [ bench "func" $ nf prod list
        , bench "grad" $ nf grad_prod list
        , bench "grad_slow" $ nf grad_prod_slow list
        ]
    , env (return (take 200 allxs)) $
      \ ~list ->
      bgroup "200"
        [ bench "func" $ nf prod list
        , bench "grad" $ nf grad_prod list
        , bench "grad_slow" $ nf grad_prod_slow list
        ]
    , env (return (take 1000 allxs)) $
      \ ~list ->
      bgroup "1000"
        [ bench "func" $ nf prod list
        , bench "grad" $ nf grad_prod list
        , bench "grad_slow" $ nf grad_prod_slow list
        ]
    , env (return (take 10000 allxs)) $
      \ ~list ->
      bgroup "1e4"
        -- grad_slow too slow at this point
        [ bench "func" $ nf prod list
        , bench "grad" $ nf grad_prod list
        ]
    , env (return (take 100000 allxs)) $
      \ ~list ->
      bgroup "1e5"
        [ bench "func" $ nf prod list
        , bench "grad" $ nf grad_prod list
        ]
    , env (return (take 1000000 allxs)) $
      \ ~list ->
      bgroup "1e6"
        [ bench "func" $ nf prod list
        , bench "grad" $ nf grad_prod list
        ]
    , env (return (take 10000000 allxs)) $
      \ ~list ->
      bgroup "1e7"
        [ bench "func" $ nf prod list
        , bench "grad" $ nf grad_prod list
        ]
    , env (return (take 50000000 allxs)) $
      \ ~list ->
      bgroup "Half1e8"  -- 5e7 == 5 * 10^7 == 0.5 * 10^8 == 0.5e8
        [ bench "func" $ nf prod list
        , bench "grad" $ nf grad_prod list
        ]
    ]
