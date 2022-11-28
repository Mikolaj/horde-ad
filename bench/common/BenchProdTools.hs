{-# LANGUAGE DataKinds, TypeFamilies #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
module BenchProdTools where

import Prelude

import           Criterion.Main
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Vector)

import HordeAd

bgroup100, bgroup200, bgroup1000, bgroup1e4, bgroup1e5, bgroup1e6, bgroup1e7, bgroup5e7 :: [Double] -> Benchmark

bgroup100 allxs =
      env (return (take 100 allxs, V.fromList $ take 100 allxs)) $
      \ ~(list, vec) ->
      bgroup "100"
        [ bench "func_vec" $ nf vec_prod vec
        , bench "grad_vec" $ nf grad_vec_prod vec
        , bench "grad_vec_NotShared" $ nf grad_vec_prod_NotShared vec
        , bench "grad_toList" $ nf grad_toList_prod list
        , bench "grad_vec_scalarSum" $ nf grad_vec_scalarSum vec
        , bench "grad_vec_sum" $ nf grad_vec_sum vec
        , bench "grad_vec_altSum" $ nf grad_vec_altSum vec
        ]

bgroup200 allxs =
      env (return (take 200 allxs, V.fromList $ take 200 allxs)) $
      \ ~(list, vec) ->
      bgroup "200"
        [ bench "func_vec" $ nf vec_prod vec
        , bench "grad_vec" $ nf grad_vec_prod vec
        , bench "grad_vec_NotShared" $ nf grad_vec_prod_NotShared vec
        , bench "grad_toList" $ nf grad_toList_prod list
        , bench "grad_vec_scalarSum" $ nf grad_vec_scalarSum vec
        , bench "grad_vec_sum" $ nf grad_vec_sum vec
        , bench "grad_vec_altSum" $ nf grad_vec_altSum vec
        ]

bgroup1000 allxs =
      env (return (take 1000 allxs, V.fromList $ take 1000 allxs)) $
      \ ~(list, vec) ->
      bgroup "1000"
        [ bench "func_vec" $ nf vec_prod vec
        , bench "grad_vec" $ nf grad_vec_prod vec
        , bench "grad_vec_NotShared" $ nf grad_vec_prod_NotShared vec
        , bench "grad_toList" $ nf grad_toList_prod list
        , bench "grad_vec_scalarSum" $ nf grad_vec_scalarSum vec
        , bench "grad_vec_sum" $ nf grad_vec_sum vec
        , bench "grad_vec_altSum" $ nf grad_vec_altSum vec
        ]

bgroup1e4 allxs =
      env (return (take 10000 allxs, V.fromList $ take 10000 allxs)) $
      \ ~(list, vec) ->
      bgroup "1e4"
        [ bench "func_vec" $ nf vec_prod vec
        , bench "grad_vec" $ nf grad_vec_prod vec
        , bench "grad_vec_NotShared" $ nf grad_vec_prod_NotShared vec
        , bench "grad_toList" $ nf grad_toList_prod list
        , bench "grad_vec_scalarSum" $ nf grad_vec_scalarSum vec
        , bench "grad_vec_sum" $ nf grad_vec_sum vec
        , bench "grad_vec_altSum" $ nf grad_vec_altSum vec
        ]

bgroup1e5 allxs =
      env (return (take 100000 allxs, V.fromList $ take 100000 allxs)) $
      \ ~(list, vec) ->
      bgroup "1e5"
        [ bench "func_vec" $ nf vec_prod vec
        , bench "grad_vec" $ nf grad_vec_prod vec
        , bench "grad_vec_NotShared" $ nf grad_vec_prod_NotShared vec
        , bench "grad_toList" $ nf grad_toList_prod list
        , bench "grad_vec_scalarSum" $ nf grad_vec_scalarSum vec
        , bench "grad_vec_sum" $ nf grad_vec_sum vec
        , bench "grad_vec_altSum" $ nf grad_vec_altSum vec
        ]

bgroup1e6 allxs =
      env (return (take 1000000 allxs, V.fromList $ take 1000000 allxs)) $
      \ ~(list, vec) ->
      bgroup "1e6"
        [ bench "func_vec" $ nf vec_prod vec
        , bench "grad_vec" $ nf grad_vec_prod vec
        , bench "grad_vec_NotShared" $ nf grad_vec_prod_NotShared vec
        , bench "grad_toList" $ nf grad_toList_prod list
        , bench "grad_vec_scalarSum" $ nf grad_vec_scalarSum vec
        , bench "grad_vec_sum" $ nf grad_vec_sum vec
-- low memory usage, but repeated benchmark runs take quarters
--        , bench "grad_vec_altSum" $ nf grad_vec_altSum vec
        ]

bgroup1e7 allxs =
      env (return (take 10000000 allxs, V.fromList $ take 10000000 allxs)) $
      \ ~(list, vec) ->
      bgroup "1e7"
        [ bench "func_vec" $ nf vec_prod vec
        , bench "grad_vec" $ nf grad_vec_prod vec
        , bench "grad_vec_NotShared" $ nf grad_vec_prod_NotShared vec
        , bench "grad_toList" $ nf grad_toList_prod list
        , bench "grad_vec_scalarSum" $ nf grad_vec_scalarSum vec
        , bench "grad_vec_sum" $ nf grad_vec_sum vec
        ]

bgroup5e7 allxs =
      env (return $ V.fromList $ take 50000000 allxs) $
      \ vec ->
      bgroup "5e7"  -- 5e7 == 5 * 10^7 == 0.5 * 10^8 == 0.5e8
        [ bench "func_vec" $ nf vec_prod vec
        , bench "grad_vec" $ nf grad_vec_prod vec
        , bench "grad_vec_NotShared" $ nf grad_vec_prod_NotShared vec
-- this already takes 35G, so the worse variants not attempted:
--        , bench "grad_toList" $ nf grad_toList_prod list
        , bench "grad_vec_scalarSum" $ nf grad_vec_scalarSum vec
        , bench "grad_vec_sum" $ nf grad_vec_sum vec
        ]

-- The @foldlDual'@, instead of the standard @foldl'@, is an awkward clutch
-- that can't be avoided without changing the representation of the vector
-- of dual numbers. The use of a pair of vectors to represent
-- a vector of dual numbers is an optimization for gradient descent,
-- which works fine there, but costs us some cycles and the use
-- of a custom operation here, where there's no gradient descent
-- to manage the vectors for us.
vec_prod_aux :: forall d r. ADModeAndNum d r
             => ADInputs d r -> ADVal d r
vec_prod_aux = foldlDual' (*) 1
  -- no handwritten derivatives; only the derivative for @(*)@ is provided

vec_prod :: forall r. ADModeAndNum 'ADModeValue r
         => Vector r -> r
vec_prod ds = valueOnDomains vec_prod_aux (ds, V.empty, V.empty, V.empty)

grad_vec_prod :: HasDelta r => Vector r -> Vector r
grad_vec_prod ds =
  (\(v, _, _, _) -> v) . fst
  $ revOnDomains 1 vec_prod_aux (ds, V.empty, V.empty, V.empty)

grad_vec_prod_NotShared :: HasDelta r => Vector r -> Vector r
grad_vec_prod_NotShared ds =
  (\(v, _, _, _) -> v) . fst
  $ revOnDomains 1 (foldlDual' multNotShared 1) (ds, V.empty, V.empty, V.empty)

grad_toList_prod :: HasDelta r => [r] -> [r]
grad_toList_prod l = V.toList $ grad_vec_prod (V.fromList l)

vec_scalarSum_aux
  :: forall d r. ADModeAndNum d r
  => ADInputs d r -> ADVal d r
vec_scalarSum_aux = foldlDual' (+) 0

sumElementsV :: ADInputs 'ADModeGradient Double
             -> ADVal 'ADModeGradient Double
sumElementsV inputs =
  let x = at1 inputs 0
  in sumElements0 x

altSumElementsV :: ADInputs 'ADModeGradient Double
                -> ADVal 'ADModeGradient Double
altSumElementsV inputs =
  let x = at1 inputs 0
  in altSumElements0 x

grad_vec_scalarSum :: HasDelta r => Vector r -> Vector r
grad_vec_scalarSum ds =
  (\(v, _, _, _) -> v)
  . fst $ revOnDomains 1 vec_scalarSum_aux (ds, V.empty, V.empty, V.empty)

grad_vec_sum :: Vector Double -> Vector Double
grad_vec_sum ds =
  (\(_, v, _, _) -> V.head v) . fst
  $ revOnDomains 1 sumElementsV (V.empty, V.singleton ds, V.empty, V.empty)

grad_vec_altSum :: Vector Double -> Vector Double
grad_vec_altSum ds =
  (\(_, v, _, _) -> V.head v) . fst
  $ revOnDomains 1 altSumElementsV (V.empty, V.singleton ds, V.empty, V.empty)
