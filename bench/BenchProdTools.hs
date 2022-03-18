{-# LANGUAGE AllowAmbiguousTypes, TypeFamilies #-}
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
        , bench "grad_toList" $ nf grad_toList_prod list
        , bench "func_vec_omit" $ nf vec_omit_prod vec
        , bench "grad_vec_omit" $ nf grad_vec_omit_prod vec
        , bench "grad_vec_omit_scalarSum" $ nf grad_vec_omit_scalarSum vec
        , bench "grad_vec_omit_sum" $ nf grad_vec_omit_sum vec
        , bench "grad_vec_omit_altSum" $ nf grad_vec_omit_altSum vec
        ]

bgroup200 allxs =
      env (return (take 200 allxs, V.fromList $ take 200 allxs)) $
      \ ~(list, vec) ->
      bgroup "200"
        [ bench "func_vec" $ nf vec_prod vec
        , bench "grad_vec" $ nf grad_vec_prod vec
        , bench "grad_toList" $ nf grad_toList_prod list
        , bench "func_vec_omit" $ nf vec_omit_prod vec
        , bench "grad_vec_omit" $ nf grad_vec_omit_prod vec
        , bench "grad_vec_omit_scalarSum" $ nf grad_vec_omit_scalarSum vec
        , bench "grad_vec_omit_sum" $ nf grad_vec_omit_sum vec
        , bench "grad_vec_omit_altSum" $ nf grad_vec_omit_altSum vec
        ]

bgroup1000 allxs =
      env (return (take 1000 allxs, V.fromList $ take 1000 allxs)) $
      \ ~(list, vec) ->
      bgroup "1000"
        [ bench "func_vec" $ nf vec_prod vec
        , bench "grad_vec" $ nf grad_vec_prod vec
        , bench "grad_toList" $ nf grad_toList_prod list
        , bench "func_vec_omit" $ nf vec_omit_prod vec
        , bench "grad_vec_omit" $ nf grad_vec_omit_prod vec
        , bench "grad_vec_omit_scalarSum" $ nf grad_vec_omit_scalarSum vec
        , bench "grad_vec_omit_sum" $ nf grad_vec_omit_sum vec
        , bench "grad_vec_omit_altSum" $ nf grad_vec_omit_altSum vec
        ]

bgroup1e4 allxs =
      env (return (take 10000 allxs, V.fromList $ take 10000 allxs)) $
      \ ~(list, vec) ->
      bgroup "1e4"
        [ bench "func_vec" $ nf vec_prod vec
        , bench "grad_vec" $ nf grad_vec_prod vec
        , bench "grad_toList" $ nf grad_toList_prod list
        , bench "func_vec_omit" $ nf vec_omit_prod vec
        , bench "grad_vec_omit" $ nf grad_vec_omit_prod vec
        , bench "grad_vec_omit_scalarSum" $ nf grad_vec_omit_scalarSum vec
        , bench "grad_vec_omit_sum" $ nf grad_vec_omit_sum vec
        , bench "grad_vec_omit_altSum" $ nf grad_vec_omit_altSum vec
        ]

bgroup1e5 allxs =
      env (return (take 100000 allxs, V.fromList $ take 100000 allxs)) $
      \ ~(list, vec) ->
      bgroup "1e5"
        [ bench "func_vec" $ nf vec_prod vec
        , bench "grad_vec" $ nf grad_vec_prod vec
        , bench "grad_toList" $ nf grad_toList_prod list
        , bench "func_vec_omit" $ nf vec_omit_prod vec
        , bench "grad_vec_omit" $ nf grad_vec_omit_prod vec
        , bench "grad_vec_omit_scalarSum" $ nf grad_vec_omit_scalarSum vec
        , bench "grad_vec_omit_sum" $ nf grad_vec_omit_sum vec
        , bench "grad_vec_omit_altSum" $ nf grad_vec_omit_altSum vec
        ]

bgroup1e6 allxs =
      env (return (take 1000000 allxs, V.fromList $ take 1000000 allxs)) $
      \ ~(list, vec) ->
      bgroup "1e6"
        [ bench "func_vec" $ nf vec_prod vec
        , bench "grad_vec" $ nf grad_vec_prod vec
        , bench "grad_toList" $ nf grad_toList_prod list
        , bench "func_vec_omit" $ nf vec_omit_prod vec
        , bench "grad_vec_omit" $ nf grad_vec_omit_prod vec
        , bench "grad_vec_omit_scalarSum" $ nf grad_vec_omit_scalarSum vec
        , bench "grad_vec_omit_sum" $ nf grad_vec_omit_sum vec
-- low memory usage, but repeated benchmark runs take quarters
--        , bench "grad_vec_omit_altSum" $ nf grad_vec_omit_altSum vec
        ]

bgroup1e7 allxs =
      env (return (take 10000000 allxs, V.fromList $ take 10000000 allxs)) $
      \ ~(list, vec) ->
      bgroup "1e7"
        [ bench "func_vec" $ nf vec_prod vec
        , bench "grad_vec" $ nf grad_vec_prod vec
        , bench "grad_toList" $ nf grad_toList_prod list
        , bench "func_vec_omit" $ nf vec_omit_prod vec
        , bench "grad_vec_omit" $ nf grad_vec_omit_prod vec
        , bench "grad_vec_omit_scalarSum" $ nf grad_vec_omit_scalarSum vec
        , bench "grad_vec_omit_sum" $ nf grad_vec_omit_sum vec
        ]

bgroup5e7 allxs =
      env (return $ V.fromList $ take 50000000 allxs) $
      \ vec ->
      bgroup "5e7"  -- 5e7 == 5 * 10^7 == 0.5 * 10^8 == 0.5e8
        [ bench "func_vec" $ nf vec_prod vec
        , bench "grad_vec" $ nf grad_vec_prod vec
-- this already takes 35G, so the worse variants not attempted:
--        , bench "grad_toList" $ nf grad_toList_prod list
        , bench "func_vec_omit" $ nf vec_omit_prod vec
        , bench "grad_vec_omit" $ nf grad_vec_omit_prod vec
        , bench "grad_vec_omit_scalarSum" $ nf grad_vec_omit_scalarSum vec
        , bench "grad_vec_omit_sum" $ nf grad_vec_omit_sum vec
        ]

(*\) :: DualMonad r m
     => DualNumber r -> DualNumber r -> m (DualNumber r)
(*\) u v = returnLet $ u * v

-- The @foldMDelta'@, instead of the standard @foldM'@, is an awkward clutch
-- that can't be avoided without changing the representation of the vector
-- of dual numbers. The use of a pair of vectors to represent
-- a vector of dual numbers is an optimization for gradient descent,
-- which works fine there, but costs us some cycles and the use
-- of a custom operation here, where there's no gradient descent
-- to manage the vectors for us.
vec_prod_aux :: forall m r. DualMonad r m
             => DualNumberVariables r -> m (DualNumber r)
vec_prod_aux = foldMDelta' (*\) 1
  -- no handwritten derivatives; only the derivative for @(*)@ is provided;
  -- also, not omitting bindings; all let-bindings are present, see below

vec_prod :: forall r. HasDelta r
         => Vector (Primal r) -> Primal r
vec_prod ds = primalValue @r vec_prod_aux (ds, V.empty, V.empty, V.empty)

grad_vec_prod :: HasDelta r => Vector (Primal r) -> Vector (Primal r)
grad_vec_prod ds =
  (\(v, _, _, _) -> v) $ fst $ df vec_prod_aux (ds, V.empty, V.empty, V.empty)

grad_toList_prod :: HasDelta r => [Primal r] -> [Primal r]
grad_toList_prod l = V.toList $ grad_vec_prod $ V.fromList l

-- A version that omits all Delta bindings except for just one let
-- placed at the end in case the outcome of this function is used
-- multiple times by it's consumers. In the future, such omission
-- of bindings may ease automatic fusion of Delta expressions.
-- It probably wouldn't help in this case, though.

vec_omit_prod_aux
  :: forall r m. DualMonad r m
  => DualNumberVariables r -> m (DualNumber r)
vec_omit_prod_aux vec = returnLet $ foldlDelta' (*) 1 vec
  -- omitting most bindings, because we know nothing repeats inside

vec_omit_prod :: forall r. HasDelta r
              => Vector (Primal r) -> Primal r
vec_omit_prod ds = primalValue @r vec_omit_prod_aux (ds, V.empty, V.empty, V.empty)

grad_vec_omit_prod :: HasDelta r
                   => Vector (Primal r) -> Vector (Primal r)
grad_vec_omit_prod ds =
  (\(v, _, _, _) -> v)
  $ fst $ df vec_omit_prod_aux (ds, V.empty, V.empty, V.empty)


vec_omit_scalarSum_aux
  :: forall m r. DualMonad r m
  => DualNumberVariables r -> m (DualNumber r)
vec_omit_scalarSum_aux vec = returnLet $ foldlDelta' (+) 0 vec

sumElementsV :: DualMonad (Delta0 Double) m
             => DualNumberVariables (Delta0 Double) -> m (DualNumber (Delta0 Double))
sumElementsV variables = do
  let x = varV variables 0
  returnLet $ sumElements0 x

altSumElementsV :: DualMonad (Delta0 Double) m
                => DualNumberVariables (Delta0 Double) -> m (DualNumber (Delta0 Double))
altSumElementsV variables = do
  let x = varV variables 0
  returnLet $ altSumElements0 x

grad_vec_omit_scalarSum :: HasDelta r => Vector (Primal r) -> Vector (Primal r)
grad_vec_omit_scalarSum ds =
  (\(v, _, _, _) -> v)
  $ fst $ df vec_omit_scalarSum_aux (ds, V.empty, V.empty, V.empty)

grad_vec_omit_sum :: Vector Double -> Vector Double
grad_vec_omit_sum ds =
  (\(_, v, _, _) -> V.head v)
  $ fst $ df sumElementsV (V.empty, V.singleton ds, V.empty, V.empty)

grad_vec_omit_altSum :: Vector Double -> Vector Double
grad_vec_omit_altSum ds =
  (\(_, v, _, _) -> V.head v)
  $ fst $ df altSumElementsV (V.empty, V.singleton ds, V.empty, V.empty)
