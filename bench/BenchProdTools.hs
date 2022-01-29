{-# OPTIONS_GHC -Wno-missing-export-lists #-}
module BenchProdTools where

import Prelude

import           Criterion.Main
import qualified Data.Vector.Generic as V
import           Foreign.Storable (Storable)

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
        ]

-- The @foldMDelta'@, instead of the standard @foldM'@, is an awkward clutch
-- that can't be avoided without changing the representation of the vector
-- of dual numbers. The use of a pair of vectors to represent
-- a vector of dual numbers is an optimization for gradient descent,
-- which works fine there, but costs us some cycles and the use
-- of a custom operation here, where there's no gradient descent
-- to manage the vectors for us.
vec_prod_aux :: forall m r. (DeltaMonad r m, Num r, Storable r)
             => VecDualDelta r -> m (DualDelta r)
vec_prod_aux vec = foldMDelta' (*\) (scalar 1) vec
  -- no handwritten gradients; only the gradient for @(*)@ is provided;
  -- also, not omitting bindings; all let-bindings are present, see below

vec_prod :: (Num r, Storable r)
         => Domain r -> r
vec_prod ds = valueDualDelta vec_prod_aux (ds, V.empty)

grad_vec_prod :: (Eq r, Num r, Storable r)
              => Domain r -> Domain' r
grad_vec_prod ds = fst $ fst $ df vec_prod_aux (ds, V.empty)

grad_toList_prod :: (Eq r, Num r, Storable r)
                 => [r] -> [r]
grad_toList_prod l = V.toList $ grad_vec_prod $ V.fromList l

-- A version that omits all Delta bindings except for just one let
-- placed at the end in case the outcome of this function is used
-- multiple times by it's consumers. In the future, such omission
-- of bindings may ease automatic fusion of Delta expressions.
-- It probably wouldn't help in this case, though.

vec_omit_prod_aux
  :: forall m r. (DeltaMonad r m, Num r, Storable r)
  => VecDualDelta r -> m (DualDelta r)
vec_omit_prod_aux vec = returnLet $ foldlDelta' (*) (scalar 1) vec
  -- omitting most bindings, because we know nothing repeats inside

vec_omit_prod :: (Num r, Storable r)
              => Domain r -> r
vec_omit_prod ds = valueDualDelta vec_omit_prod_aux (ds, V.empty)

grad_vec_omit_prod :: (Eq r, Num r, Storable r)
                   => Domain r -> Domain' r
grad_vec_omit_prod ds = fst $ fst $ df vec_omit_prod_aux (ds, V.empty)
