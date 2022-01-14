{-# OPTIONS_GHC -Wno-missing-export-lists #-}
module ProdMostlyHarmlessTools where

import Prelude

import           Criterion.Main
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Unboxed
import           System.Random

import AD

allxs :: [Double]
allxs = map (\ x -> x + 0.55) $ randoms (mkStdGen 42)

bgroup100, bgroup200, bgroup1000, bgroup1e4, bgroup1e5, bgroup1e6, bgroup1e7, bgroup5e7 :: Benchmark

bgroup100 =
      env (return (take 100 allxs, V.fromList $ take 100 allxs)) $
      \ ~(list, vec) ->
      bgroup "100"
        [ bench "func_vec" $ nf vec_prod vec
        , bench "grad_vec" $ nf grad_vec_prod vec
        , bench "grad_toList" $ nf grad_toList_prod list
        , bench "func_vec_omit" $ nf vec_omit_prod vec
        , bench "grad_vec_omit" $ nf grad_vec_omit_prod vec
        ]

bgroup200 =
      env (return (take 200 allxs, V.fromList $ take 200 allxs)) $
      \ ~(list, vec) ->
      bgroup "200"
        [ bench "func_vec" $ nf vec_prod vec
        , bench "grad_vec" $ nf grad_vec_prod vec
        , bench "grad_toList" $ nf grad_toList_prod list
        , bench "func_vec_omit" $ nf vec_omit_prod vec
        , bench "grad_vec_omit" $ nf grad_vec_omit_prod vec
        ]

bgroup1000 =
      env (return (take 1000 allxs, V.fromList $ take 1000 allxs)) $
      \ ~(list, vec) ->
      bgroup "1000"
        [ bench "func_vec" $ nf vec_prod vec
        , bench "grad_vec" $ nf grad_vec_prod vec
        , bench "grad_toList" $ nf grad_toList_prod list
        , bench "func_vec_omit" $ nf vec_omit_prod vec
        , bench "grad_vec_omit" $ nf grad_vec_omit_prod vec
        ]

bgroup1e4 =
      env (return (take 10000 allxs, V.fromList $ take 10000 allxs)) $
      \ ~(list, vec) ->
      bgroup "1e4"
        [ bench "func_vec" $ nf vec_prod vec
        , bench "grad_vec" $ nf grad_vec_prod vec
        , bench "grad_toList" $ nf grad_toList_prod list
        , bench "func_vec_omit" $ nf vec_omit_prod vec
        , bench "grad_vec_omit" $ nf grad_vec_omit_prod vec
        ]

bgroup1e5 =
      env (return (take 100000 allxs, V.fromList $ take 100000 allxs)) $
      \ ~(list, vec) ->
      bgroup "1e5"
        [ bench "func_vec" $ nf vec_prod vec
        , bench "grad_vec" $ nf grad_vec_prod vec
        , bench "grad_toList" $ nf grad_toList_prod list
        , bench "func_vec_omit" $ nf vec_omit_prod vec
        , bench "grad_vec_omit" $ nf grad_vec_omit_prod vec
        ]

bgroup1e6 =
      env (return (take 1000000 allxs, V.fromList $ take 1000000 allxs)) $
      \ ~(list, vec) ->
      bgroup "1e6"
        [ bench "func_vec" $ nf vec_prod vec
        , bench "grad_vec" $ nf grad_vec_prod vec
        , bench "grad_toList" $ nf grad_toList_prod list
        , bench "func_vec_omit" $ nf vec_omit_prod vec
        , bench "grad_vec_omit" $ nf grad_vec_omit_prod vec
        ]

bgroup1e7 =
      env (return (take 10000000 allxs, V.fromList $ take 10000000 allxs)) $
      \ ~(list, vec) ->
      bgroup "1e7"
        [ bench "func_vec" $ nf vec_prod vec
        , bench "grad_vec" $ nf grad_vec_prod vec
        , bench "grad_toList" $ nf grad_toList_prod list
        , bench "func_vec_omit" $ nf vec_omit_prod vec
        , bench "grad_vec_omit" $ nf grad_vec_omit_prod vec
        ]

bgroup5e7 =
      env (return $ V.fromList $ take 50000000 allxs) $
      \ ~vec ->
      bgroup "5e7"  -- 5e7 == 5 * 10^7 == 0.5 * 10^8 == 0.5e8
        [ bench "func_vec" $ nf vec_prod vec
        , bench "grad_vec" $ nf grad_vec_prod vec
-- this already takes 35G, so the worse variants not attempted:
--        , bench "grad_toList" $ nf grad_toList_prod list
        , bench "func_vec_omit" $ nf vec_omit_prod vec
        , bench "grad_vec_omit" $ nf grad_vec_omit_prod vec
        ]

vec_prod_aux :: forall m r. (DeltaMonad r m, Num r, Data.Vector.Unboxed.Unbox r)
             => VecDualDelta r -> m (DualDelta r)
vec_prod_aux vec = do
  let f :: DualDelta r -> Int -> r -> m (DualDelta r)
      f !acc !i !valX = do
        -- An awkward use of internals that can't be avoided without
        -- some other awkward bits of code and an extra performance hit.
        -- The whole business with @vec@ being a pair of vectors,
        -- instead of one vector, is an optimization for gradient descent,
        -- which works fine there, but costs us some cycles and clarity here,
        -- where there's no gradient descent to manage the vectors.
        let x = D valX (snd vec V.! i)
        acc *\ x  -- no handwritten gradients; only gradient for * is provided;
                  -- also, not omitting bindings; all let-bindings are present
  V.ifoldM' f (scalar 1) $ fst vec

grad_vec_prod :: (Eq r, Num r, Data.Vector.Unboxed.Unbox r)
              => Domain r -> Domain' r
grad_vec_prod = fst . df vec_prod_aux

vec_prod :: (Num r, Data.Vector.Unboxed.Unbox r)
         => Domain r -> r
vec_prod = valueDualDelta vec_prod_aux

grad_toList_prod :: (Eq r, Num r, Data.Vector.Unboxed.Unbox r)
                 => [r] -> [r]
grad_toList_prod l = V.toList $ grad_vec_prod $ V.fromList l

-- A version that omits all Delta bindings except for just one let
-- placed at the end in case the outcome of this function is used
-- multiple times by it's consumers. In the future, such omission
-- of bindings may ease automatic fusion of Delta expressions.
-- It probably wouldn't help in this case, though.

vec_omit_prod_aux
  :: forall m r. (DeltaMonad r m, Num r, Data.Vector.Unboxed.Unbox r)
   => VecDualDelta r -> m (DualDelta r)
vec_omit_prod_aux vec = do
  let f :: DualDelta r -> Int -> r -> DualDelta r
      f !acc !i !valX =
        let x = D valX (snd vec V.! i)
        in acc * x  -- omitting bindings, because we know nothing repeats here
  returnLet $ V.ifoldl' f (scalar 1) $ fst vec

grad_vec_omit_prod :: (Eq r, Num r, Data.Vector.Unboxed.Unbox r)
                   => Domain r -> Domain' r
grad_vec_omit_prod = fst . df vec_omit_prod_aux

vec_omit_prod :: (Num r, Data.Vector.Unboxed.Unbox r)
              => Domain r -> r
vec_omit_prod = valueDualDelta vec_omit_prod_aux
