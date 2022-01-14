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

bgroup100, bgroup200, bgroup1000, bgroup1e4, bgroup1e5, bgroup1e6, bgroup1e7, bgroupHalf1e8 :: Benchmark

bgroup100 =
      env (return (take 100 allxs, V.fromList $ take 100 allxs)) $
      \ ~(list, vec) ->
      bgroup "100"
        [ bench "vec_func" $ nf vec_prod vec
        , bench "vec_grad" $ nf vec_grad_prod vec
        , bench "toList_grad" $ nf toList_grad_prod list
        , bench "omit_vec_func" $ nf omit_vec_prod vec
        , bench "omit_vec_grad" $ nf omit_vec_grad_prod vec
        ]

bgroup200 =
      env (return (take 200 allxs, V.fromList $ take 200 allxs)) $
      \ ~(list, vec) ->
      bgroup "200"
        [ bench "vec_func" $ nf vec_prod vec
        , bench "vec_grad" $ nf vec_grad_prod vec
        , bench "toList_grad" $ nf toList_grad_prod list
        , bench "omit_vec_func" $ nf omit_vec_prod vec
        , bench "omit_vec_grad" $ nf omit_vec_grad_prod vec
        ]

bgroup1000 =
      env (return (take 1000 allxs, V.fromList $ take 1000 allxs)) $
      \ ~(list, vec) ->
      bgroup "1000"
        [ bench "vec_func" $ nf vec_prod vec
        , bench "vec_grad" $ nf vec_grad_prod vec
        , bench "toList_grad" $ nf toList_grad_prod list
        , bench "omit_vec_func" $ nf omit_vec_prod vec
        , bench "omit_vec_grad" $ nf omit_vec_grad_prod vec
        ]

bgroup1e4 =
      env (return (take 10000 allxs, V.fromList $ take 10000 allxs)) $
      \ ~(list, vec) ->
      bgroup "1e4"
        [ bench "vec_func" $ nf vec_prod vec
        , bench "vec_grad" $ nf vec_grad_prod vec
        , bench "toList_grad" $ nf toList_grad_prod list
        , bench "omit_vec_func" $ nf omit_vec_prod vec
        , bench "omit_vec_grad" $ nf omit_vec_grad_prod vec
        ]

bgroup1e5 =
      env (return (take 100000 allxs, V.fromList $ take 100000 allxs)) $
      \ ~(list, vec) ->
      bgroup "1e5"
        [ bench "vec_func" $ nf vec_prod vec
        , bench "vec_grad" $ nf vec_grad_prod vec
        , bench "toList_grad" $ nf toList_grad_prod list
        , bench "omit_vec_func" $ nf omit_vec_prod vec
        , bench "omit_vec_grad" $ nf omit_vec_grad_prod vec
        ]

bgroup1e6 =
      env (return (take 1000000 allxs, V.fromList $ take 1000000 allxs)) $
      \ ~(list, vec) ->
      bgroup "1e6"
        [ bench "vec_func" $ nf vec_prod vec
        , bench "vec_grad" $ nf vec_grad_prod vec
        , bench "toList_grad" $ nf toList_grad_prod list
        , bench "omit_vec_func" $ nf omit_vec_prod vec
        , bench "omit_vec_grad" $ nf omit_vec_grad_prod vec
        ]

bgroup1e7 =
      env (return (take 10000000 allxs, V.fromList $ take 10000000 allxs)) $
      \ ~(list, vec) ->
      bgroup "1e7"
        [ bench "vec_func" $ nf vec_prod vec
        , bench "vec_grad" $ nf vec_grad_prod vec
        , bench "toList_grad" $ nf toList_grad_prod list
        , bench "omit_vec_func" $ nf omit_vec_prod vec
        , bench "omit_vec_grad" $ nf omit_vec_grad_prod vec
        ]

bgroupHalf1e8 =
      env (return (take 50000000 allxs, V.fromList $ take 50000000 allxs)) $
      \ ~(_list, vec) ->
      bgroup "Half1e8"  -- 5e7 == 5 * 10^7 == 0.5 * 10^8 == 0.5e8
        [ bench "vec_func" $ nf vec_prod vec
        , bench "vec_grad" $ nf vec_grad_prod vec
-- this already takes 35G, so the worse variants not attempted:
--        , bench "toList_grad" $ nf toList_grad_prod list
        , bench "omit_vec_func" $ nf omit_vec_prod vec
        , bench "omit_vec_grad" $ nf omit_vec_grad_prod vec
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

vec_grad_prod :: (Eq r, Num r, Data.Vector.Unboxed.Unbox r)
              => Domain r -> Domain' r
vec_grad_prod = fst . df vec_prod_aux

vec_prod :: (Num r, Data.Vector.Unboxed.Unbox r)
         => Domain r -> r
vec_prod = valueDualDelta vec_prod_aux

toList_grad_prod :: (Eq r, Num r, Data.Vector.Unboxed.Unbox r)
                 => [r] -> [r]
toList_grad_prod l = V.toList $ vec_grad_prod $ V.fromList l

-- A version that omits all Delta bindings except for just one let
-- placed at the end in case the outcome of this function is used
-- multiple times by it's consumers. In the future, such omission
-- of bindings may ease automatic fusion of Delta expressions.
-- It probably wouldn't help in this case, though.

omit_vec_prod_aux
  :: forall m r. (DeltaMonad r m, Num r, Data.Vector.Unboxed.Unbox r)
   => VecDualDelta r -> m (DualDelta r)
omit_vec_prod_aux vec = do
  let f :: DualDelta r -> Int -> r -> DualDelta r
      f !acc !i !valX =
        let x = D valX (snd vec V.! i)
        in acc * x  -- omitting bindings, because we know nothing repeats here
  returnLet $ V.ifoldl' f (scalar 1) $ fst vec

omit_vec_grad_prod :: (Eq r, Num r, Data.Vector.Unboxed.Unbox r)
                   => Domain r -> Domain' r
omit_vec_grad_prod = fst . df omit_vec_prod_aux

omit_vec_prod :: (Num r, Data.Vector.Unboxed.Unbox r)
              => Domain r -> r
omit_vec_prod = valueDualDelta omit_vec_prod_aux
