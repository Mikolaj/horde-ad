{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
module ProdBackpropTools where

import Prelude

import           Criterion.Main
import qualified Data.Vector
import qualified Data.Vector.Generic as V

import           Numeric.Backprop
import qualified Prelude.Backprop

-- TODO: this is probably naive. Revisit once we understand backprop better.

-- TODO: Unboxed vectors don't have the Foldable constraint, so I don't know
-- how to use them. Perhaps using hmatrix would be easier and with
-- better performance than boxed vectors.

bgroup100, bgroup200, bgroup1000, bgroup1e4, bgroup1e5, bgroup1e6, bgroup1e7, bgroup5e7 :: [Double] -> Benchmark

bgroup100 allxs =
      env (return (take 100 allxs, V.fromList $ take 100 allxs)) $
      \ ~(list, vec) ->
      bgroup "100"
        [ bench "func" $ nf prod list
        , bench "grad" $ nf grad_prod list
        , bench "func_vec" $ nf vec_prod vec
        , bench "grad_vec" $ nf grad_vec_prod vec
        , bench "func_handwritten" $ nf handwritten_prod list
        , bench "grad_handwritten" $ nf grad_handwritten_prod list
        , bench "func_handwritten_vec" $ nf handwritten_vec_prod vec
        , bench "grad_handwritten_vec" $ nf grad_handwritten_vec_prod vec
        ]

bgroup200 allxs =
      env (return (take 200 allxs, V.fromList $ take 200 allxs)) $
      \ ~(list, vec) ->
      bgroup "200"
        [ bench "func" $ nf prod list
        , bench "grad" $ nf grad_prod list
        , bench "func_vec" $ nf vec_prod vec
        , bench "grad_vec" $ nf grad_vec_prod vec
        , bench "func_handwritten" $ nf handwritten_prod list
        , bench "grad_handwritten" $ nf grad_handwritten_prod list
        , bench "func_handwritten_vec" $ nf handwritten_vec_prod vec
        , bench "grad_handwritten_vec" $ nf grad_handwritten_vec_prod vec
        ]

bgroup1000 allxs =
      env (return (take 1000 allxs, V.fromList $ take 1000 allxs)) $
      \ ~(list, vec) ->
      bgroup "1000"
        [ bench "func" $ nf prod list
        , bench "grad" $ nf grad_prod list
        , bench "func_vec" $ nf vec_prod vec
        , bench "grad_vec" $ nf grad_vec_prod vec
        , bench "func_handwritten" $ nf handwritten_prod list
        , bench "grad_handwritten" $ nf grad_handwritten_prod list
        , bench "func_handwritten_vec" $ nf handwritten_vec_prod vec
        , bench "grad_handwritten_vec" $ nf grad_handwritten_vec_prod vec
        ]

bgroup1e4 allxs =
      env (return $ V.fromList $ take 10000 allxs) $
      \ ~vec ->
      bgroup "1e4"
        -- backprop takes quite long, so many benches pruned
        [ bench "func_handwritten_vec" $ nf handwritten_vec_prod vec
        , bench "grad_handwritten_vec" $ nf grad_handwritten_vec_prod vec
        ]

bgroup1e5 allxs =
      env (return $ V.fromList $ take 100000 allxs) $
      \ ~vec ->
      bgroup "1e5"
        -- backprop takes forever except with vector-based handwritten gradients
        [ bench "func_handwritten_vec" $ nf handwritten_vec_prod vec
        , bench "grad_handwritten_vec" $ nf grad_handwritten_vec_prod vec
        ]

bgroup1e6 allxs =
      env (return $ V.fromList $ take 1000000 allxs) $
      \ ~vec ->
      bgroup "1e6"
        -- backprop takes forever except with vector-based handwritten gradients
        [ bench "func_handwritten_vec" $ nf handwritten_vec_prod vec
        , bench "grad_handwritten_vec" $ nf grad_handwritten_vec_prod vec
        ]

bgroup1e7 allxs =
      env (return $ V.fromList $ take 10000000 allxs) $
      \ ~vec ->
      bgroup "1e7"
        -- backprop takes forever except with vector-based handwritten gradients
        [ bench "func_handwritten_vec" $ nf handwritten_vec_prod vec
        , bench "grad_handwritten_vec" $ nf grad_handwritten_vec_prod vec
        ]

bgroup5e7 allxs =
      env (return $ V.fromList $ take 50000000 allxs) $
      \ ~vec ->
      bgroup "5e7"  -- 5e7 == 5 * 10^7 == 0.5 * 10^8 == 0.5e8
        -- backprop takes forever except with vector-based handwritten gradients
        [ bench "func_handwritten_vec" $ nf handwritten_vec_prod vec
        , bench "grad_handwritten_vec" $ nf grad_handwritten_vec_prod vec
        ]

{-
foldl' :: (Traversable t, Backprop a, Reifies s W)
       => (BVar s b -> BVar s a -> BVar s b) -> BVar s b -> BVar s (t a)
       -> BVar s b
-}

prod_aux :: (Fractional r, Backprop r, Reifies s W)
         => BVar s [r] -> BVar s r
prod_aux = Prelude.Backprop.foldl' (*) 1

prod :: [Double] -> Double
prod = evalBP prod_aux

grad_prod :: [Double] -> [Double]
grad_prod = gradBP prod_aux

-- Apparently, vectors degrade performance (except when using the handwritten
-- @product@), so there may be conversion(s) to list going on.
vec_prod_aux :: (Fractional r, Backprop r, Reifies s W)
             => BVar s (Data.Vector.Vector r) -> BVar s r
vec_prod_aux = Prelude.Backprop.foldl' (*) 1

vec_prod :: Data.Vector.Vector Double -> Double
vec_prod = evalBP vec_prod_aux

grad_vec_prod :: Data.Vector.Vector Double -> Data.Vector.Vector Double
grad_vec_prod = gradBP vec_prod_aux


-- These are extremely fast, because they have fast (not sure if accurate,
-- given the multiplication and then division) hand-written gradients.

{-
product :: (Foldable t, Functor t, Backprop (t a), Fractional a, Reifies s W)
        => BVar s (t a) -> BVar s a
product af = liftOp1 af . op1 $ \xs ->
    let p = P.product xs
    in ( p
       , \d -> (\x -> p * d / x) P.<$> xs
       )
-}

handwritten_prod_aux :: (Fractional r, Backprop r, Reifies s W)
                     => BVar s [r] -> BVar s r
handwritten_prod_aux = Prelude.Backprop.product  -- hand-written gradient

handwritten_prod :: [Double] -> Double
handwritten_prod = evalBP handwritten_prod_aux

grad_handwritten_prod :: [Double] -> [Double]
grad_handwritten_prod = gradBP prod_aux

handwritten_vec_prod_aux :: (Fractional r, Backprop r, Reifies s W)
                         => BVar s (Data.Vector.Vector r) -> BVar s r
handwritten_vec_prod_aux = Prelude.Backprop.product  -- hand-written gradient

handwritten_vec_prod :: Data.Vector.Vector Double -> Double
handwritten_vec_prod = evalBP handwritten_vec_prod_aux

grad_handwritten_vec_prod :: Data.Vector.Vector Double
                          -> Data.Vector.Vector Double
grad_handwritten_vec_prod = gradBP handwritten_vec_prod_aux
