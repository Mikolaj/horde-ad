{-# LANGUAGE FlexibleContexts #-}
module Main (main) where

import Prelude

import           Criterion.Main
import qualified Data.Vector
import qualified Data.Vector.Generic as V
import           System.Random

import           Numeric.Backprop
import qualified Prelude.Backprop

-- TODO: this is probably naive. Revisit once we understand backprop better.

-- TODO: Unboxed vectors don't have the Foldable constraint, so I don't know
-- how to use them. Perhaps using hmatrix would be easier and with
-- better performance than boxed vectors.

main :: IO ()
main = do
  let allxs = map (+ 0.55) $ randoms (mkStdGen 42) :: [Double]
      vec100 = V.fromList $ take 100 allxs
      vec200 = V.fromList $ take 200 allxs
      vec1000 = V.fromList $ take 1000 allxs
      vec1000000 = V.fromList $ take 1000000 allxs
      vec10000000 = V.fromList $ take 10000000 allxs
  defaultMain
    [ bgroup "100"
        [ bench "func" $ nf prod (take 100 allxs)
        , bench "grad" $ nf grad_prod (take 100 allxs)
        , bench "vec_func" $ nf vec_prod vec100
        , bench "vec_grad" $ nf vec_grad_prod vec100
        , bench "handwritten_func" $ nf handwritten_prod (take 100 allxs)
        , bench "handwritten_grad" $ nf handwritten_grad_prod (take 100 allxs)
        , bench "handwritten_vec_func" $ nf handwritten_vec_prod vec100
        , bench "handwritten_vec_grad" $ nf handwritten_vec_grad_prod vec100
        ]
    , bgroup "200"
        [ bench "func" $ nf prod (take 200 allxs)
        , bench "grad" $ nf grad_prod (take 200 allxs)
        , bench "vec_func" $ nf vec_prod vec200
        , bench "vec_grad" $ nf vec_grad_prod vec200
        , bench "handwritten_func" $ nf handwritten_prod (take 200 allxs)
        , bench "handwritten_grad" $ nf handwritten_grad_prod (take 200 allxs)
        , bench "handwritten_vec_func" $ nf handwritten_vec_prod vec200
        , bench "handwritten_vec_grad" $ nf handwritten_vec_grad_prod vec200
        ]
    , bgroup "1000"
        [ bench "func" $ nf prod (take 1000 allxs)
        , bench "grad" $ nf grad_prod (take 1000 allxs)
        , bench "vec_func" $ nf vec_prod vec1000
        , bench "vec_grad" $ nf vec_grad_prod vec1000
        , bench "handwritten_func" $ nf handwritten_prod (take 1000 allxs)
        , bench "handwritten_grad" $ nf handwritten_grad_prod (take 1000 allxs)
        , bench "handwritten_vec_func" $ nf handwritten_vec_prod vec1000
        , bench "handwritten_vec_grad" $ nf handwritten_vec_grad_prod vec1000
        ]
    , bgroup "1000000"
        [ bench "func" $ nf prod (take 1000000 allxs)
        , bench "grad" $ nf grad_prod (take 1000000 allxs)
        , bench "vec_func" $ nf vec_prod vec1000000
        , bench "vec_grad" $ nf vec_grad_prod vec1000000
        , bench "handwritten_func" $ nf handwritten_prod (take 1000000 allxs)
        , bench "handwritten_grad" $ nf handwritten_grad_prod
                                        (take 1000000 allxs)
        , bench "handwritten_vec_func" $ nf handwritten_vec_prod vec1000000
        , bench "handwritten_vec_grad" $ nf handwritten_vec_grad_prod vec1000000
        ]
    , bgroup "10000000"
        -- backprop can't cope, except with handwritten gradients
        [ bench "handwritten_func" $ nf handwritten_prod (take 10000000 allxs)
        , bench "handwritten_grad" $ nf handwritten_grad_prod
                                        (take 10000000 allxs)
        , bench "handwritten_vec_func" $ nf handwritten_vec_prod vec10000000
        , bench "handwritten_vec_grad" $ nf handwritten_vec_grad_prod
                                            vec10000000
        ]
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

vec_prod_aux :: (Fractional r, Backprop r, Reifies s W)
             => BVar s (Data.Vector.Vector r) -> BVar s r
vec_prod_aux = Prelude.Backprop.foldl' (*) 1

vec_prod :: Data.Vector.Vector Double -> Double
vec_prod = evalBP vec_prod_aux

vec_grad_prod :: Data.Vector.Vector Double -> Data.Vector.Vector Double
vec_grad_prod = gradBP vec_prod_aux


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

handwritten_grad_prod :: [Double] -> [Double]
handwritten_grad_prod = gradBP prod_aux

handwritten_vec_prod_aux :: (Fractional r, Backprop r, Reifies s W)
                         => BVar s (Data.Vector.Vector r) -> BVar s r
handwritten_vec_prod_aux = Prelude.Backprop.product  -- hand-written gradient

handwritten_vec_prod :: Data.Vector.Vector Double -> Double
handwritten_vec_prod = evalBP handwritten_vec_prod_aux

handwritten_vec_grad_prod :: Data.Vector.Vector Double
                          -> Data.Vector.Vector Double
handwritten_vec_grad_prod = gradBP handwritten_vec_prod_aux
