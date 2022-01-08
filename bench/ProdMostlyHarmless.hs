module Main (main) where

import Prelude

import           Criterion.Main
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Unboxed
import           System.Random

import AD

main :: IO ()
main = do
  let allxs = map (+ 0.55) $ randoms (mkStdGen 42) :: [Double]
      vec100 = V.fromList $ take 100 allxs
      vec200 = V.fromList $ take 200 allxs
      vec1000 = V.fromList $ take 1000 allxs
  defaultMain
    [ bgroup "100"
        [ bench "func" $ nf prod (take 100 allxs)
        , bench "grad" $ nf grad_prod (take 100 allxs)
        , bench "both" $ nf both_prod (take 100 allxs)
        , bench "vec_both" $ nf grad_prod_aux vec100
        , bench "vec_both2" $ nf grad_prod_aux2 vec100
        ]
    , bgroup "200"
        [ bench "func" $ nf prod (take 200 allxs)
        , bench "grad" $ nf grad_prod (take 200 allxs)
        , bench "both" $ nf both_prod (take 200 allxs)
        , bench "vec_both" $ nf grad_prod_aux vec200
        , bench "vec_both2" $ nf grad_prod_aux2 vec200
        ]
    , bgroup "1000"
        [ bench "func" $ nf prod (take 1000 allxs)
        , bench "grad" $ nf grad_prod (take 1000 allxs)
        , bench "both" $ nf both_prod (take 1000 allxs)
        , bench "vec_both" $ nf grad_prod_aux vec1000
        , bench "vec_both2" $ nf grad_prod_aux2 vec1000
        ]
    ]

prod_aux :: forall r. (Num r, Data.Vector.Unboxed.Unbox r)
         => VecDualDelta r -> DeltaMonad r (DualDelta r)
prod_aux vec = do
  let f :: DualDelta r -> Int -> r -> DeltaMonad r (DualDelta r)
      f !acc !i !valX = do
        -- Micro-optimization, instead of calling just @var i vec@.
        -- But this also saves the noise of taking length of @fst vec@.
        -- The whole business with a pair of vectors is an optimization
        -- for gradient descent, which works fine there, but costs us
        -- some cycles here, even with micro-optimizations and hacks.
        let x = D valX (snd vec V.! i)
        acc *\ x
  V.ifoldM' f (scalar 1) $ fst vec

grad_prod_aux :: (Eq r, Num r, Data.Vector.Unboxed.Unbox r)
              => Domain r -> (Domain' r, r)
grad_prod_aux = df prod_aux

prod :: (Eq r, Num r, Data.Vector.Unboxed.Unbox r)
     => [r] -> r
prod l =
  let vec = V.fromList l
      (_, value) = grad_prod_aux vec
  in value

grad_prod :: (Eq r, Num r, Data.Vector.Unboxed.Unbox r)
          => [r] -> [r]
grad_prod l =
  let vec = V.fromList l
      (gradient, _) = grad_prod_aux vec
  in V.toList gradient

both_prod :: (Eq r, Num r, Data.Vector.Unboxed.Unbox r)
          => [r] -> ([r], r)
both_prod l =
  let vec = V.fromList l
      (gradient, value) = grad_prod_aux vec
  in (V.toList gradient, value)

-- This is a real speedup, side-stepping a part of the optimization
-- for gradients, but it's fragile and doesn't scale to more
-- complex expressions.
prod_aux2 :: forall r. (Num r, Data.Vector.Unboxed.Unbox r)
          => VecDualDelta r -> DeltaMonad r (DualDelta r)
prod_aux2 vec = do
  let f :: DualDelta r -> Int -> r -> DeltaMonad r (DualDelta r)
      f !acc !i !valX = do
        -- The ugliest possible hack.
        let x = D valX (Var $ DeltaId i)
        acc *\ x
  V.ifoldM' f (scalar 1) $ fst vec

grad_prod_aux2 :: (Eq r, Num r, Data.Vector.Unboxed.Unbox r)
               => Domain r -> (Domain' r, r)
grad_prod_aux2 = df prod_aux2

{-
-- This verifies that changing the nesting of multiplications doesn't matter.
prod_aux3 :: forall r. (Num r, Data.Vector.Unboxed.Unbox r)
          => VecDualDelta r -> DeltaMonad r (DualDelta r)
prod_aux3 vec = do
  let f :: DualDelta r -> Int -> r -> DeltaMonad r (DualDelta r)
      f !acc !i !valX = do
        -- Micro-optimization, instead of calling just @var i vec@.
        let x = D valX (snd vec V.! i)
        x *\ acc  -- !!!
  V.ifoldM' f (scalar 1) $ fst vec

grad_prod_aux3 :: (Eq r, Num r, Data.Vector.Unboxed.Unbox r)
               => Domain r -> (Domain' r, r)
grad_prod_aux3 = df prod_aux3
-}
