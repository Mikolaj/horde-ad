module Main (main) where

import Prelude

import           Criterion.Main
import qualified Data.Vector
import qualified Data.Vector.Generic as V
import           System.Random

import Numeric.AD.Mode.Reverse.Double hiding (diff)

main :: IO ()
main = do
  let allxs = map (\x -> x + 0.55) $ randoms (mkStdGen 42) :: [Double]
      vec100 = V.fromList $ take 100 allxs
      vec200 = V.fromList $ take 200 allxs
      vec1000 = V.fromList $ take 1000 allxs
  defaultMain
    [ bgroup "100"
        [ bench "func" $ nf list_prod (take 100 allxs)
        , bench "grad" $ nf list_grad_prod (take 100 allxs)
        , bench "vec_grad" $ nf grad_prod_aux vec100
        ]
    , bgroup "200"
        [ bench "func" $ nf list_prod (take 200 allxs)
        , bench "grad" $ nf list_grad_prod (take 200 allxs)
        , bench "vec_grad" $ nf grad_prod_aux vec200
        ]
    , bgroup "1000"
        [ bench "func" $ nf list_prod (take 1000 allxs)
        , bench "grad" $ nf list_grad_prod (take 1000 allxs)
        , bench "vec_grad" $ nf grad_prod_aux vec1000
        ]
    ]

list_prod :: Num r => [r] -> r
list_prod [x] = x
list_prod (x : xs) = x * list_prod xs

list_grad_prod :: [Double] -> [Double]
list_grad_prod = grad list_prod

-- This benchmark shows that there is only slowdown from using vectors
-- with the ad library. The Traversable data structure is probably
-- converted to a list ASAP. Conversion of lists to lists is free,
-- so that's the best structure to use.
prod_aux :: forall r. Num r
         => Data.Vector.Vector r -> r
prod_aux vec = V.foldl1' (*) vec

grad_prod_aux :: Data.Vector.Vector Double -> Data.Vector.Vector Double
grad_prod_aux = grad prod_aux
