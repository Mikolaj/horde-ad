module Main (main) where

import Prelude

import qualified Data.Vector as V

import AD

main :: IO ()
main = mapM_ print result

fX :: Vec (Dual Delta) -> DeltaImplementation (Dual Delta)
fX vec = do
  let x = vec V.! 0
  return x

fX1Y :: Vec (Dual Delta) -> DeltaImplementation (Dual Delta)
fX1Y vec = do
  let x = vec V.! 0
      y = vec V.! 1
  x1 <- x +\ scalar 1
  x1 *\ y

fXXY :: Vec (Dual Delta) -> DeltaImplementation (Dual Delta)
fXXY vec = do
  let x = vec V.! 0
      y = vec V.! 1
  xy <- x *\ y
  x *\ xy

fXYplusZ :: Vec (Dual Delta) -> DeltaImplementation (Dual Delta)
fXYplusZ vec = do
  let x = vec V.! 0
      y = vec V.! 1
      z = vec V.! 2
  xy <- x *\ y
  xy +\ z

fXtoY :: Vec (Dual Delta) -> DeltaImplementation (Dual Delta)
fXtoY vec = do
  let x = vec V.! 0
      y = vec V.! 1
  x **\ y

freluX :: Vec (Dual Delta) -> DeltaImplementation (Dual Delta)
freluX vec = do
  let x = vec V.! 0
  reluAct x

fquad :: Vec (Dual Delta) -> DeltaImplementation (Dual Delta)
fquad vec = do
  let x = vec V.! 0
      y = vec V.! 1
  x2 <- x *\ x
  y2 <- y *\ y
  tmp <- x2 +\ y2
  tmp +\ scalar 5

scaleAddWithBias :: Dual Delta -> Dual Delta -> Int -> Vec (Dual Delta)
                 -> DeltaImplementation (Dual Delta)
scaleAddWithBias x y ixWeight vec = do
  let wx = vec V.! ixWeight
      wy = vec V.! (ixWeight + 1)
      bias = vec V.! (ixWeight + 2)
  sx <- x *\ wx
  sy <- y *\ wy
  sxy <- sx +\ sy
  sxy +\ bias

neuron :: (Dual Delta -> DeltaImplementation (Dual Delta))
       -> Dual Delta -> Dual Delta -> Int -> Vec (Dual Delta)
       -> DeltaImplementation (Dual Delta)
neuron factivation x y ixWeight vec = do
  sc <- scaleAddWithBias x y ixWeight vec
  factivation sc

nnXor :: (Dual Delta -> DeltaImplementation (Dual Delta))
      -> Dual Delta -> Dual Delta -> Vec (Dual Delta)
      -> DeltaImplementation (Dual Delta)
nnXor factivation x y vec = do
  n1 <- neuron factivation x y 0 vec
  n2 <- neuron factivation x y 3 vec
  neuron factivation n1 n2 6 vec

lossXor :: Dual Delta -> Dual Delta -> DeltaImplementation (Dual Delta)
lossXor u v = do
  diff <- u -\ v
  diff *\ diff

nnLoss :: (Dual Delta -> DeltaImplementation (Dual Delta))
      -> Float -> Float -> Float -> Vec (Dual Delta)
      -> DeltaImplementation (Dual Delta)
nnLoss factivation x y res vec = do
  r <- nnXor factivation (scalar x) (scalar y) vec
  lossXor r (scalar res)

setLoss :: (Dual Delta -> DeltaImplementation (Dual Delta))
        -> Vec (Dual Delta)
        -> DeltaImplementation (Dual Delta)
setLoss factivation vec = do
  n1 <- nnLoss factivation 0 0 0 vec
  n2 <- nnLoss factivation 0 1 1 vec
  n3 <- nnLoss factivation 1 0 1 vec
  n4 <- nnLoss factivation 1 1 0 vec
  n12 <- n1 +\ n2
  n34 <- n3 +\ n4
  n12 +\ n34

initWeights, initWeights2 :: Vec Float
initWeights = let w = [0.37, 0.28, 0.19] in V.fromList $ w ++ w ++ w
initWeights2 = let w = [-1.37, 2.28, -0.19] in V.fromList $ w ++ w ++ w

result :: [(Vec Result, Float)]
result =
  map (\(f, v) -> df f v)
    [ (fX, V.fromList [99])  -- 1
    , (fX1Y, V.fromList [3, 2])  -- 2, 4
    , (fXXY, V.fromList [3, 2])  -- 12, 9
    , (fXYplusZ, V.fromList [1, 2, 3])  -- 2, 1, 1
    , (fXtoY, V.fromList [0.00000000000001, 2])  -- ~0, ~0
    , (fXtoY, V.fromList [1, 2])  -- 2, 0
    , (freluX, V.fromList [-1])  -- 0
    , (freluX, V.fromList [0])  -- ? (0)
    , (freluX, V.fromList [0.0001])  -- 1
    , (freluX, V.fromList [99])  -- 1
    , (fquad, V.fromList [2, 3])  -- 4, 6
    ]
  ++ [ gradDescShow 0.1 fquad (V.fromList [2, 3]) 30
         -- 2.47588e-3, 3.7138206e-3
     , gradDescShow 0.01 fquad (V.fromList [2, 3]) 30
     , gradDescShow 0.01 fquad (V.fromList [2, 3]) 300
     , gradDescShow 0.01 fquad (V.fromList [2, 3]) 300000
         -- 3.5e-44, 3.5e-44
     , gradDescShow 0.1 (setLoss tanhAct) initWeights 500  -- 1.205092e-2
     , gradDescShow 0.1 (setLoss tanhAct) initWeights 5000  -- 1.8422995e-4
     , gradDescShow 0.01 (setLoss tanhAct) initWeights2 5000
     , gradDescShow 0.01 (setLoss reluAct) initWeights 5000  -- no cookie
     , gradDescShow 0.1 (setLoss reluAct) initWeights2 5000  -- no cookie
     ]
