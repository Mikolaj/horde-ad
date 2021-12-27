module Main (main) where

import Prelude

import qualified Data.Vector.Generic as V
import           Test.Tasty
import           Test.Tasty.HUnit

import AD

main :: IO ()
main = defaultMain tests

dfShow :: (VecDualDelta -> DeltaImplementation (Dual Delta))
       -> [Float]
       -> ([Result], Float)
dfShow f deltaInput =
  let (results, value) = df f (V.fromList deltaInput)
  in (V.toList results, value)

gradDescShow :: Float
             -> (VecDualDelta -> DeltaImplementation (Dual Delta))
             -> [Float]
             -> Int
             -> ([Result], Float)
gradDescShow gamma f initVec n =
  let res = V.toList $ gradDesc gamma f (V.fromList initVec) !! n
  in (res, snd $ dfShow f res)

tests :: TestTree
tests = testGroup "Tests" [ dfTests
                          , gradDescTests
                          , xorTests
                          ]

fX :: VecDualDelta -> DeltaImplementation (Dual Delta)
fX vec = do
  let x = vec V.! 0
  return x

fX1Y :: VecDualDelta -> DeltaImplementation (Dual Delta)
fX1Y vec = do
  let x = vec V.! 0
      y = vec V.! 1
  x1 <- x +\ scalar 1
  x1 *\ y

fXXY :: VecDualDelta -> DeltaImplementation (Dual Delta)
fXXY vec = do
  let x = vec V.! 0
      y = vec V.! 1
  xy <- x *\ y
  x *\ xy

fXYplusZ :: VecDualDelta -> DeltaImplementation (Dual Delta)
fXYplusZ vec = do
  let x = vec V.! 0
      y = vec V.! 1
      z = vec V.! 2
  xy <- x *\ y
  xy +\ z

fXtoY :: VecDualDelta -> DeltaImplementation (Dual Delta)
fXtoY vec = do
  let x = vec V.! 0
      y = vec V.! 1
  x **\ y

freluX :: VecDualDelta -> DeltaImplementation (Dual Delta)
freluX vec = do
  let x = vec V.! 0
  reluAct x

fquad :: VecDualDelta -> DeltaImplementation (Dual Delta)
fquad vec = do
  let x = vec V.! 0
      y = vec V.! 1
  x2 <- x *\ x
  y2 <- y *\ y
  tmp <- x2 +\ y2
  tmp +\ scalar 5

dfTests :: TestTree
dfTests = testGroup "df application tests" $
  map (\(txt, f, v, expected) ->
        testCase txt $ dfShow f v @?= expected)
    [ ("fX", fX, [99], ([1.0],99.0))
    , ("fX1Y", fX1Y, [3, 2], ([2.0,4.0],8.0))
    , ("fXXY", fXXY, [3, 2], ([12.0,9.0],18.0))
    , ("fXYplusZ", fXYplusZ, [1, 2, 3], ([2.0,1.0,1.0],5.0))
    , ( "fXtoY", fXtoY, [0.00000000000001, 2]
      , ([2.0e-14,-3.2236188e-27],9.9999994e-29) )
    , ("fXtoY2", fXtoY, [1, 2], ([2.0,0.0],1.0))
    , ("freluX", freluX, [-1], ([0.0],0.0))
    , ("freluX2", freluX, [0], ([0.0],0.0))
    , ("freluX3", freluX, [0.0001], ([1.0],1.0e-4))
    , ("freluX4", freluX, [99], ([1.0],99.0))
    , ("fquad", fquad, [2, 3], ([4.0,6.0],18.0))
    ]

gradDescTests :: TestTree
gradDescTests = testGroup "simple gradDesc tests"
  [ testCase "0.1 30"
    $ gradDescShow 0.1 fquad [2, 3] 30
      @?= ([2.47588e-3,3.7138206e-3],5.00002)
  , testCase "0.01 30"
    $ gradDescShow 0.01 fquad [2, 3] 30
      @?= ([1.0909687,1.6364527],8.86819)
  , testCase "0.01 300"
    $ gradDescShow 0.01 fquad [2, 3] 300
      @?= ([4.665013e-3,6.9975173e-3],5.0000706)
  , testCase "0.01 300000"
    $ gradDescShow 0.01 fquad [2, 3] 300000
      @?= ([3.5e-44,3.5e-44],5.0)
  ]

scaleAddWithBias :: Dual Delta -> Dual Delta -> Int -> VecDualDelta
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
       -> Dual Delta -> Dual Delta -> Int -> VecDualDelta
       -> DeltaImplementation (Dual Delta)
neuron factivation x y ixWeight vec = do
  sc <- scaleAddWithBias x y ixWeight vec
  factivation sc

nnXor :: (Dual Delta -> DeltaImplementation (Dual Delta))
      -> Dual Delta -> Dual Delta -> VecDualDelta
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
      -> Float -> Float -> Float -> VecDualDelta
      -> DeltaImplementation (Dual Delta)
nnLoss factivation x y res vec = do
  r <- nnXor factivation (scalar x) (scalar y) vec
  lossXor r (scalar res)

setLoss :: (Dual Delta -> DeltaImplementation (Dual Delta))
        -> VecDualDelta
        -> DeltaImplementation (Dual Delta)
setLoss factivation vec = do
  n1 <- nnLoss factivation 0 0 0 vec
  n2 <- nnLoss factivation 0 1 1 vec
  n3 <- nnLoss factivation 1 0 1 vec
  n4 <- nnLoss factivation 1 1 0 vec
  n12 <- n1 +\ n2
  n34 <- n3 +\ n4
  n12 +\ n34

ws, ws2 :: [Float]
ws = let w = [0.37, 0.28, 0.19] in w ++ w ++ w
ws2 = let w = [-1.37, 2.28, -0.19] in w ++ w ++ w

xorTests :: TestTree
xorTests = testGroup "XOR neural net tests"
  [ testCase "0.1 tanhAct ws 500"
    $ gradDescShow 0.1 (setLoss tanhAct) ws 500
      @?= ([2.256964,2.255974,-0.6184605,0.94326925,0.94314164,-1.2784436,1.8050723,-1.992514,-0.70439947],1.205092e-2)
  , testCase "0.1 tanhAct ws 5000"
    $ gradDescShow 0.1 (setLoss tanhAct) ws 5000
      @?= ([2.4474483,2.4467785,-0.83506805,1.3046683,1.3045536,-1.8912246,2.3819222,-2.555036,-0.8139771],1.8422995e-4)
  , testCase "0.01 tanhAct ws2 50000"
    $ gradDescShow 0.01 (setLoss tanhAct) ws2 50000
      @?= ([-1.987227,2.576038,0.66793245,-1.7813855,2.2283037,-0.98668087,-2.1694314,2.1973305,2.9272888],2.1781538e-4)
  , testCase "0.01 reluAct ws 5000"
    $ gradDescShow 0.01 (setLoss reluAct) ws 5000  -- no cookie
      @?= ([0.18997861,0.14774865,0.2541552,0.2825405,0.21788016,0.22178593,8.9811325e-2,-6.0578037e-2,0.49060056],1.0)
  , testCase "0.1 reluAct ws2 50000"
    $ gradDescShow 0.1 (setLoss reluAct) ws2 50000  -- no cookie
      @?= ([-1.2425352,2.6025252,0.13252532,-1.5821311,1.7432425,-0.72675747,-1.7345629,1.9154371,-0.42541993],2.0)
  ]
