{-# LANGUAGE RankNTypes #-}
module Main (main) where

import Prelude

import qualified Data.Vector
import qualified Data.Vector.Generic as V
import           Numeric.AD.Mode.Reverse hiding (diff)
import           Test.Tasty
import           Test.Tasty.HUnit

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Ad Tests" [ adXorTests
                             ]

type Domain r = Data.Vector.Vector r
-- Bummer. Unboxed vectors can't be Traversable due to their constraint.
-- type Domain r = Data.Vector.Unboxed.Vector r

type Domain' r = Domain r

gradDesc :: forall r . (Ord r, Floating r)  -- Data.Vector.Unboxed.Unbox r
         => r
         -> (forall k. (Ord k, Floating k) => Domain k -> k)
         -> Int
         -> Domain r
         -> Domain' r
gradDesc gamma f n0 vecInitial0 = go n0 vecInitial0 where
  go :: Int -> Domain r -> Domain' r
  go 0 !vecInitial = vecInitial
  go n vecInitial =
    let combine i r = i - gamma * r
        v = gradWith combine f vecInitial
    in go (pred n) v

gradDescShow :: Float
             -> (forall k. (Ord k, Floating k) => Domain k -> k)
             -> [Float]
             -> Int
             -> ([Float], Float)
gradDescShow gamma f initVec n =
  let res = V.toList $ gradDesc gamma f n (V.fromList initVec)
      (v, _) = grad' f $ V.fromList res
                 -- overhead to match that in the original tests
  in (res, v)

var :: Int -> Domain r -> r
var i vec = vec V.! i

tanhAct :: Floating r
        => r -> r
tanhAct = tanh

reluAct :: (Num r, Ord r)
        => r -> r
reluAct = max 0

scaleAddWithBias :: Num r
                 => r -> r -> Int
                 -> Domain r
                 -> r
scaleAddWithBias x y ixWeight vec =
  let wx = var ixWeight vec
      wy = var (ixWeight + 1) vec
      bias = var (ixWeight + 2) vec
      sx = x * wx
      sy = y * wy
      sxy = sx + sy
  in sxy + bias

neuron :: Num r
       => (r -> r)
       -> r -> r -> Int -> Domain r
       -> r
neuron factivation x y ixWeight vec =
  let sc = scaleAddWithBias x y ixWeight vec
  in factivation sc

nnXor :: Num r
      => (r -> r)
      -> r -> r -> Domain r
      -> r
nnXor factivation x y vec =
  let n1 = neuron factivation x y 0 vec
      n2 = neuron factivation x y 3 vec
  in neuron factivation n1 n2 6 vec

lossXor :: Num r
        => r -> r -> r
lossXor u v =
  let diff = u - v
  in diff * diff

nnLoss :: Num r
       => (r -> r)
       -> r -> r -> r -> Domain r
       -> r
nnLoss factivation x y res vec =
  let r = nnXor factivation x y vec
  in lossXor r res

setLoss :: Num r
        => (r -> r)
        -> Domain r
        -> r
setLoss factivation vec =
  let n1 = nnLoss factivation 0 0 0 vec
      n2 = nnLoss factivation 0 1 1 vec
      n3 = nnLoss factivation 1 0 1 vec
      n4 = nnLoss factivation 1 1 0 vec
      n12 = n1 + n2
      n34 = n3 + n4
  in n12 + n34

ws, ws2 :: [Float]
ws = let w = [0.37, 0.28, 0.19] in w ++ w ++ w
ws2 = let w = [-1.37, 2.28, -0.19] in w ++ w ++ w

-- The values below are copied from the other tests to compare results
-- They seem to be pretty close.
adXorTests :: TestTree
adXorTests = testGroup "XOR neural net tests (3 errors are expected)"
  [ testCase "0.1 tanhAct ws 500"
    $ gradDescShow 0.1 (setLoss tanhAct) ws 500
      @?= ([2.256964,2.255974,-0.6184606,0.943269,0.9431414,-1.2784432,1.805072,-1.9925138,-0.704399],1.20509565e-2)
  , testCase "0.1 tanhAct ws 5000"
    $ gradDescShow 0.1 (setLoss tanhAct) ws 5000
      @?= ([2.4474504,2.4467778,-0.8350617,1.3046894,1.3045748,-1.8912042,2.3819275,-2.5550227,-0.8139653],1.8524402e-4)
  , testCase "0.01 tanhAct ws2 50000"
    $ gradDescShow 0.01 (setLoss tanhAct) ws2 50000
      @?= ([-1.9872262,2.576039,0.66793317,-1.7813873,2.2283037,-0.9866766,-2.1694322,2.1973324,2.9272876],2.1781659e-4)
  , testCase "0.01 reluAct ws 5000"
    $ gradDescShow 0.01 (setLoss reluAct) ws 5000  -- no cookie
      @?= ([0.18997861,0.14774871,0.25415534,0.28254044,0.21788013,0.22178599,8.981165e-2,-6.05783e-2,0.49060053],1.0)
  , testCase "0.1 reluAct ws2 50000"
    $ gradDescShow 0.1 (setLoss reluAct) ws2 50000  -- no cookie
      @?= ([-1.2425352,2.6025252,0.13252532,-1.5821311,1.7432425,-0.72675747,-1.7345629,1.9154371,-0.42541993],2.0)
  ]
