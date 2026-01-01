{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}
module Main where

import Control.Exception (bracket)
import Control.Monad (when)
import Data.Array.Internal qualified as OI
import Data.Array.Internal.RankedG qualified as RG
import Data.Array.Internal.RankedS qualified as RS
import Data.Vector.Storable qualified as VS
import Numeric.LinearAlgebra qualified as LA
import Test.Tasty.Bench
import Text.Show (showListWith)

import Data.Array.Nested
import Data.Array.Nested.Mixed (Mixed(M_Primitive), mliftPrim, mliftPrim2, toPrimitive)
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Ranked (liftRanked1, liftRanked2)
import Data.Array.Nested.Ranked.Shape
import Data.Array.Strided.Arith.Internal qualified as Arith
import Data.Array.XArray (XArray(..))


main :: IO ()
main = do
  let enable = False
  bracket (Arith.statisticsEnable enable)
          (\() -> do Arith.statisticsEnable False
                     when enable Arith.statisticsPrintAll)
          (\() -> main_tests)

main_tests :: IO ()
main_tests = defaultMain
  [bgroup "compare" tests_compare
  ,bgroup "dotprod" $
    let stridesOf (Ranked (toPrimitive -> M_Primitive _ (XArray (RS.A (RG.A _ (OI.T strides _ _)))))) = strides
        dotprodBench name (inp1, inp2) =
          let showSh l = showListWith (\n -> let ln = round (logBase 10 (fromIntegral n :: Double)) :: Int
                                             in if n > 1 && n == 10 ^ ln then showString ("1e" ++ show ln) else shows n)
                                      l ""
          in bench (name ++ " " ++ showSh (shrToList (rshape inp1)) ++
                      " str " ++ showSh (stridesOf inp1) ++ " " ++ showSh (stridesOf inp2)) $
               nf (\(a,b) -> rsumAllPrim (rdot1Inner a b)) (inp1, inp2)

        iota = riota @Double
    in
    [dotprodBench "dot 1D"
        (iota 10_000_000
        ,iota 10_000_000)
    ,dotprodBench "revdot"
        (rrev1 (iota 10_000_000)
        ,rrev1 (iota 10_000_000))
    ,dotprodBench "dot 2D"
        (rreshape (1000 :$: 10_000 :$: ZSR) (iota 10_000_000)
        ,rreshape (1000 :$: 10_000 :$: ZSR) (iota 10_000_000))
    ,dotprodBench "batched dot"
        (rreplicate (1000 :$: ZSR) (iota 10_000)
        ,rreplicate (1000 :$: ZSR) (iota 10_000))
    ,dotprodBench "transposed dot" $
        let (a, b) = (rreshape (1000 :$: 10_000 :$: ZSR) (iota 10_000_000)
                     ,rreshape (1000 :$: 10_000 :$: ZSR) (iota 10_000_000))
        in (rtranspose [1,0] a, rtranspose [1,0] b)
    ,dotprodBench "repdot" $
        let (a, b) = (rreplicate (1000 :$: ZSR) (iota 10_000)
                     ,rreplicate (1000 :$: ZSR) (iota 10_000))
        in (rtranspose [1,0] a, rtranspose [1,0] b)
    ,dotprodBench "matvec" $
        let (m, v) = (rreshape (1000 :$: 10_000 :$: ZSR) (iota 10_000_000)
                     ,iota 10_000)
        in (m, rreplicate (1000 :$: ZSR) v)
    ,dotprodBench "vecmat" $
        let (v, m) = (iota 1_000
                     ,rreshape (1000 :$: 10_000 :$: ZSR) (iota 10_000_000))
        in (rreplicate (10_000 :$: ZSR) v, rtranspose [1,0] m)
    ,dotprodBench "matmat" $
       let (n,m,k) = (100, 100, 1000)
           (m1, m2) = (rreshape (n :$: m :$: ZSR) (iota (n*m))
                      ,rreshape (m :$: k :$: ZSR) (iota (m*k)))
       in (rtranspose [1,0] (rreplicate (k :$: ZSR) m1)
          ,rreplicate (n :$: ZSR) (rtranspose [1,0] m2))
    ,dotprodBench "matmatT" $
       let (n,m,k) = (100, 100, 1000)
           (m1, m2) = (rreshape (n :$: m :$: ZSR) (iota (n*m))
                      ,rreshape (k :$: m :$: ZSR) (iota (m*k)))
       in (rtranspose [1,0] (rreplicate (k :$: ZSR) m1)
          ,rreplicate (n :$: ZSR) m2)
    ]
  ,bgroup "orthotope"
    [bench "normalize [1e6]" $
      let n = 1_000_000
      in nf (\a -> RS.normalize a)
            (RS.rev [0] (RS.iota @Double n))
    ,bench "normalize noop [1e6]" $
      let n = 1_000_000
      in nf (\a -> RS.normalize a)
            (RS.rev [0] (RS.rev [0] (RS.iota @Double n)))
    ]
  ,bgroup "misc"
    [let n = 1000
         k = 1000
     in bgroup ("fusion [" ++ show k ++ "]*" ++ show n)
      [bench "sum (concat)" $
        nf (\as -> VS.sum (VS.concat as))
           (replicate n (VS.enumFromTo (1::Int) k))
      ,bench "sum (force (concat))" $
        nf (\as -> VS.sum (VS.force (VS.concat as)))
              (replicate n (VS.enumFromTo (1::Int) k))]
    ,bgroup "concat"
      [bgroup "N"
        [bgroup "hmatrix"
          [bench ("LA.vjoin [500]*1e" ++ show ni) $
            let n = 10 ^ ni
                k = 500
            in nf (\as -> LA.vjoin as)
                  (replicate n (VS.enumFromTo (1::Int) k))
          | ni <- [1::Int ..5]]
        ,bgroup "vectorStorable"
          [bench ("VS.concat [500]*1e" ++ show ni) $
            let n = 10 ^ ni
                k = 500
            in nf (\as -> VS.concat as)
                  (replicate n (VS.enumFromTo (1::Int) k))
          | ni <- [1::Int ..5]]
        ]
      ,bgroup "K"
        [bgroup "hmatrix"
          [bench ("LA.vjoin [1e" ++ show ki ++ "]*500") $
            let n = 500
                k = 10 ^ ki
            in nf (\as -> LA.vjoin as)
                  (replicate n (VS.enumFromTo (1::Int) k))
          | ki <- [1::Int ..5]]
        ,bgroup "vectorStorable"
          [bench ("VS.concat [1e" ++ show ki ++ "]*500") $
            let n = 500
                k = 10 ^ ki
            in nf (\as -> VS.concat as)
                  (replicate n (VS.enumFromTo (1::Int) k))
          | ki <- [1::Int ..5]]
        ]
      ]
    ,bench "ixxFromLinear 10000x" $
      let n = 10000
          sh0 = SUnknown 10 :$% SUnknown 10 :$% SUnknown 10 :$% SUnknown 10 :$% SUnknown 10 :$% ZSX
      in nf (\sh -> [ixxFromLinear @Int sh i | i <- [1..n]]) sh0
    ,bench "ixxFromLinear 1x" $
      let sh0 = SUnknown 10 :$% SUnknown 10 :$% SUnknown 10 :$% SUnknown 10 :$% SUnknown 10 :$% ZSX
      in nf (\sh -> ixxFromLinear @Int sh 1234) sh0
    ,bench "shxEnum" $
      let sh0 = SUnknown 10 :$% SUnknown 10 :$% SUnknown 10 :$% SUnknown 10 :$% SUnknown 10 :$% ZSX
      in nf (\sh -> shxEnum sh) sh0
    ]
  ]

tests_compare :: [Benchmark]
tests_compare =
  let n = 1_000_000 in
  [bgroup "Num"
    [bench "sum(+) Double [1e6]" $
      nf (\(a, b) -> runScalar (rsumOuter1Prim (liftRanked2 (mliftPrim2 (+)) a b)))
         (riota @Double n, riota n)
    ,bench "sum(*) Double [1e6]" $
      nf (\(a, b) -> runScalar (rsumOuter1Prim (liftRanked2 (mliftPrim2 (*)) a b)))
         (riota @Double n, riota n)
    ,bench "sum(/) Double [1e6]" $
      nf (\(a, b) -> runScalar (rsumOuter1Prim (liftRanked2 (mliftPrim2 (/)) a b)))
         (riota @Double n, riota n)
    ,bench "sum(**) Double [1e6]" $
      nf (\(a, b) -> runScalar (rsumOuter1Prim (liftRanked2 (mliftPrim2 (**)) a b)))
         (riota @Double n, riota n)
    ,bench "sum(sin) Double [1e6]" $
      nf (\a -> runScalar (rsumOuter1Prim (liftRanked1 (mliftPrim sin) a)))
         (riota @Double n)
    ,bench "sum Double [1e6]" $
      nf (\a -> runScalar (rsumOuter1Prim a))
         (riota @Double n)
    ]
  ,bgroup "NumElt"
    [bench "sum(+) Double [1e6]" $
      nf (\(a, b) -> runScalar (rsumOuter1Prim (a + b)))
         (riota @Double n, riota n)
    ,bench "sum(*) Double [1e6]" $
      nf (\(a, b) -> runScalar (rsumOuter1Prim (a * b)))
         (riota @Double n, riota n)
    ,bench "sum(/) Double [1e6]" $
      nf (\(a, b) -> runScalar (rsumOuter1Prim (a / b)))
         (riota @Double n, riota n)
    ,bench "sum(**) Double [1e6]" $
      nf (\(a, b) -> runScalar (rsumOuter1Prim (a ** b)))
         (riota @Double n, riota n)
    ,bench "sum(sin) Double [1e6]" $
      nf (\a -> runScalar (rsumOuter1Prim (sin a)))
         (riota @Double n)
    ,bench "sum Double [1e6]" $
      nf (\a -> runScalar (rsumOuter1Prim a))
         (riota @Double n)
    ,bench "sum(*) Double [1e6] stride 1; -1" $
      nf (\(a, b) -> runScalar (rsumOuter1Prim (a * b)))
         (riota @Double n, rrev1 (riota n))
    ,bench "dotprod Float [1e6]" $
      nf (\(a, b) -> rdot a b)
         (riota @Float n, riota @Float n)
    ,bench "dotprod Float [1e6] stride 1; -1" $
      nf (\(a, b) -> rdot a b)
         (riota @Float n, rrev1 (riota @Float n))
    ,bench "dotprod Double [1e6]" $
      nf (\(a, b) -> rdot a b)
         (riota @Double n, riota @Double n)
    ,bench "dotprod Double [1e6] stride 1; -1" $
      nf (\(a, b) -> rdot a b)
         (riota @Double n, rrev1 (riota @Double n))
    ]
  ,bgroup "hmatrix"
    [bench "sum(+) Double [1e6]" $
      nf (\(a, b) -> LA.sumElements (a + b))
         (LA.linspace @Double n (0.0, fromIntegral (n - 1))
         ,LA.linspace @Double n (0.0, fromIntegral (n - 1)))
    ,bench "sum(*) Double [1e6]" $
      nf (\(a, b) -> LA.sumElements (a * b))
         (LA.linspace @Double n (0.0, fromIntegral (n - 1))
         ,LA.linspace @Double n (0.0, fromIntegral (n - 1)))
    ,bench "sum(/) Double [1e6]" $
      nf (\(a, b) -> LA.sumElements (a / b))
         (LA.linspace @Double n (0.0, fromIntegral (n - 1))
         ,LA.linspace @Double n (0.0, fromIntegral (n - 1)))
    ,bench "sum(**) Double [1e6]" $
      nf (\(a, b) -> LA.sumElements (a ** b))
         (LA.linspace @Double n (0.0, fromIntegral (n - 1))
         ,LA.linspace @Double n (0.0, fromIntegral (n - 1)))
    ,bench "sum(sin) Double [1e6]" $
      nf (\a -> LA.sumElements (sin a))
         (LA.linspace @Double n (0.0, fromIntegral (n - 1)))
    ,bench "sum Double [1e6]" $
      nf (\a -> LA.sumElements a)
         (LA.linspace @Double n (0.0, fromIntegral (n - 1)))
    ,bench "dotprod Float [1e6]" $
      nf (\(a, b) -> a LA.<.> b)
         (LA.linspace @Double n (0.0, fromIntegral (n - 1))
         ,LA.linspace @Double n (fromIntegral (n - 1), 0.0))
    ,bench "dotprod Double [1e6]" $
      nf (\(a, b) -> a LA.<.> b)
         (LA.linspace @Double n (0.0, fromIntegral (n - 1))
         ,LA.linspace @Double n (fromIntegral (n - 1), 0.0))
    ]
  ]
