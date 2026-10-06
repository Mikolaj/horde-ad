# vector issue comment: Storable `foldl'` allocates the thunk of the read for every element when it cannot inline its function

Posted 2026-10-06 as [a comment][comment] on [vector issue 570][570]; this file stays as the record of the comment, the text from "The lazy read also costs" down being the body as posted. The prose is ASD-STE100 Simplified Technical English, as the issue's is. It records a second consumer of the defect, found by the specialisation test on orthotope's `pr-mikolaj-toVectorListT` branch, where Storable `reduce` allocates 56 bytes an element more than boxed `reduce` and the test allows that excess until the issue is fixed. The maintainer reproduced the issue and confirmed the proposed fix on 2026-10-04, so the comment adds a case and asks for nothing.

The lazy read also costs 40 bytes for each element in `foldl'`, if `foldl'` cannot inline the function that it folds with. For example, this occurs when a client specialises an `INLINABLE` function that gets the fold function from its caller. The table gives the bytes that one `foldl' (+) 0` over one million `Double`s allocates, divided by the length, when the fold function is an argument of a `NOINLINE` function. The results are the same with GHC 9.6.7, 9.8.4, 9.10.3, 9.12.4, 9.14.1 and HEAD 10.1.20260918, at `-O1` and at `-O2`.

| Vector | Bytes per element |
|---|---|
| Storable | 72 |
| Unboxed | 32 |
| boxed | 16 |
| Storable, read forced | 32 |

The fold function is not known, so the Unboxed fold allocates a `D#` box for each element and one for each result, and the boxed fold allocates a box for each result. The Storable fold allocates 40 bytes more than the Unboxed fold: the thunk of the read. The last line of the program forces the read, as the proposed fix does, and then the Storable fold allocates the same as the Unboxed fold.

## Steps to reproduce

1. Save the program below as `Repro.hs`.

2. Run it. To select a compiler, add `-w ghc-VERSION`. For GHC 9.14.1 and HEAD, I also added `--allow-newer=base,ghc-prim,ghc-bignum,template-haskell,containers`.

```
cabal run -v0 Repro.hs
```

3. The output is:

```
Storable foldl'    72.0 bytes per element
Unboxed foldl'     32.0 bytes per element
boxed foldl'       16.0 bytes per element
Storable, strict   32.0 bytes per element
```

```haskell
{- cabal:
build-depends: base, vector ==0.13.2.0, vector-stream ==0.1.0.1
ghc-options: -O1
-}
-- Reproducer: a Storable foldl' whose function it cannot inline allocates
-- a thunk for every element; Unboxed's does not.
--
-- Run: cabal run -v0 Repro.hs
--
-- The last line folds the same Storable vector through a stream whose
-- element read is forced, as Data.Vector.Primitive's is.
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import Control.Exception (evaluate)
import Data.Stream.Monadic (Stream (..), Step (..))
import qualified Data.Stream.Monadic as S
import Data.Vector.Fusion.Util (unId)
import qualified Data.Vector as V
import qualified Data.Vector.Storable as VS
import qualified Data.Vector.Unboxed as VU
import System.Mem (getAllocationCounter)
import Text.Printf (printf)

-- The stream of a Storable vector, with the element read forced.
strictStream :: Monad m => VS.Vector Double -> Stream m Double
strictStream v = Stream step 0
  where
    step i
      | i >= VS.length v = return Done
      | otherwise = let !x = VS.unsafeIndex v i in return (Yield x (i + 1))

-- Folds whose function is an argument, so that the fold cannot inline it.
{-# NOINLINE foldS #-}
foldS, foldStrict :: (Double -> Double -> Double) -> VS.Vector Double -> Double
foldS f = VS.foldl' f 0
{-# NOINLINE foldStrict #-}
foldStrict f v = unId (S.foldl' f 0 (strictStream v))

{-# NOINLINE foldU #-}
foldU :: (Double -> Double -> Double) -> VU.Vector Double -> Double
foldU f = VU.foldl' f 0

{-# NOINLINE foldB #-}
foldB :: (Double -> Double -> Double) -> V.Vector Double -> Double
foldB f = V.foldl' f 0

-- Bytes allocated, per element, by one fold with (+).
perElement :: String -> ((Double -> Double -> Double) -> v -> Double) -> v -> Int
           -> IO ()
perElement name fold v n = do
  c0 <- getAllocationCounter
  _ <- evaluate (fold (+) v)
  c1 <- getAllocationCounter
  printf "%-17s %5.1f bytes per element\n" name
    (fromIntegral (c0 - c1) / fromIntegral n :: Double)

main :: IO ()
main = do
  let n = 1000000
  s <- evaluate (VS.generate n fromIntegral)
  u <- evaluate (VU.generate n fromIntegral)
  b <- evaluate (V.generate n fromIntegral)
  _ <- evaluate (V.sum b)
  perElement "Storable foldl'" foldS s n
  perElement "Unboxed foldl'" foldU u n
  perElement "boxed foldl'" foldB b n
  perElement "Storable, strict" foldStrict s n
```

[570]: https://github.com/haskell/vector/issues/570
[comment]: https://github.com/haskell/vector/issues/570#issuecomment-6015332651
