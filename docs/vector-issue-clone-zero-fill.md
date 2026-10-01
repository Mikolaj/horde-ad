# vector issue: `force`, `modify` and `(//)` fill new memory with zeros before they copy into it

Filed 2026-10-01 as [vector issue 571][571]; this file stays as the filed record, the text from "## Summary" down being the filed body. Title: **Generic `clone` fills its new vector with zeros before it copies into it, so `force`, `modify` and `(//)` write each element two times**. The prose is ASD-STE100 Simplified Technical English. The reproducer is a cabal script and needs only `vector`. The problem was found while measuring the copy that orthotope's `normalize` makes of an array that is one block of a longer vector, on orthotope's `pr-mikolaj-bugfixes` branch: `normalize` uses `concat` of one slice, which was faster than `force`. A search of the vector issues and pull requests for `force`, `clone`, `unsafeNew`, `basicInitialize`, `memset` and zero initialisation found nothing about this; [#511][511] and [#513][513] are about the documentation of `force`, and [#30][30] reports that `new` once gave uninitialised memory. A second problem was suspected and is not in the body: that the rewrite rules `clone/new` and `take/new` could let `force` return a slice of a larger fresh vector. A test of `force` and `concat` after `take`, `drop`, `slice` and `unsafeSlice` of a vector from `create` found no case that keeps the larger vector alive. A workaround is known and is in the body.

## Summary

`force` copies a vector, so that a slice does not keep a larger vector alive. For `Data.Vector.Storable` and `Data.Vector.Unboxed` vectors of `Double`s, `force` takes 1.6 times as long as `concat` of a list of one vector at 100000 elements, and 4.4 times as long at 1000000 elements. The two functions make the same copy. `modify` with one write and `(//)` with one update take as long as `force`.

The table gives the time of one call, in microseconds, on GHC 9.12.4, for a slice of a vector of `Double`s. Each value is the mean of two runs of the program in "Steps to reproduce". On GHC 9.6.7, 9.8.4, 9.10.3 and 9.14.1, the times are the same within 15 percent.

| | Storable, 100000 | Storable, 1000000 | Unboxed, 100000 | Unboxed, 1000000 |
|---|---|---|---|---|
| `force` | 22.3 | 646 | 21.6 | 650 |
| `concat [v]` | 14.1 | 147 | 13.8 | 149 |
| `new`, then `copy` | 22.0 | 642 | 21.5 | 641 |
| `unsafeNew`, then `copy` | 13.9 | 148 | 13.8 | 144 |
| `(//)`, one update | 21.4 | 659 | | |
| `modify`, one write | 21.5 | 648 | | |

The cause is `clone` in `Data.Vector.Generic` ([lines 2649 to 2655][clone]):

```haskell
clone v = v `seq` New.create (
  do
    mv <- M.new (basicLength v)
    unsafeCopy mv v
    return mv)
```

`M.new` calls `basicInitialize` ([lines 468 to 471 of Data/Vector/Generic/Mutable.hs][new]), which fills the new memory with zeros for Storable and Primitive vectors. Then `unsafeCopy` writes each element again. In the table, `new` then `copy` takes as long as `force`, and `unsafeNew` then `copy` takes as long as `concat`. `thaw` ([lines 2475 to 2480][thaw]) and the mutable `clone` ([lines 516 to 521 of Data/Vector/Generic/Mutable.hs][mclone]) make the same copy into memory from `M.unsafeNew`, and do not fill it first.

The generic `clone` is under `force` ([lines 825 to 829][force]), `modify` and `modifyWithBundle` ([lines 1054 to 1064][modify]). `modifyWithBundle` is under `(//)`, `update`, `update_`, `accum`, `accumulate`, `accumulate_` and their unsafe forms. Boxed vectors do not have the problem, because their `basicInitialize` does nothing.

The fill itself is as fast as `fillBytes` from base: `M.new` of 1000000 `Double`s takes 267 microseconds, and `M.unsafeNew` then `fillBytes` takes the same time.

## Proposed fix

In the generic `clone`, use `M.unsafeNew`, as `thaw` and the mutable `clone` do. `unsafeCopy` writes each element of the new vector, so no element is read before it is written. This is the change to vector-0.13.2.0 that I tested:

```diff
--- a/vector/src/Data/Vector/Generic.hs
+++ b/vector/src/Data/Vector/Generic.hs
@@ -2637,7 +2637,7 @@
 {-# INLINE_FUSED clone #-}
 clone v = v `seq` New.create (
   do
-    mv <- M.new (basicLength v)
+    mv <- M.unsafeNew (basicLength v)
     unsafeCopy mv v
     return mv)
 
```

With this change, on GHC 9.12.4, `force`, `modify` and `(//)` take as long as `concat`. At 100000 and 1000000 elements, Storable `force` takes 14.4 and 142 microseconds, `(//)` 13.9 and 146, `modify` 13.9 and 146, and Unboxed `force` 13.9 and 146. With the change, all 2808 tests of `vector-tests-O2` and all 14 tests of `vector-inspection` pass on GHC 9.10.3. On GHC 9.12.4 the test suites do not build, because no version of `doctest` in their bounds supports it.

Until a fix is released, `concat [v]` makes the copy that `force v` makes, without the fill.

## Steps to reproduce

1. Save the program below as `Repro.hs`.

2. Run it. To select a compiler, add `-w ghc-VERSION`.

```
cabal run -v0 Repro.hs
```

3. On GHC 9.12.4, the output is:

```
n =  100000  Storable force                 22.2 us     22.4 us
n =  100000  Storable concat                13.8 us     14.3 us
n =  100000  Storable new, copy             21.4 us     22.5 us
n =  100000  Storable unsafeNew, copy       13.7 us     14.1 us
n =  100000  Storable (//), one update      21.4 us     21.4 us
n =  100000  Storable modify, one write     21.3 us     21.7 us
n =  100000  Unboxed force                  21.4 us     21.7 us
n =  100000  Unboxed concat                 13.8 us     13.8 us
n =  100000  Unboxed new, copy              21.4 us     21.6 us
n =  100000  Unboxed unsafeNew, copy        13.8 us     13.8 us
n = 1000000  Storable force                641.7 us    650.2 us
n = 1000000  Storable concat               143.7 us    150.4 us
n = 1000000  Storable new, copy            640.9 us    642.9 us
n = 1000000  Storable unsafeNew, copy      143.6 us    152.2 us
n = 1000000  Storable (//), one update     660.3 us    658.5 us
n = 1000000  Storable modify, one write    654.7 us    641.4 us
n = 1000000  Unboxed force                 664.1 us    636.1 us
n = 1000000  Unboxed concat                153.4 us    145.3 us
n = 1000000  Unboxed new, copy             637.4 us    644.8 us
n = 1000000  Unboxed unsafeNew, copy       145.6 us    142.6 us
```

```haskell
{- cabal:
build-depends: base, vector ==0.13.2.0
ghc-options: -O2
-}
-- Reproducer: force fills its new vector with zeros before it copies, so
-- it takes longer than concat of a list of one vector, which makes the
-- same copy; (//) and modify copy through the same clone as force.
--
-- Run: cabal run -v0 Repro.hs
--
-- The rows "new, copy" and "unsafeNew, copy" are the two halves of
-- force: a copy into memory from new, which fills it with zeros first,
-- and a copy into memory from unsafeNew.  Each case runs twice, the
-- second time in the reverse order.
module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (forM, forM_)
import qualified Data.Vector.Storable as VS
import qualified Data.Vector.Storable.Mutable as VSM
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Unboxed.Mutable as VUM
import GHC.Clock (getMonotonicTime)
import Text.Printf (printf)

-- Microseconds for one call of f, evaluated to WHNF, the mean of reps
-- calls.
time :: Int -> (Int -> a) -> IO Double
time reps f = do
  t0 <- getMonotonicTime
  forM_ [1 .. reps] $ \ i -> evaluate (f (i `mod` 2))
  t1 <- getMonotonicTime
  return ((t1 - t0) / fromIntegral reps * 1e6)

main :: IO ()
main = forM_ [100000, 1000000] $ \ n -> do
  let xs = [1 .. fromIntegral (3 * n)] :: [Double]
      vs = VS.fromList xs
      vu = VU.fromList xs
      reps = 200000000 `div` n
      -- A slice of n elements of the vector, at offset n or n + 1.
      sl o = VS.slice (n + o) n vs
      su o = VU.slice (n + o) n vu
      cases =
        [ ("Storable force", \ r -> time r (\ o -> VS.force (sl o)))
        , ("Storable concat", \ r -> time r (\ o -> VS.concat [sl o]))
        , ("Storable new, copy", \ r -> time r (\ o -> VS.create (do
              m <- VSM.new n; VS.copy m (sl o); return m)))
        , ("Storable unsafeNew, copy", \ r -> time r (\ o -> VS.create (do
              m <- VSM.unsafeNew n; VS.copy m (sl o); return m)))
        , ("Storable (//), one update", \ r -> time r (\ o -> sl o VS.// [(0, 0)]))
        , ("Storable modify, one write", \ r -> time r (\ o -> VS.modify (\ m -> VSM.write m 0 0) (sl o)))
        , ("Unboxed force", \ r -> time r (\ o -> VU.force (su o)))
        , ("Unboxed concat", \ r -> time r (\ o -> VU.concat [su o]))
        , ("Unboxed new, copy", \ r -> time r (\ o -> VU.create (do
              m <- VUM.new n; VU.copy m (su o); return m)))
        , ("Unboxed unsafeNew, copy", \ r -> time r (\ o -> VU.create (do
              m <- VUM.unsafeNew n; VU.copy m (su o); return m))) ]
  _ <- evaluate (VS.length vs + VU.length vu)
  -- Each case twice, the second time in the reverse order.
  ts1 <- forM cases $ \ (_, t) -> t reps
  ts2 <- fmap reverse $ forM (reverse cases) $ \ (_, t) -> t reps
  forM_ (zip3 cases ts1 ts2) $ \ ((name, _), t1, t2) ->
    printf "n = %7d  %-26s %8.1f us %8.1f us\n" n name t1 t2
```

## Expected behavior

`force`, `modify` and `(//)` write each element of their new vector one time, and take about as long as `concat` of a list of one vector.

## Environment

* vector-0.13.2.0, from Hackage. On master at [fd2ebe1534][master], the generic `clone`, `force`, `modify`, `modifyWithBundle` and `thaw`, and the mutable `new` and `clone`, have the same code.
* GHC 9.6.7, 9.8.4, 9.10.3, 9.12.4 and 9.14.1; cabal-install 3.18.1.0.
* Linux (kernel 7.0.0-31-generic), x86_64 (AMD Ryzen 7 5800X).

[571]: https://github.com/haskell/vector/issues/571
[511]: https://github.com/haskell/vector/issues/511
[513]: https://github.com/haskell/vector/pull/513
[30]: https://github.com/haskell/vector/issues/30
[clone]: https://github.com/haskell/vector/blob/fd2ebe15344913368c38bd62e4f0452ecbe08e74/vector/src/Data/Vector/Generic.hs#L2649-L2655
[new]: https://github.com/haskell/vector/blob/fd2ebe15344913368c38bd62e4f0452ecbe08e74/vector/src/Data/Vector/Generic/Mutable.hs#L468-L471
[thaw]: https://github.com/haskell/vector/blob/fd2ebe15344913368c38bd62e4f0452ecbe08e74/vector/src/Data/Vector/Generic.hs#L2475-L2480
[mclone]: https://github.com/haskell/vector/blob/fd2ebe15344913368c38bd62e4f0452ecbe08e74/vector/src/Data/Vector/Generic/Mutable.hs#L516-L521
[force]: https://github.com/haskell/vector/blob/fd2ebe15344913368c38bd62e4f0452ecbe08e74/vector/src/Data/Vector/Generic.hs#L825-L829
[modify]: https://github.com/haskell/vector/blob/fd2ebe15344913368c38bd62e4f0452ecbe08e74/vector/src/Data/Vector/Generic.hs#L1054-L1064
[master]: https://github.com/haskell/vector/tree/fd2ebe15344913368c38bd62e4f0452ecbe08e74
