# GHC issue: pinned-allocation spray doubles the block pool

Filed as [GHC work item 27601](https://gitlab.haskell.org/ghc/ghc/-/work_items/27601); this file stays as the filed record, the text from "## Summary" down being the filed body. Title: **The block allocator never recovers from a short burst of small pinned allocations: retained memory doubles for the process lifetime and later code runs slower**. The prose is ASD-STE100 Simplified Technical English. The full analysis of the originating case is in [position-effect.md](position-effect.md); the filed body is self-contained.

## Summary

A program phase that makes many short-lived pinned allocations can cause the block pool of the RTS to become two times as large. Each allocation in the program below is a buffer of 3600 bytes. This size is above the large-object limit of 3276 bytes, by only 324 bytes. Thus the RTS gives each buffer its own block group. The RTS frees pinned objects only at a garbage collection, and this phase causes almost no other allocation. Thus, between two garbage collections, approximately one gigabyte of these block groups is in the pool. The garbage collector then frees the groups, but the pool does not become small again, and its free lists stay divided into many small parts. This condition continues for the full life of the process. Major garbage collections do not correct it. The option `-Fd1` does not correct it. No operation that a program can do corrects it.

Code that allocates in this pool after this phase is slower. The effect has two strengths. Code that writes and reads each new buffer only one time becomes slower by a small quantity. In the reproducer below, the slowdown is 1% to 4%. Code that recycles a large working set through the divided free lists at a high rate becomes much slower. In the application that this program models (an array-interpretation workload), such code becomes 22% slower for the remainder of the process, after the same pool change (1117 MiB to 2180 MiB). The difference between the two strengths comes from the access pattern, and it is the reason a small program does not easily show the large effect. A simple loop has one of two protections. When its working set is small, the cache holds the set, scattered or not. When its accesses are sequential, the hardware prefetcher hides the DRAM latency. The interpreter of the application has no such protection: in each iteration, it reads and writes many arrays of different sizes through pointers, and each such access to the scattered region can miss.

In that application, the effect did more than make the code slower. It made benchmark results invalid. The change is a bias, not noise. In one process, the regression fits stay tight (R2 >= 0.999) around a value that is wrong by up to 22% for the pool state of that process. More samples in the same process make the confidence interval smaller around the wrong value. They do not find or decrease the bias. Comparisons between processes with different initial workloads thus show differences that are not real. One such false 18--20% regression showed the same tight fits across twelve measurements and survived an interleaved and controlled A/B procedure. Also, while the pool grows, the early samples of a benchmark are slow. This transient makes the fitted time-per-iteration slope too low at usual time budgets. Only runs several times longer give a slope that is free of it.

For the 22% case, hardware counters show the cause. Data from `perf stat` over runs with a fixed iteration count, per iteration:

| per iteration | clean pool | divided pool | ratio |
|---|---:|---:|---:|
| task-clock | 10.81 ms | 13.21 ms | 1.222 |
| instructions | 133.55M | 133.48M | 0.9994 |
| dTLB-load-misses | 22.1k | 22.9k | 1.04 |
| cache-misses | 120.0k | 343.5k | 2.86 |
| page faults (full phase) | 90k | 98 | --- |
| clock | 4.954 GHz | 4.953 GHz | 1.00 |

The instruction counts are equal. The dTLB misses are almost equal. The clock speeds are equal. The garbage-collection counts, the copied bytes and the allocated bytes are equal. There are no page faults in the slow phase. Thus all the memory is resident. Only the last-level-cache misses increase, 2.86 times. Each added cache miss costs approximately 53 cycles, which is DRAM latency with overlap. This is sufficient to cause the full time increase. Two controls show that the cause is the structure of the pool, not its size. A pool of the same size that the RTS gets in one continuous piece (`+RTS -H2G`) has no cost. A different first phase, which makes a larger pool with larger parts, has a smaller cost.

This path is important for array programs: `Data.Vector.Storable` makes pinned allocations at each size, and buffers with sizes directly above 3276 bytes are the worst case. Issues #7257, #7831, #19171 and #23221 report the memory cost of pinned and large-object fragmentation. This report adds a time cost of the same condition. An earlier report of this time cost was not found. Three corrections are possible. (1) At a major garbage collection, release the megablocks that are fully free. In the reproducer, most of the added gigabyte is free space after the collection between the phases, but the RTS keeps all of it. (2) For new pinned and large allocations, select free blocks in address order, so that the allocations of one program phase become adjacent. The `+RTS -H2G` control shows that adjacent placement removes the time cost. (3) Give pinned and large objects their own region of megablocks, so that their churn cannot divide the region that other allocations use. Separately, a diagnosis aid, not a correction: `GHC.Stats` gives no data about the free-list condition, and the increase of `max_mem_in_use_bytes` is the only visible symptom.

## Steps to reproduce

1. Save the program below as `Repro.hs`.
2. Compile the program: `ghc -O1 -rtsopts Repro.hs`. Use a GHC installation with optimized boot libraries. A quick-flavour build of GHC does not show the effect, because its larger allocation overhead causes frequent collections, and these prevent the accumulation.
3. Run `./Repro victim +RTS -A1G -I0 -T -RTS` a few times.
4. Run `./Repro poison victim +RTS -A1G -I0 -T -RTS` a few times.
5. Compare the `victim` times and the `mem in use` values in the outputs of steps 3 and 4. The `victim` loop is the same code and the same allocation in the two modes, yet the runtime shows a slowdown. The results on the test system, from a few runs for each mode and each compiler (in rare runs the effect does not reproduce, and its magnitude differs randomly from run to run, which is yet another problem when benchmarking):

   | | victim alone | victim poisoned | slowdown | pool alone | pool poisoned |
   |---|---:|---:|---:|---:|---:|
   | 9.12.4 | 2.63--2.70 ms/iter | 2.71--2.81 ms/iter | +4% | 1.018 GiB | 2.166 GiB |
   | 9.14.1 | 2.57--2.60 ms/iter | 2.61--2.68 ms/iter | +2% | 1.018 GiB | 2.166 GiB |
   | HEAD 10.1.20260803 | 2.44--2.45 ms/iter | 2.47--2.49 ms/iter | +1% | 1.018 GiB | 2.166 GiB |

   The `poison` phase completes in approximately 3 seconds. Thus a short phase of allocation, of a type that array programs do frequently, is sufficient to cause the permanent change.

```haskell
-- Reproducer for the pinned-spray pool doubling.  Base only.
--
-- Build:  ghc -O1 -rtsopts Repro.hs
-- Run:    ./Repro victim        +RTS -A1G -I0 -T -RTS
--         ./Repro poison victim +RTS -A1G -I0 -T -RTS
--
-- Poison sprays short-lived pinned buffers sized just above GHC's
-- large-object threshold (450 doubles = 3600 bytes > 3276),
-- for a fixed 8000 iterations -- a saturating dose, counted rather
-- than timed so it does not depend on compiler or library speed.  The victim
-- loop is identical in both modes; a major GC separates the phases, as
-- a benchmark harness would do.
-- mallocForeignPtrBytes allocates a pinned ByteArray# on the RTS heap --
-- the same entry point Data.Vector.Storable uses -- so this depends on
-- base alone.  The NOINLINE pragmas guard against full-laziness hoisting
-- an allocation out of its loop.
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import Control.Monad (forM_, when)
import Foreign.ForeignPtr (mallocForeignPtrBytes, withForeignPtr)
import Foreign.Storable (peekElemOff, pokeElemOff)
import GHC.Clock (getMonotonicTime)
import GHC.Stats (getRTSStats, max_mem_in_use_bytes)
import System.Environment (getArgs)
import System.Mem (performGC)

-- Allocate a pinned n-Double buffer on the RTS heap, fill it, sum it.
{-# NOINLINE fillSum #-}
fillSum :: Int -> Double -> IO Double
fillSum n x = do
  fp <- mallocForeignPtrBytes (n * 8)
  withForeignPtr fp $ \p -> do
    let fill !i | i >= n = pure ()
                | otherwise = pokeElemOff p i x >> fill (i + 1)
    fill 0
    let summ !acc !i | i >= n = pure acc
                     | otherwise = do v <- peekElemOff p i
                                      summ (acc + v) (i + 1)
    summ 0 0

{-# NOINLINE poisonIter #-}
poisonIter :: Int -> IO Double
poisonIter seed = do
  let go !acc !i | i >= 288 = pure acc
                 | otherwise = do v <- fillSum 450 (fromIntegral (seed + i))
                                  go (acc + v) (i + 1)
  s <- go 0 0
  -- No churn here, and deliberately so: with almost no ordinary
  -- allocation the nursery fills only every ~1000 poison iterations,
  -- so about a gigabyte of spray groups accumulates live between
  -- collections -- which is what grows and fragments the pool.
  pure s

{-# NOINLINE victimIter #-}
victimIter :: Int -> IO Double
victimIter seed = do
  let go !acc !i | i >= 12000 = pure acc
                 | otherwise = do v <- fillSum 9 (fromIntegral (seed + i))
                                  go (acc + v) (i + 1)
  small <- go 0 0
  large <- fillSum 200000 (fromIntegral seed)
  pure $! small + large

memGiB :: IO Double
memGiB = do s <- getRTSStats
            pure (fromIntegral (max_mem_in_use_bytes s) / 2 ^ (30 :: Int))

main :: IO ()
main = do
  args <- getArgs
  when ("poison" `elem` args) $ do
    t0 <- getMonotonicTime
    forM_ [1 .. 8000 :: Int] $ \i -> do
      _ <- poisonIter i
      pure ()
    t1 <- getMonotonicTime
    m <- memGiB
    putStrLn ("poisoned in " ++ show (t1 - t0)
              ++ " s; mem in use: " ++ show m ++ " GiB")
  performGC
  t0 <- getMonotonicTime
  forM_ [1 .. 300 :: Int] $ \i -> do
    _ <- victimIter i
    pure ()
  t1 <- getMonotonicTime
  m <- memGiB
  putStrLn ("victim: " ++ show ((t1 - t0) / 300 * 1000)
            ++ " ms/iter; mem in use: " ++ show m ++ " GiB")
```

## Expected behavior

The expected behavior is that the block pool decreases to approximately its initial size (1.02 GiB) after the major garbage collection between the two phases, or that the free memory becomes continuous again. The expected behavior is also that the `victim` loop has the same speed in the two modes.

## Environment

* GHC version used: 9.12.4, 9.14.1, and HEAD 10.1.20260803 (commit d415f38a75). All three show the same behavior.

Optional:

* Operating System: Linux (kernel 6.17)
* System Architecture: x86_64 (AMD Ryzen 7 5800X, Zen 3, 32 MB last-level cache)


/label ~"T::bug"
/label ~"needs triage"
