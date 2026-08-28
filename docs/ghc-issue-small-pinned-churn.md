# GHC issue: small-pinned churn taxes the mutator

Staged 2026-08-18; filed 2026-08-19 as [GHC work item 27719](https://gitlab.haskell.org/ghc/ghc/-/work_items/27719), this file staying as the filed record, the text from "## Summary" down being the body as filed. Title: **10--44% extra mutator time permanently, from a short burst of small pinned allocations**. The prose is ASD-STE100 Simplified Technical English. This file follows the form of [ghc-issue-block-pool-fragmentation.md](ghc-issue-block-pool-fragmentation.md) (filed as #27601), which reports a DIFFERENT condition; the split between the two is stated in the body so triage does not merge them. The awareness sweep (2026-08-18, gitlab.haskell.org issues and MRs, the introducing MR !5175's full discussion, the user's guide, the GHC.ForeignPtr and Data.Vector.Storable haddocks, and an authenticated project-wide COMMENT-body sweep --- 41 search terms over the notes scope, every pinned/block-fragmentation hit memory-framed) found the TIME cost unknown upstream, so this is framed as an RTS performance defect, per the plan's branch for that verdict; the sweeps' full evidence record, quotes and links is [ghc-issue-small-pinned-churn-sweep.md](ghc-issue-small-pinned-churn-sweep.md).

## Summary

A program phase that makes many short-lived SMALL pinned allocations makes all later allocation-heavy code in the same process permanently slower. "Small" means that the object, with its header, is under 409 machine words --- the large-object limit, `BLOCK_SIZE * 8 / 10` = 3276 bytes, compared in words --- thus a payload of at most 3248 bytes, or 406 `Double`s. The runtime system puts such objects into a shared per-capability pinned block (the accumulator path of `allocatePinned` in rts/sm/Storage.c; commit 47d6acd3be, MR !5175, for #19481, reworked where that path's blocks are taken from, because taking them out of the nursery fragmented it). Objects above the limit each get their own block group. This size class is the whole cause: in the reproducer below, sprays of 800 B, 1800 B and 2304 B objects at an equal object count (1.15 million) all produce the slowdown, and a spray of 3600 B objects produces zero slowdown. Every `Data.Vector.Storable` vector and every `mallocForeignPtrBytes` buffer is pinned, at every size, so array programs that produce many vectors of up to 407 doubles do this constantly.

The slowdown applies to later code that allocates heavily on the ordinary (unpinned) heap, and it grows with the allocation area. In the reproducer, the victim loop (a boxed-list traversal plus one pinned result per iteration) becomes 9 to 18% slower at `-A32m` and at `-A1G`, and 0% slower at the default nursery size. In the application-scale array-interpretation workload that the reproducer models, the same poison phase makes a list-traversal phase 12% slower at `-A32m` and 33 to 44% slower at `-A64m` to `-A1G` (fixed iteration counts, the poison phase's own time subtracted), permanently, while phases with little allocation stay unharmed. The state is permanent for the process life: major collections do not correct it, `-H2G` does not correct it, and no operation available to a program corrects it. GHC 9.14.1 and HEAD behave the same as 9.12.4.

The dose response is logarithmic in the object count, approximately 2.5% per decade over four decades, and it saturates between 10^5 and 10^6 objects. A phase of one second is sufficient to reach saturation. Allocation-area tuning does not remove the tax: on the application victims (several, at saturating doses) it is +3 to +6% at `-A4m`, +12 to +17% at `-A32m`, +27 to +37% at `-A64m` and `-A256m`, and up to +44% at `-A1G`. Thus only small allocation areas refuse to pay, at their own collection cost, and the areas that make allocation-heavy code fastest are the areas that pay the most.

Hardware counters show what the tax is. On the application victim with a fixed iteration count at `-A1G` (poison-alone process subtracted from the pair process), per the full phase:

| | victim alone | victim after poison | ratio |
|---|---:|---:|---:|
| instructions | 571.9e9 | 570.6e9 | 0.998 |
| cycles | 178.4e9 | 237.5e9 | 1.33 |
| cache-misses | 419.6e6 | 1310.2e6 | 3.12 |
| dTLB-load-misses | 104.6e6 | 104.8e6 | 1.00 |

The instruction count is identical. The dTLB misses are identical. Only the last-level-cache misses increase, approximately 3.1 times. The memory in use barely moves: at `-A32m` the reproducer's `max_mem_in_use_bytes` is identical (0.1025 GiB) in the poisoned and the clean process while the victim is 11% slower. Thus the cost is the STRUCTURE that the churn leaves, not the quantity of memory.

The mechanism, from the RTS sources: each sub-threshold pinned allocation goes into the per-capability accumulator block; each full accumulator block retires into generation 0's large-object list; the collection that follows frees these blocks into the size-binned LIFO free lists of the block allocator. A 2304-byte object fills a 4096-byte block alone, so a million-object spray cycles a million blocks through this path. The free lists are never repaired: allocation takes the head of the first bucket that fits, coalescing is local, and nothing restores address order --- GHC's own `Note [Sources of Block Level Fragmentation]` (rts/sm/Storage.c) documents this as a trade-off, for the MEMORY cost. The nursery is then rebuilt from these scattered singletons: every post-collection trim and grow takes blocks from the free lists, and every out-of-line allocation permutes the nursery chain, so the later mutator walks a permanently scattered allocation area. **The `Note` names a correction --- reallocate the nursery periodically --- and states that it is not implemented.**

Objections this report anticipates, each answered by a measurement:

* **"A large allocation area has bad cache locality; this is expected."** The comparison is within one area: at the same `-A1G` the victim runs 6.35 ms per iteration clean and 7.12 ms after one second of small pinned allocations. A clean process at a large area is the FASTEST configuration measured (6.35 ms against 26.55 ms at the default size), so the condition takes away exactly the speed the large area buys. And an equal count of 3600 B pinned objects --- more total bytes --- costs zero in the same binary at the same area, which no general locality account explains.
* **"Duplicate of the known pinned-fragmentation reports."** Those report the MEMORY cost of the same family of conditions: #7257, #7831, #19171 and #23221 (pinned/large fragmentation), #19481 (the nursery hodge-podge that motivated the accumulator path), #19248 (compaction does not help block-level fragmentation), #21483 (`-Fd` thrashing), and the alternative pinned allocators #19175 and #22768, all memory-motivated. This report adds the mutator TIME cost, and an earlier report of it was not found: the discussion of MR !5175 does not name one, and a search of issue and MR titles, descriptions and ALL comment bodies (2026-08-18, 41 terms over the tracker's notes search scope) finds the nearest remarks tying heap layout to mutator time only through other mechanisms --- a hugepages MR (!4523) measured a dTLB improvement with no elapsed-time change, and #14981 notes that the GC's moving objects together can help mutator performance --- none of them the cost of pinned or block-level churn.
* **"Duplicate of #27601."** That condition needs sprays of objects directly ABOVE the 3276-byte limit: they go through the own-group path, the retained memory doubles, and `-H2G` removes the penalty. The condition of THIS report needs objects BELOW the limit, and the shared accumulator path is the necessary ingredient: the memory in use is unmoved at `-A32m`, `-H2G` does not help (the poisoned victim stays 9% slower under `-A1G -H2G`), and the same 1.15-million-object dose that poisons here produces zero tax when its objects are 3600 B. One binary discriminates the two conditions (`poison` against `poisonbig` in the reproducer below).
* **"A known and conscious trade-off."** The documented trade-off is a memory floor. `Note [Sources of Block Level Fragmentation]` states: "Having a block-level fragmented heap means your program will never go below a certain memory threshold but it doesn't \"use\" more memory during periods of high residency." and "The block allocator can reuse unused space within a megablock and therefore as residency increases again, the fragmented blocks will get filled up." --- the assumption that the fragmented space is harmlessly reusable, which the 3.1x cache-miss measurement above contradicts. The review of MR !5175 discusses collection frequency, never mutator speed. A cost nobody wrote down is not a conscious trade-off.
* **"The program is doing something pathological."** Every `Data.Vector.Storable` vector and every `mallocForeignPtrBytes` buffer is pinned, and a million small vectors is about one second of an ordinary array workload (the reproducer prints this phase's time). The user also cannot know: the user's guide's runtime-control chapter does not contain the word "pinned", and the `GHC.ForeignPtr` haddocks recommend the entry point ("strongly recommended in preference to newForeignPtr") without a caveat.
* **"A major or idle collection heals it."** The reproducer performs a major collection between the phases and the tax remains; no collection rebuilds free-list structure or re-sorts the nursery chain (rts sources), and the state lasts for the process life.
* **"Some RTS flag fixes it."** Measured: `-H2G`, `-G1`, `-xn`, `-Fd0`, `--disable-delayed-os-memory-return` and `-c` do not (the Attempted workarounds section below); `-G1` makes it worse.
* **"Run at the default `-A` then."** The user's guide itself recommends 16 to 64 MB areas for parallel throughput, and the tax is already +12 to +17% at `-A32m`; and running at the default size costs allocation-heavy loops up to 4 times their runtime (26.55 against 6.35 ms in the reproducer).

The measurements suggest three correction directions. (1) Make the accumulator path recycle its blocks the way the own-group path evidently does without damage, or give the accumulator blocks a separate region, so that their churn cannot scatter the region that the nursery is rebuilt from. (2) Implement the periodic nursery reallocation that `Note [Sources of Block Level Fragmentation]` already names, which repairs the victim side. (3) Lowering the large-object threshold is NOT a correction: the 800 B and 1800 B sprays show that any sub-threshold size poisons, so a lower threshold only moves a window of sizes to the (harmless) own-group path at a memory cost for that window.

## Steps to reproduce

The reproducer demonstrates the size-class discrimination, the allocation-area dependence including the zero at the default size, the `-H2G` result and the unmoved memory; the dose curve, the hardware counters and the RTS-flag results are measurements of the application-scale workload.

1. Save the program below as `Repro.hs`.
2. Compile the program: `ghc -O1 -rtsopts Repro.hs`. Use a GHC installation with optimized boot libraries.
3. Run `./Repro victim +RTS -A32m -I0 -T -RTS` a few times, and the same with `poison victim`, `poisonmid victim`, `poisontiny victim`, `poisonbig victim`; then the same five at `-A1G`, and at the default nursery (the same command with no `-A` flag), and at `-A1G -H2G`.
4. Compare the second-half `victim` rates. The first half of the victim loop contains a warm-up transient whose sign depends on the allocation area (at `-A1G` a fresh process's first pass through the nursery is FASTER than steady state), so only the second halves are comparable. The results on the test system (ms per iteration, second half, representative single runs; the spread between repeated runs is a few percent):

   | 9.12.4, second half | `-A32m` | tax | `-A1G` | tax |
   |---|---:|---:|---:|---:|
   | victim alone | 9.35 | | 6.35 | |
   | after 2304 B spray (1 per block) | 10.36 | +10.8% | 7.12 | +12.1% |
   | after 1800 B spray (2 per block) | 10.50 | +12.3% | 6.91 | +8.8% |
   | after 800 B spray (5 per block) | 10.45 | +11.8% | 7.46 | +17.5% |
   | after 3600 B spray (own group, the 27601 class) | 9.24 | -1.2% | 6.34 | -0.2% |

   | compiler, 2304 B spray | alone `-A32m` | poisoned | alone `-A1G` | poisoned |
   |---|---:|---:|---:|---:|
   | 9.12.4 | 9.35 | 10.36 (+10.8%) | 6.35 | 7.12 (+12.1%) |
   | 9.14.1 | 9.27 | 10.49 (+13.1%) | 6.42 | 7.11 (+10.8%) |
   | HEAD 10.1.20260803 | 9.35 | 10.38 (+11.0%) | 6.37 | 7.11 (+11.7%) |

   The class discrimination of the first table reproduces on all three compilers (the 9.14.1 sub-threshold sprays read +12.4 to +13.3% at `-A32m` and +8.8 to +16.9% at `-A1G` with the 3600 B control at +0.6/+0.4%; HEAD reads the same within run-to-run spread).

   At the default nursery the tax is zero (26.55 alone against 26.35 poisoned on 9.12.4). Under `-A1G -H2G` the tax stays (6.44 alone against 7.05 poisoned, +9.4%). The `max_mem_in_use_bytes` at `-A32m` is identical in all five modes (0.1025 GiB). The reproduction is confirmed when the sub-threshold sprays slow the second half by clearly more than the run-to-run spread at `-A32m` and at `-A1G`, while the 3600 B spray and the default-nursery runs stay within the spread. The magnitudes depend on the cache hierarchy; the tables are from the machine in the Environment section (32 MB last-level cache), and a different hierarchy can show different sizes of the same pattern.

```haskell
-- Reproducer for the small-pinned churn tax.  Base only.
--
-- Build:  ghc -O1 -rtsopts Repro.hs
-- Run:    ./Repro victim            +RTS -A32m -I0 -T -RTS
--         ./Repro poison victim     +RTS -A32m -I0 -T -RTS
--         ./Repro poisonmid victim  +RTS -A32m -I0 -T -RTS
--         ./Repro poisontiny victim +RTS -A32m -I0 -T -RTS
--         ./Repro poisonbig victim  +RTS -A32m -I0 -T -RTS
--   and the same five at -A1G, at the default nursery, and at -A1G -H2G.
--
-- The poison phase sprays 1.15 million short-lived pinned buffers of 2304
-- bytes (288 doubles) -- below the 3276-byte large-object limit, so each
-- goes through the shared per-capability pinned accumulator block.
-- poisonmid (1800 B, two per block) and poisontiny (800 B, five per block)
-- spray the same object count at other sub-threshold sizes.  poisonbig
-- (3600 B, above the limit, own block group each -- #27601's
-- class) is the control: the same count, zero tax.  The victim mimics an
-- array program's list-processing phase: heavy short-lived boxed churn
-- (a materialized cons list read off a long-lived pinned source buffer),
-- plus one pinned result per iteration.  mallocForeignPtrBytes allocates
-- a pinned ByteArray# on the RTS heap -- the same entry point
-- Data.Vector.Storable uses -- so this depends on base alone.  The
-- NOINLINE pragmas guard against full-laziness hoisting an allocation out
-- of its loop.
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import Control.Monad (forM_, when)
import Foreign.ForeignPtr (mallocForeignPtrBytes, withForeignPtr)
import Foreign.Ptr (Ptr)
import Foreign.Storable (peekElemOff, pokeElemOff)
import GHC.Clock (getMonotonicTime)
import GHC.Stats (getRTSStats, max_mem_in_use_bytes)
import System.Environment (getArgs)
import System.Mem (performMajorGC)

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

-- The sprays: 4000 * 288 ~ 1.15M pinned allocations each, counted rather
-- than timed so the dose does not depend on compiler or library speed.
{-# NOINLINE poisonIter #-}
poisonIter :: Int -> IO Double
poisonIter seed = do
  let go !acc !i | i >= 288 = pure acc
                 | otherwise = do v <- fillSum 288 (fromIntegral (seed + i))
                                  go (acc + v) (i + 1)
  go 0 0

{-# NOINLINE poisonMidIter #-}
poisonMidIter :: Int -> IO Double
poisonMidIter seed = do
  let go !acc !i | i >= 288 = pure acc
                 | otherwise = do v <- fillSum 225 (fromIntegral (seed + i))
                                  go (acc + v) (i + 1)
  go 0 0

{-# NOINLINE poisonTinyIter #-}
poisonTinyIter :: Int -> IO Double
poisonTinyIter seed = do
  let go !acc !i | i >= 288 = pure acc
                 | otherwise = do v <- fillSum 100 (fromIntegral (seed + i))
                                  go (acc + v) (i + 1)
  go 0 0

{-# NOINLINE poisonBigIter #-}
poisonBigIter :: Int -> IO Double
poisonBigIter seed = do
  let go !acc !i | i >= 288 = pure acc
                 | otherwise = do v <- fillSum 450 (fromIntegral (seed + i))
                                  go (acc + v) (i + 1)
  go 0 0

-- The victim: read a long-lived pinned source through a temporary
-- cons list of boxed Doubles (~600k (:) cells and boxed Doubles per
-- iteration, ~24 MB of nursery churn), then one pinned result per
-- iteration.  The mapM materializes the whole list before sum consumes
-- it -- deliberate, a multi-megabyte live span, not an accident to
-- optimize away.
{-# NOINLINE victimIter #-}
victimIter :: Ptr Double -> Int -> IO Double
victimIter src seed = do
  let l = 600000 :: Int
  vs <- mapM (peekElemOff src) [0 .. l - 1]
  let !s = sum [v + fromIntegral seed | v <- vs]
  r <- fillSum 200000 s
  pure $! s + r

memGiB :: IO Double
memGiB = do s <- getRTSStats
            pure (fromIntegral (max_mem_in_use_bytes s) / 2 ^ (30 :: Int))

main :: IO ()
main = do
  args <- getArgs
  srcFp <- mallocForeignPtrBytes (600000 * 8)
  withForeignPtr srcFp $ \src -> do
    forM_ [0 .. 600000 - 1] $ \i ->
      pokeElemOff src i (fromIntegral i :: Double)
    forM_ [("poison", poisonIter), ("poisonmid", poisonMidIter),
           ("poisontiny", poisonTinyIter), ("poisonbig", poisonBigIter)] $
      \(name, iter) ->
        when (name `elem` args) $ do
          t0 <- getMonotonicTime
          forM_ [1 .. 4000 :: Int] $ \i -> do
            _ <- iter i
            pure ()
          t1 <- getMonotonicTime
          m <- memGiB
          putStrLn (name ++ "ed in " ++ show (t1 - t0)
                    ++ " s; mem in use: " ++ show m ++ " GiB")
    performMajorGC
    -- Two halves timed separately: an unpoisoned run's first pass through
    -- a fresh large nursery runs FASTER than steady state, so the second
    -- half is the reading to compare across modes.
    t0 <- getMonotonicTime
    forM_ [1 .. 150 :: Int] $ \i -> do
      _ <- victimIter src i
      pure ()
    t1 <- getMonotonicTime
    forM_ [151 .. 300 :: Int] $ \i -> do
      _ <- victimIter src i
      pure ()
    t2 <- getMonotonicTime
    m <- memGiB
    putStrLn ("victim: first half " ++ show ((t1 - t0) / 150 * 1000)
              ++ " ms/iter, second half " ++ show ((t2 - t1) / 150 * 1000)
              ++ " ms/iter; mem in use: " ++ show m ++ " GiB")
```

## Attempted workarounds

Runtime options do not remove the condition. `-H2G` does not (the table above). `-G1`, `-xn` (the nonmoving collector), `-Fd0`, `--disable-delayed-os-memory-return` and `-c` were each measured against the saturated state on the application victim: `-G1` makes it worse (approximately +8% at `-A32m`) and the others change nothing --- `-c` cannot help by construction, since compaction skips pinned blocks and rebuilds no free list. Two allocation-area measures palliate without removing it: a small area refuses most of the tax (+3 to +6% at `-A4m`), at its own collection cost; and raising the large-object allowance at a small area (`-A4m -AL64m`) gives code whose collections are driven by LARGE allocations the speed of a big area at the small area's exposure --- it does not reach code whose churn is small objects, and it does not re-open the own-group accumulation of #27601 at the small area (measured: the 3600 B spray under `-A4m -AL64m` costs zero time and ~15 MB of memory in use).

At the source level the workaround is to prevent the poisoning in the first place: pad each small pinned allocation above the 3276-byte limit (allocate at least 410 doubles, use a slice of the buffer), which routes it through the harmless own-group path at a memory cost of up to ~3 KB per buffer --- or route small buffers through unpinned memory (`ByteArray#`, unboxed vectors) and convert only at an FFI boundary. A program that never makes a sub-threshold pinned allocation never forms the state through this route. But the prevention must be complete before the first spray, across every library in the program, because no measure repairs a state that has formed and a process restart is the only reset --- and the prevention protects only phases shaped like the victim's, a burst followed by homogeneous allocation-heavy work; a second formation route that no allocation policy prevents is reported in a follow-up comment.

The padding workaround is itself an argument for a correction in the RTS. It works --- the reproducer measures it directly, the same spray at the padded size costing zero time where the sub-threshold sizes cost 9 to 18%, at `-A32m` and at `-A1G` alike, and the application-scale workload confirms it end to end: with every result allocation padded, the fixed-iteration victim reads +0.2% after the mega-dose at `-A32m` and +0.6% at `-A1G`, where the unpadded program reads +12% and +44% --- so for phases of this shape a padded program keeps the FULL benefit of the enlarged areas, which are the fastest configurations when clean. **And it works by deliberately defeating the memory optimization that the accumulator path exists to provide**: the program wastes up to ~3 KB per buffer to buy back the mutator speed the optimization takes. Once this is known, a performance-sensitive library has every reason to pad all its small pinned allocations automatically (the maintainers of the array stack that found this condition are already weighing exactly that allocation policy). Then the 3276-byte threshold becomes a de-facto interface that programs are written against, memory is wasted as a matter of course, and the accumulator optimization serves nobody. A mechanism that users are best served by defeating is better corrected than defeated.

## Expected behavior

The expected behavior is that the speed of the victim loop is the same whether or not an earlier phase of the process made small pinned allocations, at every allocation-area setting --- or, if the condition is an accepted trade-off, that the user's guide and the pinned-allocation entry points document it, because today a program that enlarges `-A` to make allocation-heavy code (often dramatically) faster gets, from one second of an unlucky common allocation pattern, a permanent slowdown larger than the gain. The condition also makes criterion-style in-process benchmarking of array code invalid at enlarged allocation areas: every benchmark that runs after a small-pinned-allocating benchmark in the same process runs permanently slower --- and by a second formation route, reported in a follow-up comment, after any allocation-heavy benchmark --- the shift is a bias and not noise (the per-iteration fits stay tight around a value that is wrong for the process state), and interleaved A/B comparisons cannot see it, because both arms share the process. From the first small-pinned benchmark on, such a suite measures the damaged state, not the code.

## Environment

* GHC version used: 9.12.4, 9.14.1, and HEAD 10.1.20260803 (commit d415f38a75). All three show the same behavior.
* The reproducer runs on one capability; the accumulator path is per-capability, and behavior under `-N` was not measured.

Optional:

* Operating System: Linux (kernel 7.0)
* System Architecture: x86_64 (AMD Ryzen 7 5800X, Zen 3, 32 MB last-level cache)


/label ~"T::bug"
/label ~"needs triage"
