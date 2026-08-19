# GHC issue comment: the interleaved formation route

Staged 2026-08-18, NOT yet posted; a follow-up comment for the small-pinned-churn issue, filed 2026-08-19 as [GHC work item 27719](https://gitlab.haskell.org/ghc/ghc/-/work_items/27719) ([ghc-issue-small-pinned-churn.md](ghc-issue-small-pinned-churn.md) is its filed record), so this is now postable, the text from "The condition" down being the body to post. Extended 2026-08-19: the body embeds a base-only reproducer — the description's program plus the interleave modes and two non-allocating controls — and its results table was taken on the exact embedded program. The prose is ASD-STE100 Simplified Technical English, as in the issue.

The condition in the report in the issue description is one face of something broader. The victim we describe here is a similar pattern but at application scale (a small reproducer follows at the end of this comment): a loop that reads a 7 MB array through a temporary cons list of boxed `Double`s — approximately 200 MB of ordinary short-lived allocation per iteration — and writes one 7 MB pinned result per iteration. It runs in a standalone driver over `vector` and `base`, each call timed by the monotonic clock, with the steady state read from the late rounds of a run (the early rounds carry the warm-up). Measured so, the victim shows a SECOND formation route for what appears to be the same damaged state: interleave its iterations with small allocating calls, pinned or not, and it degrades to the same level that the pinned spray produces.

The victim runs at 16.8 ms per iteration alone in a process (18.7 through the driver loop, its measured constant offset). With 1000 small calls interleaved between each pair of victim iterations, it runs at 23.7 ms — the level that the upfront sub-threshold spray of the report produces. The facts that separate the two routes:

* The interleaved route does not need the pinned size class: a spray of MOVABLE buffers, which never touches the pinned allocator, produces the effect. In the driver, the calls produce the full effect whether the sprayer's result is a sub-threshold pinned buffer (2304 B), an above-threshold pinned one (3280 B, own block group) or an unpinned unboxed one — but a real array call also makes small movable allocations (index vectors, boxed values) whatever its result's class, and the reproducer below isolates those as the ingredient: the interleaves of 2304 B pinned and 2304 B movable `ByteArray#` buffers degrade the victim at both areas, while the two PURE large-object interleaves (3600 B pinned and 3600 B movable — own block group each, no small allocation beside them) sit at the non-allocating controls' level at both areas. So the ingredient of this route is allocation BELOW the large-object limit — the object's heap does not matter and the shared pinned accumulator is not necessary — and no pinned-allocation policy reaches it. The class selectivity of the report belongs to the UPFRONT route only: a burst of allocations followed by a homogeneous phase damages that phase only when the burst is sub-threshold pinned (the report's in-binary control: 2304 B +23%, 3600 B zero; and upfront MOVABLE churn is what every program does constantly — the victim's own first half is a ~3.6 GB movable spray, and an alone run's second half sits at the steady state regardless). The split is stable against the dose rate and the horizon (the own-group interleave stays within +1 to +2% at `-A1G` at a tenth of the call rate and over a tenfold iteration horizon), and its counters match the driver's signature base-only: the unboxed interleave shows 1.5 times the cache misses of the own-group one at FEWER instructions and equal dTLB misses. The independence from the pinned class also shows at application scale in a criterion suite: with every benchmark's result allocation padded above the limit — every spray own-group, every call still making its small movable allocations — a scan of 23 candidate benchmarks against a final victim in one process reproduces the same degradation, +0.5 to +12.7% ordered by the candidate's call count, while the same padding takes the upfront-burst tax on a fixed-iteration victim from +12% to +0.2% at `-A32m` and from +44% to +0.6% at `-A1G`.
* The dose is cumulative in the BYTES of sub-threshold allocation; the call count is a proxy at a fixed call size. The driver's series at a fixed 2304 B call — 1, 10, 100 and 1000 calls per victim iteration over 1000 iterations — reads 18.96, 20.55 (still rising), 23.46 and 23.68, saturating in the same 10^5-to-10^6-call region as the report's pinned dose curve. The reproducer separates the two axes at `-A1G`: at a fixed 1000 calls per iteration, movable sprays of 288, 800 and 2304 B cost +1%, +3% and +7%, while at fixed total bytes the cost stays +7 to +8% across an eightfold change in call count — six cells on one curve in cumulative bytes (86 MB nearly clean, 240 MB partial, ~690 MB at the ceiling).
* The state PERSISTS. When the interleaving stops after 500 victim iterations, the victim holds the degraded rate (23.5-23.6) for 1000 further iterations with no recovery. `-H2G` does not remove it (23.0-23.9), as it does not remove the report's condition.
* The hardware signature is the report's signature. Between the pure run and the interleaved run (1000 iterations each): instructions +4.4% (the interleaved calls' own work), cycles +29%, cache-misses 2.16 times, dTLB-load-misses flat.

The route has a base-only reproducer: the program of the issue description with the interleave modes and the two non-allocating controls added, its upfront modes and its victim unchanged (the full program is hidden in a collapsed section at the end of this comment). The results on the test system (GHC 9.12.4; ms per victim iteration, second half, two runs each; the sprays' own wall time is subtracted):

| per interleaved call | `-A32m` | tax | `-A1G` | tax |
|---|---:|---:|---:|---:|
| victim alone | 9.27 / 9.18 | | 6.37 / 6.38 | |
| `inter`: 2304 B pinned | 11.78 / 11.48 | +26% | 7.07 / 7.06 | +11% |
| `interunboxed`: 2304 B movable | 11.32 / 11.26 | +22% | 6.92 / 6.93 | +9% |
| `interbig`: 3600 B pinned, own group | 10.48 / 10.55 | +14% | 6.47 / 6.47 | +1% |
| `interunboxedbig`: 3600 B movable, own group | 10.59 / 10.58 | +15% | 6.43 / 6.46 | +1% |
| `internoalloc`: write control, no allocation | 11.00 / 10.88 | +19% | 6.49 / 6.51 | +2% |
| `internoallocr`: read control, no allocation | 10.62 / 10.58 | +15% | 6.45 / 6.45 | +1% |

GHC 9.14.1 and HEAD 10.1.20260803 reproduce this table within the run-to-run spread, as they do the report's.

One caveat the controls expose, stated so that a runner is not surprised. At `-A1G` the discrimination is clean: the two small-allocating sprays cost +9 to +12% and everything else costs +1 to +2%. At `-A32m` this victim pays +14 to +19% for ANY interleaved activity at this cadence, allocating or not, and the allocation-specific damage is the increment above the controls, +7 to +11 points. The allocation-free disturbance appears only on this victim and only at the allocation area that equals the last-level cache of the test system: it is measured absent at 16, 24, 48 and 64 MB, and absent on the application driver's victim at `-A32m` and `-A64m` alike, where the non-allocating controls read ~19.0 against 20.3 and 23.3 to 23.7 sprayed. Part of the disturbance is collector work — the disturbed run copies 10% more during GC at an identical allocation total — and the rest was not investigated. The allocation-specific readings are therefore the `-A1G` column here and the application driver's cells.

The reading that fits all of it: there is one persistent block-level layout state, and there are two ways to reach it. A burst of sub-threshold pinned allocations builds it in one step, through the shared accumulator blocks — the report's condition, and the only way a SHORT phase can install it. Interleaved sub-threshold allocation — small objects, pinned or movable — builds the same state gradually, byte by byte, as the foreign allocations punctuate the victim's block reuse rhythm; allocations above the large-object limit, which get their own block groups, do not build it. This also explains a measurement that first appears to contradict the report: a workload that MIXES many different calls shows no additional slowdown after the pinned spray — because the mix has already built the state through the interleaved route. The clean-against-poisoned contrast of the report needs a homogeneous victim phase to be visible; real heterogeneous programs sit at the degraded level already, and the pinned burst is the only route that can put a homogeneous program there.

The corrections the report proposes stand, and this narrows which of them reach which case. A separate region or recycling for the accumulator blocks removes the burst route only. Periodic nursery reallocation — the correction that `Note [Sources of Block Level Fragmentation]` already names — repairs the victim side and thus should reach both routes.

<details><summary>The reproducer (click to expand)</summary>

```haskell
-- Reproducer for the small-pinned churn tax, with the interleave modes
-- of the follow-up comment added.  Base only.  The upfront modes and
-- the victim are the program of the issue description, unchanged.
--
-- Build:  ghc -O1 -rtsopts Repro.hs
-- Run:    ./Repro victim              +RTS -A32m -I0 -T -RTS
--         ./Repro poison victim       +RTS -A32m -I0 -T -RTS
--           (and poisonmid, poisontiny, poisonbig, as in the description)
--         ./Repro inter victim        +RTS -A32m -I0 -T -RTS
--         ./Repro interbig victim     +RTS -A32m -I0 -T -RTS
--         ./Repro interunboxed victim +RTS -A32m -I0 -T -RTS
--         ./Repro interunboxedbig victim +RTS -A32m -I0 -T -RTS
--         ./Repro internoalloc victim +RTS -A32m -I0 -T -RTS
--         ./Repro internoallocr victim +RTS -A32m -I0 -T -RTS
--   and the same at -A1G.
--
-- The inter modes make 1000 small calls between every pair of victim
-- iterations, so the cumulative call count crosses the dose curve's
-- saturation region inside the victim's second half (150000 calls by
-- its start).  The calls' own wall time is measured and subtracted, so
-- the printed halves stay the victim's rate.  Per call, inter allocates
-- a 2304 B pinned buffer (the description's poison class), interbig a
-- 3600 B pinned buffer (own block group each), interunboxed a 2304 B
-- movable ByteArray# (no pinned allocation at all), and
-- interunboxedbig a 3600 B movable ByteArray# -- above the large-object
-- limit, so it gets its own block group and does not pass through the
-- nursery.  Two modes allocate
-- nothing and are the controls: internoalloc WRITES a preallocated
-- pinned 2304 B buffer end to end at the same cadence, and
-- internoallocr READS an equal-sized window of the long-lived source.
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
module Main (main) where

import Control.Monad (forM_, when)
import Data.IORef (modifyIORef', newIORef, readIORef)
import Foreign.ForeignPtr (ForeignPtr, mallocForeignPtrBytes, withForeignPtr)
import Foreign.Ptr (Ptr)
import Foreign.Storable (peekElemOff, pokeElemOff)
import GHC.Clock (getMonotonicTime)
import GHC.Exts
import GHC.IO (IO (..))
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

-- The unpinned counterpart of fillSum: the same fill-and-sum over an
-- ordinary movable ByteArray# from newByteArray# -- no pinned
-- allocation at all.  Base only, via primops.
{-# NOINLINE fillSumUnpinned #-}
fillSumUnpinned :: Int -> Double -> IO Double
fillSumUnpinned (I# n) (D# x) = IO $ \s0 ->
  case newByteArray# (n *# 8#) s0 of
    (# s1, mba #) ->
      let fill i s | isTrue# (i >=# n) = s
                   | otherwise = fill (i +# 1#) (writeDoubleArray# mba i x s)
          summ acc i s
            | isTrue# (i >=# n) = (# s, D# acc #)
            | otherwise = case readDoubleArray# mba i s of
                (# s', v #) -> summ (acc +## v) (i +# 1#) s'
      in  summ 0.0## 0# (fill 0# s1)

-- The non-allocating write control: write a preallocated pinned 2304 B
-- buffer end to end, read two elements back, allocate nothing.
{-# NOINLINE noallocWrite #-}
noallocWrite :: ForeignPtr Double -> Int -> IO Double
noallocWrite fp seed = withForeignPtr fp $ \p -> do
  let x = fromIntegral seed
      fill !i | i >= (288 :: Int) = pure ()
              | otherwise = pokeElemOff p i x >> fill (i + 1)
  fill 0
  a <- peekElemOff p 0
  b <- peekElemOff p 287
  pure $! a + b

-- The non-allocating read control: sum an equal-sized window of the
-- long-lived source, allocate and dirty nothing.
{-# NOINLINE noallocRead #-}
noallocRead :: Ptr Double -> Int -> IO Double
noallocRead p seed = do
  let go !acc !i | i >= (288 :: Int) = pure acc
                 | otherwise = do v <- peekElemOff p i
                                  go (acc + v) (i + 1)
  go (fromIntegral seed) 0

-- 1000 calls of the selected small operation, between two victim
-- iterations.
{-# NOINLINE interIter #-}
interIter :: (Int -> IO Double) -> Int -> IO Double
interIter one seed = do
  let go !acc !i | i >= 1000 = pure acc
                 | otherwise = do v <- one (seed + i)
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
  naFp <- mallocForeignPtrBytes (288 * 8)
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
    let interOne
          | "inter" `elem` args =
              Just (\k -> fillSum 288 (fromIntegral k))
          | "interbig" `elem` args =
              Just (\k -> fillSum 450 (fromIntegral k))
          | "interunboxed" `elem` args =
              Just (\k -> fillSumUnpinned 288 (fromIntegral k))
          | "interunboxedbig" `elem` args =
              Just (\k -> fillSumUnpinned 450 (fromIntegral k))
          | "internoalloc" `elem` args = Just (noallocWrite naFp)
          | "internoallocr" `elem` args = Just (noallocRead src)
          | otherwise = Nothing
    sprayT <- newIORef (0 :: Double)
    let victimLoop lo hi = forM_ [lo .. hi :: Int] $ \i -> do
          case interOne of
            Nothing -> pure ()
            Just one -> do
              c0 <- getMonotonicTime
              _ <- interIter one (i * 1000)
              c1 <- getMonotonicTime
              modifyIORef' sprayT (+ (c1 - c0))
          _ <- victimIter src i
          pure ()
    t0 <- getMonotonicTime
    victimLoop 1 150
    t1 <- getMonotonicTime
    s1 <- readIORef sprayT
    victimLoop 151 300
    t2 <- getMonotonicTime
    s2 <- readIORef sprayT
    m <- memGiB
    putStrLn ("victim: first half " ++ show ((t1 - t0 - s1) / 150 * 1000)
              ++ " ms/iter, second half "
              ++ show ((t2 - t1 - (s2 - s1)) / 150 * 1000)
              ++ " ms/iter; mem in use: " ++ show m ++ " GiB")
```

</details>
