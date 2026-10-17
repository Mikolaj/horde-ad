# GHC issue comment: two more loops that reload a loop-read value from the C stack on every iteration, one spilled around a C call before the loop

Posted 2026-10-17 as a comment on GHC [#27742](https://gitlab.haskell.org/ghc/ghc/-/work_items/27742), horde-ad's own issue (`docs/ghc-issue-linear-regalloc-order.md`); this file stays as the record of the comment, the text from "Two more loops" down being the body as posted. Verified with GHC HEAD 10.1.20260918 and 9.14.1, which give the same counts, from the files as shown here. Read on 2026-10-17: the issue's description and all its notes. Mikolaj's note of 2026-08-29 already states the eviction mechanism of the second loop, without a reproducer, so the comment offers the reproducer and figures and does not repeat the mechanism. His note of 2026-09-05 shows `-fregs-graph` doing worse on related code, so the comment says that `-fregs-graph` does better on this loop only. AndreasK's note of 2026-08-31 names SCC-based loop detection, and on 2026-09-15 he linked the issue from his open proof of concept GHC [!16693](https://gitlab.haskell.org/ghc/ghc/-/merge_requests/16693), "regalloc-linear: choose free registers by liveness-derived hints", not built here; the comment asks whether either covers both loops. The prose is ASD-STE100 Simplified Technical English.

Two more loops where the linear allocator keeps a value that the loop reads in a C stack slot and reloads it on every iteration. Both reproducers need only `base`. HEAD (10.1.20260918, a build of `wip/T27737` on master e2d5702699 with local simplifier patches) and 9.14.1 give the same counts.

The first has a cause that this issue does not show: the value is live across a C call before the loop. `sumCopy` copies a buffer with `copyAddrToAddrNonOverlapping#`, which calls `memcpy`, and then sums the products of the two buffers. Three values are live across the call: the two addresses and the length. The addresses go to `%rbx` and `%r14`, and `saveClobberedTemps` spills the length ([Linear.hs, line 672][save]). The loop header takes the assignment of its first predecessor, where the length is in memory ([JoinToTargets.hs, lines 134-139][first]). So the loop reloads the length at every element ([Linear.hs, lines 1027-1032][load]), although it does not use `%rdx`, `%rsi`, `%rdi` or `%r8` to `%r11`. With `-DCOPY -DDOT`:

```
.LcBL:
	movsd (%r14,%rax,8),%xmm1
	mulsd (%rbx,%rax,8),%xmm1
	addsd %xmm1,%xmm0
	incq %rax
.LcBD:
	movq 64(%rsp),%rcx
	cmpq %rcx,%rax
	jl .LcBL
```

With `-DDOT` alone, there is no copy, and the loop compares with a register: `cmpq %rdi,%rax`. Instructions an element:

```
-DCOPY -DDOT    7.75
-DDOT           6.00
-DCOPY          4.75
no flag         4.00
```

With `-DCOPY` alone, only two values are live across the call, both stay in registers, and the 0.75 an element is the work of `memcpy`. Thus the reload costs 1 of the 7.75.

<details><summary>Reproducer 1</summary>

`Lib.hs`:

```haskell
{-# LANGUAGE CPP, MagicHash, UnboxedTuples #-}
-- A loop over a buffer whose address and length are live across a memcpy
-- (COPY), or with no copy before it.  DOT reads the source too, so that
-- three values are live across the call; without it, two are.
module Lib (sumCopy) where

import GHC.Exts
import GHC.IO (IO (..))

{-# NOINLINE sumCopy #-}
sumCopy :: Ptr Double -> Ptr Double -> Int -> IO Double
sumCopy (Ptr dst) (Ptr src) (I# n) = IO $ \ s0 ->
#if defined(COPY)
  case copyAddrToAddrNonOverlapping# src dst (n *# 8#) s0 of
    s1 -> go 0# 0.0## s1
#else
  go 0# 0.0## s0
#endif
  where
    go i acc s = case i >=# n of
      1# -> (# s, D# acc #)
      _  -> case readDoubleOffAddr# dst i s of
#if defined(DOT)
              (# s2, x #) -> case readDoubleOffAddr# src i s2 of
                (# s3, y #) -> go (i +# 1#) (acc +## x *## y) s3
#else
              (# s2, x #) -> go (i +# 1#) (acc +## x) s2
#endif
```

`Main.hs`:

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import Foreign.Marshal.Alloc (mallocBytes)
import Foreign.Storable (pokeElemOff)
import System.Environment (getArgs)
import Lib

main :: IO ()
main = do
  [ks, rs] <- getArgs
  let k = read ks :: Int
      reps = read rs :: Int
  src <- mallocBytes (8 * k)
  dst <- mallocBytes (8 * k)
  mapM_ (\ i -> pokeElemOff src i (fromIntegral i :: Double)) [0 .. k - 1]
  let go :: Int -> Double -> IO Double
      go 0 !acc = return acc
      go r !acc = do x <- sumCopy dst src k; go (r - 1) (acc + x)
  go reps 0 >>= print
```

`ghc -O -DCOPY -DDOT -outputdir copy3 -o Main-copy3 -ddump-asm -ddump-to-file Main.hs`, and the same with `-DDOT` (`none3`), `-DCOPY` (`copy2`) and no flag (`none2`) in place of `copy3`. `perf stat -e instructions:u ./Main-copy3 100000 100`, and the same with `200`; the difference divided by 10^7 is the count for one element.

</details>

The second is the eviction in a nested loop from my note of 2026-08-29 above, now with a reproducer. `fillA` and `fillB` copy a strided view, two elements a step. `fillB` computes `2 * st` once, out of the loops, so it has one more live value. Its pair loop reads the source base from `64(%rsp)` three times, spills and reloads the output base, and stores the source base back in the loop header `.Lc14Q`:

```
.Lc150:
	movq 64(%rsp),%rcx
	movsd 16(%rcx,%r11,8),%xmm0
	movsd %xmm0,16(%rax,%rdi,8)
	movq %r11,%rcx
	addq %r8,%rcx
	movq %rax,72(%rsp)
	movq 64(%rsp),%rax
	movsd 16(%rax,%rcx,8),%xmm0
	leaq 1(%rdi),%rcx
	movq 72(%rsp),%rax
	movsd %xmm0,16(%rax,%rcx,8)
	addq %rdx,%r11
	addq $2,%rdi
.LnI:
	movq 64(%rsp),%rcx
.Lc14Q:
	movq %rcx,64(%rsp)
	leaq 1(%rdi),%rcx
	cmpq %r10,%rcx
	jl .Lc150
```

With `-fregs-graph`, the same pair loop has no C stack reference. Instructions an element:

```
         linear   -fregs-graph
fillA    6.08     6.08
fillB    9.65     6.68
```

<details><summary>Reproducer 2</summary>

`Lib.hs`:

```haskell
{-# LANGUAGE MagicHash, UnboxedTuples, BangPatterns #-}
module Lib (BA (..), MBA (..), fillA, fillB) where

import GHC.Exts
import GHC.IO (IO (..))

data BA = BA ByteArray#
data MBA = MBA (MutableByteArray# RealWorld)

rd :: BA -> Int -> Double
rd (BA a) (I# i) = D# (indexDoubleArray# a i)

wr :: MBA -> Int -> Double -> IO ()
wr (MBA m) (I# i) (D# d) = IO (\s -> (# writeDoubleArray# m i d s, () #))

fillA :: BA -> MBA -> Int -> Int -> Int -> Int -> Int -> Int -> IO ()
fillA !v !out !n0 !s0 !n1 !s1 !nInner !st = outer0 0 0 0
  where
    outer0 !i0 !b0 !o0
      | i0 >= n0 = return ()
      | otherwise = outer1 0 b0 o0 >> outer0 (i0 + 1) (b0 + s0) (o0 + n1 * nInner)
    outer1 !i1 !b1 !o1
      | i1 >= n1 = return ()
      | otherwise = run o1 b1 >> outer1 (i1 + 1) (b1 + s1) (o1 + nInner)
    run !outPos !baseOff =
      let !oEnd = outPos + nInner
          inner !o !src
            | o + 1 >= oEnd =
                if o >= oEnd then return () else wr out o (rd v src)
            | otherwise = do
                wr out o (rd v src)
                let !srcNext = src + st
                wr out (o + 1) (rd v srcNext)
                inner (o + 2) (srcNext + st)
      in inner outPos baseOff

fillB :: BA -> MBA -> Int -> Int -> Int -> Int -> Int -> Int -> IO ()
fillB !v !out !n0 !s0 !n1 !s1 !nInner !st = outer0 0 0 0
  where
    !st2 = 2 * st
    outer0 !i0 !b0 !o0
      | i0 >= n0 = return ()
      | otherwise = outer1 0 b0 o0 >> outer0 (i0 + 1) (b0 + s0) (o0 + n1 * nInner)
    outer1 !i1 !b1 !o1
      | i1 >= n1 = return ()
      | otherwise = run o1 b1 >> outer1 (i1 + 1) (b1 + s1) (o1 + nInner)
    run !outPos !baseOff =
      let !oEnd = outPos + nInner
          inner !o !src
            | o + 1 >= oEnd =
                if o >= oEnd then return () else wr out o (rd v src)
            | otherwise = do
                wr out o (rd v src)
                wr out (o + 1) (rd v (src + st))
                inner (o + 2) (src + st2)
      in inner outPos baseOff
```

`Main.hs`:

```haskell
{-# LANGUAGE MagicHash, UnboxedTuples, BangPatterns #-}
module Main (main) where

import GHC.Exts
import GHC.IO (IO (..))
import System.Environment (getArgs)
import Lib

-- Copies a [64, 64, 32] view at strides [8192, 64, 2] of a 2^19-element
-- source K times, by fillA or fillB.
main :: IO ()
main = do
  [which, sk] <- getArgs
  let k = read sk :: Int
      fill = if which == "A" then fillA else fillB
  src <- IO (\s -> case newByteArray# (8# *# 524288#) s of
                     (# s1, m #) -> case unsafeFreezeByteArray# m s1 of
                       (# s2, a #) -> (# s2, BA a #))
  out <- IO (\s -> case newByteArray# (8# *# 131072#) s of
                     (# s1, m #) -> (# s1, MBA m #))
  let go 0 = return ()
      go i = fill src out 64 8192 64 64 32 2 >> go (i - 1 :: Int)
  go k
```

`ghc -O -outputdir linear -o Main-linear -ddump-asm -ddump-to-file Main.hs`, and the same with `-fregs-graph`. `perf stat -e instructions:u ./Main-linear B 100`, and the same with `300`; the difference divided by 200 * 131072 is the count for one element.

</details>

Would !16693, or the SCC-based loop detection mentioned above, cover both loops? In the first, the call forces the spill; only the reload inside the loop can go.

[save]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/CmmToAsm/Reg/Linear.hs#L672
[first]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/CmmToAsm/Reg/Linear/JoinToTargets.hs#L134-139
[load]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/CmmToAsm/Reg/Linear.hs#L1027-1032
