# GHC issue: the linear allocator spills loop invariants around fixed-register instructions, argument order picking which

Filed as [GHC work item 27742](https://gitlab.haskell.org/ghc/ghc/-/work_items/27742); this file stays as the filed record, the text from "## Summary" down being the filed body. Title: **x86 NCG: the linear allocator spills loop invariants around `mulq`/`shrq %cl` in a loop that fits its registers, and argument order picks which (35 vs 30 instructions, 24 possible)**. The prose is ASD-STE100 Simplified Technical English. The reproducer needs only `ghc` and `base`. Found in an array micro-benchmark in the orthotope repository, on the unmerged `speedup-strided-tovector` branch, which is not public, where the order came from the compiler version: one arm took 9% more instructions and 6 to 9% more time on GHC HEAD than on 9.14.1 with the same Cmm. [Work item 27737](https://gitlab.haskell.org/ghc/ghc/-/work_items/27737) and [work item 27738](https://gitlab.haskell.org/ghc/ghc/-/work_items/27738), filed from the same benchmark, are independent: different loops, and this loop shows neither. A tracker search on 2026-08-25 found no report of this; the adjacent items are at the end of the Summary.

## Summary

`mulq` reads `rax` and writes `rdx:rax`; `shrq %cl` reads its count from `rcx`. In a loop that has both and keeps about ten values live, the linear register allocator, the native code generator's default, gives registers to values in the order the values are first defined. Whatever that order leaves in `rax`, `rdx` and `rcx` is saved and restored around those instructions on every iteration, and the back edge gets moves to restore the loop head's assignment. The allocator never chooses those registers for the instructions' own operands, and the traffic is not forced by pressure: the loop below has ten live values and eleven allocatable registers, and a hand edit of the allocator's output (step 7) that keeps eight values in registers and reads two from the stack where they are used is 24 instructions with no store in it.

The reproducer has two functions, `fillA` and `fillB`, with character-identical bodies: an inner loop that computes `i `quot` s` as a multiply-high and a shift (the Granlund-Montgomery form), reads a table entry at the quotient, reads a source element at the offset it gives, and writes it out. They differ only in the order of their seven arguments. On GHC HEAD:

| HEAD 10.1.20260803 | `fillA` | `fillB` |
|---|---:|---:|
| `-O1` | 30 instructions, 1.19 ns | 35 instructions, 1.39 ns |
| `-O2` | 30, 1.19 ns | 35, 1.38 ns |
| `-O1 -fregs-graph` | 27, 1.15 ns | 27, 1.16 ns |
| `-O1`, `fillB`'s loop hand-edited (step 7) | 30, 1.17 ns | 24, 1.06 ns |

Instructions are per element of one call, from `perf stat -e instructions:u` at two iteration counts; times are per element, the smallest of five runs. The five instructions between the two orders cost 17% of the time; the eleven between the allocator's `fillB` and the hand edit cost 30%.

The difference is register traffic only. In `fillA` the shift count sits in `r9`, so the loop saves `v` around the `mulq` and `l` around the shift: four memory moves, a back edge of two. In `fillB` the count sits in `rdx`, `t` in `rsi` and `s` in `rcx`: the loop saves the count before the `mulq`, saves `t` to make room and reloads the count into `rsi`, saves `s` to put the count into `rcx`, reloads `s` and `t` for the multiplications, and needs four moves at the back edge: seven memory moves and two more register moves. `fillA`'s loop, from HEAD at `-O1`, laid out as the code generator does, body first:

```
.Lc2Xn:                          ; the body
        cmpq $64,%r9             ; the shift count is in r9
        setl %al
        movzbl %al,%eax
        negq %rax
        movq %rcx,72(%rsp)       ; save l: the shift needs rcx
        movq %r9,%rcx
        shrq %cl,%rdx
        andq %rax,%rdx           ; q
        movq %rdx,%rax
        imulq %rsi,%rax          ; q * s
        movq %r11,%rcx
        subq %rax,%rcx           ; i - q * s
        imulq %rdi,%rcx          ; * t
        movq (%r8,%rdx,8),%rax   ; tab[q]
        addq %rcx,%rax
        movq 64(%rsp),%rdx       ; reload v
        movsd (%rdx,%rax,8),%xmm0
        movsd %xmm0,(%r14,%r10,8)
        incq %r10
        incq %r11
.Lno:
        movq 72(%rsp),%rcx       ; reload l for the loop head
        movq %r14,%rax
.Lc2X9:                          ; the loop head
        cmpq %rcx,%r11           ; i >= l
        jge .Lc2Xf
.Lc2Xp:
        movq %rax,%r14
        movq %rbx,%rax           ; magic
        movq %rdx,64(%rsp)       ; save v: mulq writes rdx
        mulq %r11                ; magic * i
        testq %r9,%r9            ; a negative shift count is an error
        jge .Lc2Xn
```

`fillB`'s loop:

```
.Lc30w:                          ; the body
        cmpq $64,%rsi            ; the shift count is in rsi now
        setl %al
        movzbl %al,%eax
        negq %rax
        movq %rcx,80(%rsp)       ; save s: the shift needs rcx
        movq %rsi,%rcx
        shrq %cl,%rdx
        andq %rax,%rdx           ; q
        movq %rdx,%rax
        movq 80(%rsp),%rcx       ; reload s
        imulq %rcx,%rax          ; q * s
        movq %r11,%rcx
        subq %rax,%rcx           ; i - q * s
        movq 72(%rsp),%rax       ; reload t
        imulq %rax,%rcx          ; * t
        movq (%r8,%rdx,8),%rdx   ; tab[q]
        addq %rcx,%rdx
        movsd (%r14,%rdx,8),%xmm0
        movsd %xmm0,(%r9,%r10,8)
        incq %r10
        incq %r11
.LnS:
        movq %rsi,%rdx           ; four moves to restore the loop head
        movq 80(%rsp),%rcx       ; reload s
        movq %rax,%rsi
        movq %r14,%rax
.Lc30i:                          ; the loop head
        cmpq %rdi,%r11           ; i >= l
        jge .Lc30o
.Lc30y:
        movq %rax,%r14
        movq %rbx,%rax           ; magic
        movq %rdx,64(%rsp)       ; save the shift count: mulq writes rdx
        mulq %r11                ; magic * i
        movq %rsi,72(%rsp)       ; save t, to make room for the count
        movq 64(%rsp),%rsi       ; reload the count into rsi
        testq %rsi,%rsi
        jge .Lc30w
```

A sweep over 61 argument orders (the one written and 60 random) gives 30 instructions for 2 orders, 31 for 28, 32 for 19, 33 for 4, 34 for 2 and 35 for 6, each order the same on 9.14.1 and HEAD, with `-fobject-determinism` on or off: in this program the order is the whole input, and its range is 17%.

In the benchmark the order is the compiler's. One arm has this loop over `vector`'s Storable and Unboxed vectors, built with `-O1 -fspec-constr -fobject-determinism` on 9.14.1 and on HEAD. The optimised Cmm of the loop is the same on both, operation for operation; the block before it loads the same nine invariants from the stack in a different order and introduces the two counters in the other order. The loop is 35 instructions on 9.14.1 and 39 on HEAD, the four being moves as above. Over 250,357 elements one call counts 10,861,520 instructions on 9.14.1 and 11,857,295 on HEAD (9.2% more) and takes 0.524 ms against 0.556 ms (6.1% more; 8.4% net of the shared forcing pass the benchmark subtracts; 0.13 ns per element). A sibling arm with the same loop moves 9.3% and 8.6%. Without `-fobject-determinism` the first arm counts 10,844,757 and 10,844,821, the same code, and the sibling 11,071,566 against 10,570,916, in HEAD's favour: the flag moves the order too, and the allocator follows it. With `-fregs-graph` the arm counts 9,584,630 and 9,582,083, 12% and 19% below the linear allocator's two results.

Adjacent reports, none of them this one: #17823 shows a fixup block the linear allocator inserts because of its assignment order, and #18208 (!3038) answered it by preferring a value's past register; #26666 proposes that a value avoid other values' preferred registers; #13051 asks for a loop-aware spill cost in the graph allocator; #9041 is the same `mulq` loop shape, closed by strength reduction. The rule this loop lacks is of the kind the first two add: an instruction with a fixed-register operand inside a loop makes that register a poor home for a value live across the loop. None of them has the order of the values as the input. The latest comment on #7679 (2026-08-19) says of allocation-dependent loop speed that "we hit that sort of thing in other work again in recent times"; this is a minimal case of it, base only.

The cost is twofold: the code, 17% of a hot loop between two orders and 30% against what the registers permit; and measurement, since a difference of this size between compiler versions, or between builds that differ in an unrelated edit or in `-fobject-determinism`, reads as a code generation regression, and the instruction count moves with it.

## Steps to reproduce

1. Save the program below as `Repro.hs`. It imports `base` only.
2. Compile and time both orders; each run prints the time per element.

   ```
   ghc -O1 -fforce-recomp Repro.hs -o repro
   ./repro a 400     # ns/elem: 1.19
   ./repro b 400     # ns/elem: 1.39
   ```

3. Count: the instructions of a run at 40 calls minus a run at 20, over 20 times 250,357 elements, is 30.0 for `a` and 35.0 for `b`.

   ```
   perf stat -e instructions:u ./repro a 40
   perf stat -e instructions:u ./repro a 20
   ```

4. `ghc -O1 -S -fforce-recomp Repro.hs`. `Repro.s` has two `mulq`, in `Main_zdwfillA_info` and `Main_zdwfillB_info`; the conditional jump after each is its loop's back edge and the block it jumps to is the body. The loops are the ones above.
5. Steps 2 and 3 with `-fregs-graph`: 27.0 for both orders.
6. Steps 2 and 3 with `-O2`: the same counts as at `-O1`.
7. See that the loop fits. In `Repro.s`, replace the block from the label after the `integerToWord#` return point in `fillB` (its first instruction is `movq 16(%rbp),%rsi`) through the `jge` after the `mulq` with the block below, keeping the labels, and `ghc -O1 -fforce-recomp Repro.s -o repro-edit`. `./repro-edit b 400` prints the same result at 1.06 ns per element, and step 3 counts 24.0. The edit keeps the shift count in `rsi`, parks `s` and `t` on the stack before the loop and reads each where it is used, and drops the moves between `rax` and `r14`; every operation of the allocator's loop is kept.

   ```
   .Lc304:
           movq 16(%rbp),%rax
           movq %rax,72(%rsp)       ; t, parked
           movq 8(%rbp),%rax
           movq %rax,80(%rsp)       ; s, parked
           movq 24(%rbp),%rdi
           movq 32(%rbp),%r8
           movq 40(%rbp),%r9
           movq 64(%rbp),%r14
           movq 48(%rbp),%rsi
           decq %rsi                ; the shift count, in rsi throughout
           movq 56(%rbp),%r10
           xorl %r11d,%r11d
           jmp .Lc30i
   .Lc30w:
           cmpq $64,%rsi
           setl %al
           movzbl %al,%eax
           negq %rax
           movq %rsi,%rcx
           shrq %cl,%rdx
           andq %rax,%rdx           ; q
           movq %rdx,%rax
           imulq 80(%rsp),%rax      ; q * s
           movq %r11,%rcx
           subq %rax,%rcx           ; i - q * s
           imulq 72(%rsp),%rcx      ; * t
           movq (%r8,%rdx,8),%rdx   ; tab[q]
           addq %rcx,%rdx
           movsd (%r14,%rdx,8),%xmm0
           movsd %xmm0,(%r9,%r10,8)
           incq %r10
           incq %r11
   .Lc30i:
           cmpq %rdi,%r11           ; i >= l
           jge .Lc30o
   .Lc30y:
           movq %rbx,%rax           ; magic
           mulq %r11                ; magic * i
           testq %rsi,%rsi
           jge .Lc30w
   ```

```haskell
-- Reproducer for the order dependence of the linear register allocator.
-- Base only.
--
-- Build:     ghc -O1 -fforce-recomp Repro.hs -o repro
-- Time:      ./repro a 400 ; ./repro b 400        (prints ns per element)
-- Count:     perf stat -e instructions:u ./repro a 40, and again with 20;
--            the difference over 20 * 250357 is the instructions per element
-- Assembly:  ghc -O1 -S -fforce-recomp Repro.hs
--
-- fillA and fillB are one function written twice.  The bodies are
-- character-identical; only the order of the seven arguments differs.
-- Both are exported, so that each keeps its own symbol in the assembly.
-- The loop is a strided gather: for i below l, with q = i `quot` s
-- computed as a multiply-high and a shift,
--
--     out[o0 + i] = v[tab[q] + (i - q * s) * t]
--
-- The mode argument selects the function, and the second argument is the
-- number of calls.  j `quot` k is 0 for every call; it keeps the calls
-- from being combined into one.
{-# LANGUAGE BangPatterns, MagicHash, UnboxedTuples #-}
module Main (main, fillA, fillB) where

import Data.Bits (countLeadingZeros, shiftR)
import Foreign.Marshal.Alloc (mallocBytes)
import Foreign.Ptr (Ptr)
import Foreign.Storable (peekElemOff, pokeElemOff)
import GHC.Clock (getMonotonicTime)
import GHC.Exts (Word (..), timesWord2#)
import System.Environment (getArgs)

{-# INLINE mulhi #-}
mulhi :: Word -> Word -> Word
mulhi (W# a) (W# b) = case timesWord2# a b of (# hi, _ #) -> W# hi

-- Granlund-Montgomery round-up magic: i `quot` d == mulhi m i `shiftR` sh
-- for every non-negative Int i and every d above 1.
{-# INLINE gmMagic #-}
gmMagic :: Int -> (Word, Int)
gmMagic d = let !mg = fromInteger (2 ^ (63 + lg) `div` toInteger d + 1)
                !sh = lg - 1
            in  (mg, sh)
  where !lg = 64 - countLeadingZeros (fromIntegral d - 1 :: Word)

{-# NOINLINE fillA #-}
fillA :: Ptr Double -> Int -> Int -> Ptr Int -> Int -> Int -> Ptr Double -> IO ()
fillA !out !s !t !tab !o0 !l !v = go 0 o0
  where !gm = gmMagic s
        !magic = fst gm
        !gsh = snd gm
        go !i !o
          | i >= l = return ()
          | otherwise = do
              let !q = fromIntegral (mulhi magic (fromIntegral i) `shiftR` gsh)
              b <- peekElemOff tab q
              x <- peekElemOff v (b + (i - q * s) * t)
              pokeElemOff out o x
              go (i + 1) (o + 1)

{-# NOINLINE fillB #-}
fillB :: Int -> Int -> Int -> Ptr Int -> Ptr Double -> Int -> Ptr Double -> IO ()
fillB !s !t !l !tab !out !o0 !v = go 0 o0
  where !gm = gmMagic s
        !magic = fst gm
        !gsh = snd gm
        go !i !o
          | i >= l = return ()
          | otherwise = do
              let !q = fromIntegral (mulhi magic (fromIntegral i) `shiftR` gsh)
              b <- peekElemOff tab q
              x <- peekElemOff v (b + (i - q * s) * t)
              pokeElemOff out o x
              go (i + 1) (o + 1)

main :: IO ()
main = do
  [mode, ks] <- getArgs
  let k = read ks :: Int
      -- a [97, 89, 29] array read as the view [97, 29, 89] with strides
      -- [2581, 1, 29]: 97 * 29 runs of s = 89 elements at stride t = 29
      l = 97 * 89 * 29
      s = 89
      t = 29
  out <- mallocBytes (8 * l)
  v <- mallocBytes (8 * l)
  mapM_ (\i -> pokeElemOff v i (fromIntegral i :: Double)) [0 .. l - 1]
  tab <- mallocBytes (8 * 97 * 29)
  mapM_ (\(i, b) -> pokeElemOff tab i b)
        (zip [0 ..] [a * 2581 + b | a <- [0 .. 96], b <- [0 .. 28]])
  t0 <- getMonotonicTime
  case mode of
    "a" -> mapM_ (\j -> fillA out s t tab (j `quot` k) l v) [0 .. k - 1]
    _   -> mapM_ (\j -> fillB s t l tab out (j `quot` k) v) [0 .. k - 1]
  x <- peekElemOff out (l - 1)
  print (x :: Double)
  t1 <- getMonotonicTime
  putStrLn ("ns/elem: " ++ show ((t1 - t0) * 1e9 / fromIntegral (k * l)))
```

## Expected behavior

The same loop gets the same code whatever the order of its values, and that code is near the 24 instructions of step 7, which use nothing the allocator does not have: no value saved and restored around an instruction on every iteration when the instruction's register can be kept for the loop's temporaries, or the value kept in memory and read once where it is used, as the graph allocator does with three invariants here and the hand edit with two.

## Workarounds

**`-fregs-graph`**: 27 instructions for both orders, and the benchmark's arm at one count on 9.14.1 and HEAD; `{-# OPTIONS_GHC -fregs-graph #-}` selects it per module, and the benchmark's agreement test passes on binaries built with it. It is not a general answer: #7679, still open, records the nofib regression for which it left `-O2`'s default, up to 10% on `fannkuch-redux`, attributed in its latest comment to a different allocation changing instruction encoding lengths in a loop. It trades one lottery for another, measured here on this loop only.

**Reordering the arguments** is not a workaround: 2 orders of 61 reach 30, the good order is not visible from the source, and an edit or another compiler version moves it.

## Environment

* GHC version used: HEAD 10.1.20260803 (commit d415f38a75). 9.10.3, 9.12.4 and 9.14.1 reproduce the same: the same instruction counts for both orders, with `-fregs-graph` and at `-O2`, and loops identical to HEAD's apart from label names. The benchmark measurement is on 9.14.1 and HEAD.

Optional:

* Operating System: Linux (kernel 7.0.0-30-generic)
* System Architecture: x86_64 (AMD Ryzen 7 5800X, Zen 3)
* Other tools: gcc 13.3.0 as the assembler; `perf` for the instruction counts; `vector` 0.13.2.0 and criterion 1.6.5.0 in the benchmark only

/label ~"T::bug"

/label ~"needs triage"
