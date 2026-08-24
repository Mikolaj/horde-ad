# GHC issue: the x86 native code generator tests a counter that dec has already set the flags for

Filed as [GHC work item 27738](https://gitlab.haskell.org/ghc/ghc/-/work_items/27738); this file stays as the filed record, the text from "## Summary" down being the filed body, drafted 2026-08-24 and verified on ghc-9.12.4 and on HEAD at 10.1.20260803. Title: **x86 NCG: a loop that counts down to zero ends in `dec`, `test`, `jg`, and the `test` repeats what `dec` established**. The prose is ASD-STE100 Simplified Technical English. The related report about per-element reloads in the same kernel is filed as [GHC work item 27737](https://gitlab.haskell.org/ghc/ghc/-/work_items/27737), its record beside this file as `docs/ghc-issue-loop-invariant-reloads.md`; the two defects are independent and each reproducer shows only its own. Two prior tracker items are adjacent and different: #14830 asks to emit `test r, r` in place of `cmp $0, r`, which GHC now does, and this report asks for the next step, to not emit the comparison at all where the flags are already correct; #27688 (single-bit tests through `bt`) is the same class of instruction-selection improvement on a different pattern.

## Summary

A loop that decrements an `Int` counter and stops at zero compiles, in the x86-64 native code generator, to a body that ends in three instructions: `decq %r; testq %r,%r; jg`. On x86-64, `dec` sets ZF, SF and OF from its result. `test r, r` sets ZF and SF from the same value and clears OF. So the `test` computes nothing that `dec` did not, except the state of OF.

In the code the reproducer produces, every path into the `test` comes from a `dec` of the same register: the loop's entry block decrements and jumps to the test, and the loop body decrements and falls into it. This is the shape:

```
        decq %rdi
        jmp .Ltest
.Lbody:
        movsd (%rax,%rsi,8),%xmm0
        movsd %xmm0,(%rcx,%rdx,8)
        incq %rdx
        addq %rbx,%rsi
        decq %rdi
.Ltest:
        testq %rdi,%rdi
        jg .Lbody
```

One caution decides how the correction must be done. `jg` reads ZF, SF and OF. After `dec`, OF is set when the decrement overflows, which happens only when the counter was the minimum `Int`; after `test`, OF is zero always. So `dec; jg` and `dec; test; jg` differ in exactly that one case. A correction therefore has three safe forms: reuse the flags only for conditions that do not read OF (`jne` covers a counter that reaches zero exactly, which this loop's counter does); or reuse them for `jg` where the counter's range is known; or keep the `test` only on paths whose flags are stale. The native code generator today has no tracking of the flags register at all, so it emits the comparison unconditionally, on every iteration of every such loop.

The cost is one instruction and three bytes per loop iteration. In the strided-copy kernel where this was noticed, removing the `test` by restructuring the source (a loop bounded on a rising cursor, `cmp` folded into the bound check) measured as a wash in a paired benchmark, so this report claims code size and decode bandwidth, not a measured speedup. The pattern is in every counted-down loop the native code generator emits, and count-down loops are what a compiler or a programmer writes exactly for the flags this backend then declines to use.

## Steps to reproduce

1. Save the program below as `Repro.hs`.
2. `ghc -O2 -S -fforce-recomp Repro.hs`
3. In `Repro.s`, find the inner loop of `copyRun`: the two `movsd` instructions. The loop ends in `decq`, and the block it falls into is `testq` of the same register and `jg`. Find the loop's entry edge: it also ends in `decq` of that register, followed by a jump to the `testq`.

`Repro.hs`:

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import Foreign.Marshal.Alloc (mallocBytes)
import Foreign.Ptr (Ptr)
import Foreign.Storable (peekElemOff, pokeElemOff)

-- A strided copy of one run: d elements read from src at stride t,
-- written at a contiguous cursor o. The falling counter d is compared
-- against zero at every iteration.
copyRun :: Ptr Double -> Ptr Double -> Int -> Int -> Int -> Int -> IO ()
{-# NOINLINE copyRun #-}
copyRun out v t d0 src0 o0 = inner d0 src0 o0
  where
    inner !d !src !o
      | d <= 0 = return ()
      | otherwise = do
          x <- peekElemOff v src
          pokeElemOff out o x
          inner (d - 1) (src + t) (o + 1)

main :: IO ()
main = do
  out <- mallocBytes (8 * 1000)
  v <- mallocBytes (8 * 8000)
  mapM_ (\i -> pokeElemOff v i (fromIntegral i :: Double)) [0 .. 7999]
  copyRun out v 8 1000 0 0
  x <- peekElemOff out 999
  print (x :: Double)
```

## Expected behavior

The loop's back edge branches on the flags that `decq` set: `decq %rdi; jne .Lbody` when the condition permits it, or `jg` where the counter's range is known not to reach the minimum `Int`, with the `testq` kept only on a path whose flags are stale. At minimum, a peephole that removes a `test r, r` whose every predecessor ends in an instruction that set the flags of `r`.

## Workarounds

None from Haskell source. Every formulation of a counted loop ends in one arithmetic instruction and one comparison: counting up ends in `cmp` against a bound, counting down ends in `dec` and `test`, and a loop bounded on a moving cursor ends in `cmp` against the bound register. The comparison is one instruction in each form, so the forms are equal and none reaches the flags reuse.

## Environment

- GHC 9.12.4 (release) and GHC HEAD at 10.1.20260803, native code generator, x86-64.
- Linux, GNU assembler.
- Also present, with the same shape, in a larger array benchmark compiled at `-O1 -fspec-constr`, so the pattern is not specific to `-O2`. The loops of that benchmark are also the loops of [work item 27737](https://gitlab.haskell.org/ghc/ghc/-/work_items/27737), whose defect is independent of this one.

/label ~"T::bug"

/label ~"needs triage"
