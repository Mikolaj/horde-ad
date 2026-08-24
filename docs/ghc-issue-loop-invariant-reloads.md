# GHC issue: one extra live value across an inner loop makes the loop reload its invariants every iteration

Filed as [GHC work item 27737](https://gitlab.haskell.org/ghc/ghc/-/work_items/27737); this file stays as the filed record, the text from "## Summary" down being the filed body, drafted 2026-08-24 and verified on ghc-9.12.4 and on HEAD at 10.1.20260803. Title: **x86 codegen: an inner loop reads its loop-invariant free variables from the closure on every iteration when the enclosing recursion keeps one more value live across the loop**. The prose is ASD-STE100 Simplified Technical English. The reproducer needs only `ghc`: its one import beyond `base` is the boot library `array`. The defect was found in an array micro-benchmark in the orthotope repository, on the unmerged `speedup-strided-tovector` branch, which is not public, and everything this report needs is in the reproducer. The related report about a redundant `test` in the same loops is filed as [GHC work item 27738](https://gitlab.haskell.org/ghc/ghc/-/work_items/27738), its record beside this file as `docs/ghc-issue-redundant-test-after-dec.md`; the two defects are independent.

## Summary

The reproducer has two functions, `fillU` and `fillR`. Both fill a new array from a strided view: an outer recursion walks the dimensions of a view, and at its leaf a local function `writeRun` copies one run of elements with a tight loop of loads and stores. The source text of `writeRun` and its loop is character-identical in the two functions. The functions differ in how the output position crosses the recursion, and these are the two natural ways to write it: `fillR`'s recursion returns the next output position, an `Int`, through the bind, and `fillU`'s recursion returns unit and recomputes the position from a table of precomputed output strides instead. So in `fillR` the value `outPos` is live across the inner loop, and in `fillU` it is not.

That one difference changes the code of the identical inner loop. `fillU`'s loop loads its invariants once, before the loop, and the body is seven instructions:

```
        movq 28(%rbx),%rax        ; before the loop: out base
        movq 36(%rbx),%rcx        ; before the loop: source base
        movq 44(%rbx),%rdx        ; before the loop: element stride
        movq 52(%rbx),%rbx        ; before the loop: the run length
        jmp .Ltest
.Lbody:
        movsd 16(%rcx,%rdi,8),%xmm0
        movsd %xmm0,16(%rax,%rsi,8)
        incq %rsi
        addq %rdx,%rdi
        decq %rbx
.Ltest:
        testq %rbx,%rbx
        jg .Lbody
```

`fillR`'s loop is ten instructions, and the three extra are memory reads that run on every iteration: the element stride and both base pointers are read from the closure again for every element:

```
.Lbody:
        movq 20(%rbx),%rax        ; reload: element stride
        movq 12(%rbx),%rcx        ; reload: source base
        movsd 16(%rcx,%rsi,8),%xmm0
        movq 4(%rbx),%rcx         ; reload: out base
        movsd %xmm0,16(%rcx,%rdi,8)
        incq %rdi
        addq %rax,%rsi
        decq %r14
.Ltest:
        testq %r14,%r14
        jg .Lbody
```

The same contrast, at the same instruction counts, appears in four configurations: `-O1 -fspec-constr` (where it was found), `-O2`, `-O1 -fspec-constr -fregs-graph` (so the graph register allocator does not correct it), and GHC HEAD at 10.1.20260803, with the in-loop reload count at three in each. The benchmark where the defect was found has the same one-change contrast over `vector`'s Storable vectors, whose closure is wider because each vector is an address and a ForeignPtrContents, and there the reload body has a fourth extra read, a dead one, its result overwritten two instructions later without a use. Those two loop bodies were confirmed in the linked binary and its `-g3` twin, at 40 bytes over 11 instructions against 24 bytes over 7, and the arms that carry the reload body ran 6 to 22 percent behind their paired controls, worst on the longest runs, which is the signature of a per-element cost.

The registers are not short: the ten-instruction body has three loop variables, and the three reloaded invariants plus the one value that is live across the loop make seven values against the fifteen registers the code generator allocates over. What the reproducer shows is only the trigger: one more value live across the loop, and the invariants stop being kept in registers.

## Steps to reproduce

1. Save the program below as `Repro.hs`. Its one import beyond `base` is the boot library `array`, so no package setup is necessary.
2. `ghc -O1 -fspec-constr -S -fforce-recomp Repro.hs`
3. In `Repro.s`, find the two copies of the inner loop: the two blocks that contain a pair of `movsd` instructions. Each sits in a lifted local function emitted next to its parent's worker: `fillU`'s copy is above the `Main_zdwfillU_info` symbol and has the invariant loads before the loop; `fillR`'s copy is above the `Main_zdwfillR_info` symbol and has the three reloads inside the loop.
4. The contrast is the same at `-O2` and with `-fregs-graph` added.

`Repro.hs`:

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import Data.Array.Base (unsafeAt, unsafeWrite)
import Data.Array.ST (STUArray, newArray_, runSTUArray)
import Data.Array.Unboxed (UArray, elems, listArray)

-- Both functions fill an array from a strided view, walking the outer
-- dimensions as an odometer (osh sizes, oats strides) and copying at the
-- leaf a run of sInner elements read at stride tInner. The inner loops
-- are character-identical; the functions differ in how the output
-- position crosses the recursion: fillR threads it back through the
-- bind, fillU recomputes it from a table of precomputed output strides.

fillR :: [Int] -> [Int] -> UArray Int Double -> UArray Int Double
{-# NOINLINE fillR #-}
fillR sh ats !v = runSTUArray $ do
  out <- newArray_ (0, l - 1)
  let writeRun !outPos !baseOff =
        let inner !d !src !o
              | d <= 0    = return ()
              | otherwise = do
                  unsafeWrite out o (unsafeAt v src)
                  inner (d - 1) (src + tInner) (o + 1)
        in  inner sInner baseOff outPos
      go !lev !outPos !baseOff
        | lev >= rOuter = writeRun outPos baseOff >> return (outPos + sInner)
        | otherwise =
            let !n  = unsafeAt oshV lev
                !st = unsafeAt oatsV lev
                dim !k !op !boff
                  | k <= 0    = return op
                  | otherwise = go (lev + 1) op boff
                                >>= \op' -> dim (k - 1) op' (boff + st)
            in  dim n outPos baseOff
  _ <- go 0 0 0
  return out
  where l = product sh
        !sInner = last sh
        !tInner = last ats
        !rOuter = length sh - 1
        oshV, oatsV :: UArray Int Int
        !oshV  = listArray (0, rOuter - 1) (init sh)
        !oatsV = listArray (0, rOuter - 1) (init ats)

fillU :: [Int] -> [Int] -> UArray Int Double -> UArray Int Double
{-# NOINLINE fillU #-}
fillU sh ats !v = runSTUArray $ do
  out <- newArray_ (0, l - 1)
  let writeRun !outPos !baseOff =
        let inner !d !src !o
              | d <= 0    = return ()
              | otherwise = do
                  unsafeWrite out o (unsafeAt v src)
                  inner (d - 1) (src + tInner) (o + 1)
        in  inner sInner baseOff outPos
      go !lev !outPos !baseOff
        | lev >= rOuter = writeRun outPos baseOff
        | otherwise =
            let !n  = unsafeAt oshV lev
                !st = unsafeAt oatsV lev
                !os = unsafeAt oostV lev
                dim !k !op !boff
                  | k <= 0    = return ()
                  | otherwise = go (lev + 1) op boff
                                >> dim (k - 1) (op + os) (boff + st)
            in  dim n outPos baseOff
  go 0 0 0
  return out
  where l = product sh
        !sInner = last sh
        !tInner = last ats
        !rOuter = length sh - 1
        oshV, oatsV, oostV :: UArray Int Int
        !oshV  = listArray (0, rOuter - 1) (init sh)
        !oatsV = listArray (0, rOuter - 1) (init ats)
        !oostV = listArray (0, rOuter - 1) (init (drop 1 (scanr (*) 1 sh)))

main :: IO ()
main = do
  let v = listArray (0, 59999) [0 .. 59999] :: UArray Int Double
      sh = [10, 20, 30]
      ats = [400, 60, 7]
  print (sum (elems (fillR sh ats v)), sum (elems (fillU sh ats v)))
```

## Expected behavior

Both copies of the loop carry the seven-instruction body, with the invariants loaded into registers before the loop. And in the wider-closure variant of the same shape, at minimum no dead load: a read whose result is overwritten before a use costs an instruction, a load port and a cache access on every iteration and can never pay.

## Workarounds

Restructure the source so that nothing is live across the inner loop: make the recursion return unit and recompute the output position from a table of precomputed output strides, as `fillU` does. This is what the benchmark that found the defect ships. The workaround is fragile the way source workarounds for code generation are: the two functions are equal in meaning, the faster one is the less direct one, and nothing warns when a later edit moves a live range back across the loop.

## Environment

- GHC 9.12.4 (release) and GHC HEAD at 10.1.20260803, native code generator, x86-64.
- Linux; `base` and the boot library `array` only. The wider-closure variant with the dead load uses `vector` 0.13.2.0.
- Observed at `-O1 -fspec-constr`, `-O2`, and with `-fregs-graph`; the dump and the linked binary agree.

/label ~"T::bug"

/label ~"needs triage"
