# GHC issue: in the linear register allocator, R1 stays allocated at a loop's own return continuation, so the back edge pays fixup moves on every iteration

Filed as GHC [#27981](https://gitlab.haskell.org/ghc/ghc/-/work_items/27981) on 2026-10-17; the text from "## Summary" down is the filed body, in the tracker's bug template. Title: **NCG linear regalloc: R1 stays allocated at a loop's own return continuation, so the back edge pays fixup moves on every iteration**. Verified with GHC HEAD 10.1.20260918 and 9.14.1. The second trigger of the same fixup, found in a loop of orthotope, is GHC [#27980](https://gitlab.haskell.org/ghc/ghc/-/work_items/27980), filed from `docs/ghc-issue-regalloc-pref-clash.md`. The program of `docs/ghc-issue-rnf-fixup-test-mr16673-comment.md`, which needs `vector`, has this trigger too, as its allocator liveness dump shows. A tracker search of 2026-10-16 found no report and no open MR that changes how real registers are released at a jump; a search on 2026-10-17 of the issues filed since then found none. The cited lines were checked at master f93d523c, where the three allocator files are the same as in the HEAD build. The prose is ASD-STE100 Simplified Technical English. Open: GHC [!16673](https://gitlab.haskell.org/ghc/ghc/-/merge_requests/16673), the fix for GHC [#27800](https://gitlab.haskell.org/ghc/ghc/-/work_items/27800), was not built, so that it does not remove this fixup is inferred from its diff; the possible fix is not tested; other targets were not checked.

## Summary

The linear register allocator can put fixup moves on the back edge of a loop that evaluates a value on each iteration. The block that evaluates the value writes R1 (`%rbx` on x86-64). If the value is already tagged, the block branches to the loop's return continuation. R1 is not live into the continuation, but R1 dies only at the next instruction, the jump to the block that enters the value. So R1 is still allocated at the branch.

At the branch, `joinToTargets_first` records the free registers for the continuation ([JoinToTargets.hs, lines 134-139][jtt-first]). It releases only `to_free`, the registers of virtual registers that are not live into the target ([lines 98-104][to-free]). R1 is a real register, so it stays allocated in the recorded set, and `initBlock` starts the continuation with this set ([Linear.hs, lines 376-378][init-again]). (For a block with no recorded assignment, `initBlock` allocates only the real registers that are live into the block, [lines 364-371][init-first].)

When the loop header holds a loop variable in `%rbx`, the continuation cannot reload the variable into `%rbx`. It reloads it into the first free register, which the header uses for another variable, so that variable is reloaded into a third register. The allocator then adds a fixup block on the back edge from the continuation to the header, and every iteration pays its moves. The header holds a variable in `%rbx` when the block that enters the loop leaves `%rbx` free, for example the continuation of a call that reads R1.

This is not #27800. In #27800, the procedure entry and a return continuation enter the loop at two different blocks, so the edges inside the loop disagree. Here one path enters the loop, and the fixup is on the back edge from the loop's own return continuation. !16673, the fix for #27800, defers only return continuations whose jumps go into a loop, so it probably does not change this case. I did not build it. #27980 reports a second trigger of a fixup on the same back edge.

A possible fix, not tested: in `joinToTargets_first`, also release the real registers that are not live into the target.

## Steps to reproduce

`Lib.hs`:

```haskell
{-# LANGUAGE CPP, MagicHash, UnboxedTuples #-}
module Lib (V (..), nf) where

import GHC.Exts

data V = V [Int] Int () (Array# Double)

{-# NOINLINE ping #-}
ping :: [Int] -> Int
ping = foldr (\_ c -> c + 1) 0

nf :: V -> ()
nf (V sh n e arr) = case ping sh of
  I# 0# -> n `seq` e `seq` ()
  I# _ -> case n of
    I# n# -> e `seq`
      let go i | isTrue# (i >=# n#) = ()
               | otherwise = case indexArray# arr i of
                   (# x #) -> case x of D# _ -> go (i +# 1#)
      in go 0#
#if defined(INL)
{-# INLINE nf #-}
#else
{-# NOINLINE nf #-}
#endif
```

`Main.hs`:

```haskell
module Main (main) where

import GHC.Arr (Array (..), listArray)
import Lib
import System.Environment (getArgs)

{-# OPAQUE force #-}
force :: Int -> V -> ()
force r v = nf (pass r v)

{-# OPAQUE pass #-}
pass :: Int -> a -> a
pass _ x = x

mk :: Int -> V
mk k = case listArray (0, k - 1) [fromIntegral i | i <- [0 .. k - 1]] of
  Array _ _ _ a -> V [k] k () a

main :: IO ()
main = do
  [k, reps] <- map read <$> getArgs
  let flat = mk k
      loop :: Int -> ()
      loop 0 = ()
      loop r = case force r flat of () -> loop (r - 1)
  print (loop reps)
```

1. `ghc -O -outputdir noinline -o Main-noinline -ddump-asm -ddump-asm-stats -ddump-to-file Main.hs`
2. `ghc -O -DINL -outputdir inline -o Main-inline -ddump-asm -ddump-asm-stats -ddump-to-file Main.hs`
3. `perf stat -e instructions:u ./Main-noinline 100000 100`, the same with `200`, and the same for `./Main-inline`. The difference of each pair, divided by 10^7, is the count for one element.

The two copies of the loop have the same Core up to names (`-fforce-recomp -ddump-simpl -dsuppress-all -dsuppress-uniques` added to steps 1 and 2, white space shortened): `case >=# i ww1 of { __DEFAULT -> case indexArray# ww2 i of { (# ipv #) -> case ipv of { D# ds1 -> jump go (+# i 1#) } }; 1# -> (##) }` in the worker `$wnf`, and the same with `-> () }` where `nf` is inlined into `force`.

### Results

The listings below are HEAD's; 9.14.1 has the same code under other labels. In `noinline/Lib.dump-asm`, the worker `$wnf` enters the loop from the continuation of the call to `ping`, with the array in `%rbx` and the counter in `%rcx`:

```
.LcX0:
	testq %rbx,%rbx
	je .LcX3
.LcX4:
	movq 8(%rbp),%rax
	movq 16(%rbp),%rbx
	xorl %ecx,%ecx
	jmp .LcXh
```

The loop's return continuation `.LcXr` reloads the array into `%rcx` and the counter into `%rdx`, and the fixup block `.Ln8` moves them on every element:

```
.LcXr:
	movq 16(%rbp),%rax
	movq 24(%rbp),%rcx
	movq 8(%rbp),%rdx
	incq %rdx
	addq $8,%rbp
.Ln8:
	movq %rcx,%rbx
	movq %rdx,%rcx
.LcXh:
	cmpq %rax,%rcx
	jge .LcX3
.LcXs:
	movq 24(%rbx,%rcx,8),%rax
	movq $.Lblock_cXr_info,-8(%rbp)
	movq %rax,%rbx
	movq %rcx,(%rbp)
	addq $-8,%rbp
	testb $7,%bl
	jne .LcXr
```

`noinline/Lib.dump-asm-stats` has `(0, 0, 0, 2, 0, 7)` for `(allocs, clobbers, loads, joinRR, joinRM, reg_reg_moves_remaining)`. With `-fforce-recomp -ddump-asm-liveness` added to step 1, `liveVRegsOnEntry` has `(cXr, {})`. In `cXs`, `%r1` is born at `movq %vI_cXp,%rbx` and dies at `jmp .LcXt`, after `jne .LcXr`.

In the inlined copy (`inline/Main.dump-asm`, `force`), the block that enters the loop also evaluates a value, `e`. The header does not use `%rbx`, and the continuation reloads into the header's registers:

```
.Lc2OI:
	movq 16(%rbp),%rax
	movq 24(%rbp),%rcx
	movq 8(%rbp),%rdx
	incq %rdx
	addq $8,%rbp
.Lc2Oy:
	cmpq %rcx,%rdx
	jge .Lc2OE
```

Instructions an element, 0 bytes allocated in all:

```
                 HEAD    9.14.1
Main-noinline    16.00   16.00
Main-inline      14.00   14.00
```

The difference is the two moves of `.Ln8`.

## Expected behavior

The loop's return continuation reloads the loop variables into the registers of the header, and the back edge has no fixup moves, as in the inlined copy.

## Environment

* GHC version used: HEAD 10.1.20260918 (`wip/T27737` at 6913545fd3, on master e2d5702699, with local simplifier patches; Reg/Linear.hs, Reg/Linear/JoinToTargets.hs and Reg/Linear/Base.hs are the same as at master f93d523c) and 9.14.1, which give the same code up to labels.

Optional:

* Operating System: Linux
* System Architecture: x86_64

[jtt-first]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/CmmToAsm/Reg/Linear/JoinToTargets.hs#L134-139
[to-free]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/CmmToAsm/Reg/Linear/JoinToTargets.hs#L98-104
[init-again]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/CmmToAsm/Reg/Linear.hs#L376-378
[init-first]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/CmmToAsm/Reg/Linear.hs#L364-371

/label ~"T::bug"
/label ~"register allocation"
/label ~"NCG backend"
/label ~"runtime perf"
/label ~"needs triage"
