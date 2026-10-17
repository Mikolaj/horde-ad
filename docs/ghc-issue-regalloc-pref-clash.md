# GHC issue: in the linear register allocator, a loop's own return continuation reloads a value into its preferred register, not into the header's, so the back edge pays a fixup move on every iteration

Filed as GHC [#27980](https://gitlab.haskell.org/ghc/ghc/-/work_items/27980) on 2026-10-17; the text from "## Summary" down is the filed body, in the tracker's bug template. Title: **NCG linear regalloc: a loop's return continuation reloads a value into its preferred register, not the header's, so every iteration pays a fixup move**. Verified with GHC HEAD 10.1.20260918 and 9.14.1, which give the same code up to labels; the listings are HEAD's. Found in a loop of orthotope. The body was filed with `#XXXXX` in place of GHC [#27981](https://gitlab.haskell.org/ghc/ghc/-/work_items/27981), filed later from `docs/ghc-issue-regalloc-stale-r1.md`, and the filed description was edited the same day to name it, as the text here does. A tracker search of 2026-10-16 found no report; a search on 2026-10-17 of the issues filed since then found none. A side finding, a dead `leaq SPEC_closure+1` in the loop, is left out: horde-ad reported it on GHC [#8327](https://gitlab.haskell.org/ghc/ghc/-/work_items/8327) (`docs/ghc-issue-cmm-sink-dead-loop-comment.md`). The cited lines were checked at master f93d523c, where the allocator files are the same as in the HEAD build. The prose is ASD-STE100 Simplified Technical English. Open: GHC [!16673](https://gitlab.haskell.org/ghc/ghc/-/merge_requests/16673) and GHC [!16693](https://gitlab.haskell.org/ghc/ghc/-/merge_requests/16693) were not built, so that they do not remove this fixup is inferred from their diffs; the possible fix is not tested; other targets were not checked.

## Summary

When the linear register allocator puts a virtual register into a real register, it takes the virtual register's preferred real register if that register is free, and otherwise the first free register ([Linear.hs, lines 900-911][final-reg]). The preferred register is the first register that a block assignment records for the virtual register ([`findPrefRealReg`][pref], [`updateBlockAssignment`][update]). The comment on `findPrefRealReg` gives the purpose:

```
-- The preferred register is simply the first one the variable
-- was assigned to (if any). This way when we allocate for a loop
-- variables are likely to end up in the same registers at the
-- end and start of the loop, avoiding redundant reg-reg moves.
```

A loop with a return continuation in it can get the opposite result:

1. The loop header gets its assignment from the entry path, which is allocated first. On that path, another value holds the preferred register of a loop variable. That other value is dead in the loop. So the header holds the loop variable in a different register.
2. The loop's own return continuation is allocated later. There the preferred register is free, so the continuation reloads the loop variable into it.
3. When it chooses that register, the allocator does not look at the assignment of the jump target, the header, which already exists. So `joinToTargets` puts a fixup block on the back edge ([JoinToTargets.hs, lines 106-115][jtt]), and every iteration pays its moves.

This trigger is different from #27800 and from #27981. In #27800, the procedure entry and a return continuation enter the loop at two different blocks, so the edges inside the loop disagree. In #27981, R1 stays allocated at the return continuation, so the header's register is not free there. Here no stale real register is involved: the continuation takes the value's preferred register, which is not the header's. !16673, the fix for #27800, defers only return continuations whose jumps go into a loop, so it probably does not change this case. I did not build it. Related: the fix for #18208 introduced the first-assignment preference, and #26666 proposes to avoid the preferred registers of other virtual registers.

A possible fix, not tested: when the allocator writes a virtual register in a block whose jump target already has an assignment for that virtual register, it prefers the target's register if that register is free.

## Steps to reproduce

Save this as `pref.cmm`:

```c
#include "Cmm.h"

helper (W_ x)
{
    return (x + 1);
}

pref_clash (W_ a, W_ n, W_ m)
{
    W_ i, x;

    (W_ r) = call helper(n);
    if (r == 0) goto early;
    goto mid;

early:
    return (a);

mid:
    (W_ s) = call helper(r + a);
    if (s == 5) goto other;
    goto setup;

other:
    return (m);

setup:
    i = s + a + m;
    goto check;

check:
    if (i >= n) goto done;
    x = W_[a + i * 8];
    (W_ y) = call helper(x);
    i = i + 1;
    goto check;

done:
    return (i);
}
```

`ghc -O -no-hs-main -c -ddump-asm -ddump-asm-stats -ddump-to-file pref.cmm`

### Results

In `pref.dump-asm`, the continuation of the second call reloads `m` into `%rax`, and `m` is used on both branches. So the block that enters the loop gets `a` in `%rcx`. `a` got `%rax` first, in the continuation of the first call:

```
.Lc9:
	movq 8(%rbp),%rax
	testq %rbx,%rbx
	je .Lcb
...
.Lce:
	movq 24(%rbp),%rax
	cmpq $5,%rbx
	je .Lcg
.Lcf:
	movq 8(%rbp),%rcx
	movq 16(%rbp),%rdx
	movq %rcx,%rsi
	addq %rax,%rsi
	addq %rsi,%rbx
	jmp .Lci
```

In the loop's return continuation `.Lcl`, `m` is dead, and `a` is reloaded into `%rax`. The fixup block `.Ln4` moves it to `%rcx` on every iteration:

```
.Lcl:
	movq 8(%rbp),%rax
	movq 16(%rbp),%rdx
	movq 24(%rbp),%rbx
	incq %rbx
.Ln4:
	movq %rax,%rcx
.Lci:
	cmpq %rdx,%rbx
	jae .Lcm
.Lcj:
	movq (%rcx,%rbx,8),%rax
	movq $.Lblock_cl_info,(%rbp)
	movq %rbx,%rcx
	movq %rax,%rbx
	movq %rcx,24(%rbp)
	jmp helper
```

`pref.dump-asm-stats` has `(0, 0, 0, 1, 0, 8)` for `(allocs, clobbers, loads, joinRR, joinRM, reg_reg_moves_remaining)`.

The same happens in Haskell. `Lib.hs`:

```haskell
{-# LANGUAGE CPP, MagicHash, UnboxedTuples #-}
module Lib (nf) where

import GHC.Exts

{-# NOINLINE ping #-}
ping :: Int# -> Int#
ping x = x +# 1#

{-# NOINLINE nf #-}
nf :: Int# -> Int# -> Array# Double -> Int#
nf m n arr = case ping n of
  0# -> sizeofArray# arr
  r -> case ping (r +# sizeofArray# arr) of
#if defined(NODISP)
    5# -> 0#
#else
    5# -> m
#endif
    s -> let go i | isTrue# (i >=# n) = i
                  | otherwise = case indexArray# arr i of
                      (# x #) -> case x of D# _ -> go (i +# 1#)
         in go (m +# s)
```

`Main.hs`:

```haskell
{-# LANGUAGE MagicHash, UnboxedTuples #-}
module Main (main) where

import GHC.Exts
import Lib
import System.Environment (getArgs)

data A = A (Array# Double)

-- K evaluated boxes, so that every element pointer is tagged.
mk :: Int -> A
mk (I# k) = case runRW# build of (# _, a #) -> A a
  where
    build s0 = case newArray# k (D# 0.0##) s0 of
      (# s1, ma #) -> unsafeFreezeArray# ma (fill ma 0# s1)
    fill ma i s
      | isTrue# (i >=# k) = s
      | otherwise = fill ma (i +# 1#) (writeArray# ma i (D# (int2Double# i)) s)

-- Hides from the optimiser that each iteration's array is the same one.
{-# OPAQUE pass #-}
pass :: Int -> A -> A
pass _ x = x

main :: IO ()
main = do
  [k, reps] <- map read <$> getArgs
  case (mk k, k) of
    (A a, I# kk) -> do
      -- nf m n arr runs its loop from ping (ping n + k) + m = n + k + 2 + m,
      -- here 0, to n = k
      let m = negateInt# (kk +# kk +# 2#)
          go :: Int -> Int -> Int
          go 0 acc = acc
          go r acc = case pass r (A a) of
            A a' -> go (r - 1) (acc + I# (nf m kk a'))
      print (go reps 0)
```

1. `ghc -O -outputdir disp -o Main-disp -ddump-asm -ddump-asm-stats -ddump-to-file Main.hs`
2. `ghc -O -DNODISP -outputdir nodisp -o Main-nodisp -ddump-asm -ddump-asm-stats -ddump-to-file Main.hs`
3. `perf stat -e instructions:u ./Main-disp 100000 100`, the same with `200`, and the same for `./Main-nodisp`. The difference of each pair, divided by 10^7, is the count for one element.

The two variants differ only in the branch `5# -> m`, which the run never takes. Their loop Core is the same (`-fforce-recomp -ddump-simpl -dsuppress-all -dsuppress-uniques` added to steps 1 and 2, white space shortened):

```
joinrec { go i = case >=# i n of { __DEFAULT -> case indexArray# arr i of { (# ipv #) -> case ipv of { D# ds3 -> jump go (+# i 1#) } }; 1# -> i }; } in jump go (+# m ds1)
```

In `disp/Lib.dump-asm`, `arr` gets `%rax` first, in the continuation of the first call. `m` takes `%rax` in the continuation of the second call, so the header gets `arr` in `%rdx` and the counter in `%rax`. The loop's return continuation reloads `arr` into `%rax`, and the fixup block swaps the two registers through the C stack:

```
.LczO:
	movq 16(%rbp),%rcx
	movq 24(%rbp),%rax
	movq 8(%rbp),%rdx
	incq %rdx
.Ln5:
	movq %rax,64(%rsp)
	movq %rdx,%rax
	movq 64(%rsp),%rdx
.LczE:
	cmpq %rcx,%rax
	jge .LczK
```

In `nodisp/Lib.dump-asm` the continuation reloads into the header's registers:

```
.LczO:
	movq 16(%rbp),%rax
	movq 24(%rbp),%rcx
	movq 8(%rbp),%rdx
	incq %rdx
.LczE:
	cmpq %rax,%rdx
	jge .LczK
```

```
               joinRR in Lib.dump-asm-stats    instructions an element
               HEAD    9.14.1                  HEAD    9.14.1
Main-disp      1       1                       14.00   14.00
Main-nodisp    0       0                       12.00   12.00
```

All runs allocate 0 bytes an element.

## Expected behavior

The loop's return continuation reloads each loop variable into the register that the header holds it in, if that register is free, and the back edge has no fixup moves.

## Environment

* GHC version used: HEAD 10.1.20260918 (`wip/T27737` at 6913545fd3, on master e2d5702699, with local simplifier patches; Reg/Linear.hs, Reg/Linear/JoinToTargets.hs and Reg/Linear/Base.hs are the same as at master f93d523c) and 9.14.1, which give the same code up to labels.

Optional:

* Operating System: Linux
* System Architecture: x86_64

[final-reg]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/CmmToAsm/Reg/Linear.hs#L900-911
[pref]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/CmmToAsm/Reg/Linear.hs#L870-880
[update]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/CmmToAsm/Reg/Linear/Base.hs#L66-84
[jtt]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/CmmToAsm/Reg/Linear/JoinToTargets.hs#L106-115

/label ~"T::bug"
/label ~"register allocation"
/label ~"NCG backend"
/label ~"runtime perf"
/label ~"needs triage"
