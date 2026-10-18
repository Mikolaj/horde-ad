# GHC issue comment: a third loop, in which the linear allocator stores and reloads, on every iteration, values that the loop never reads

Posted 2026-10-18 as a comment on GHC [#27742](https://gitlab.haskell.org/ghc/ghc/-/work_items/27742), horde-ad's own issue (`docs/ghc-issue-linear-regalloc-order.md`), after the comment of 2026-10-17 that `docs/ghc-issue-loop-reload-27742-comment.md` records; this file stays as the record of the comment, the text from "One more loop" down being the body as posted. Verified on 2026-10-18 with GHC HEAD 10.1.20260918 (`wip/T27737` at 6913545fd3 on master e2d5702699, with uncommitted patches in five files) and ghc-9.14.1 and 9.12.4, which give the same counts and the same linear loop, labels aside; their `-fregs-graph` loop has `addq %rbx,%r10` where HEAD has `addq %rbx,%r14`. The issue's description and all its notes were read on 2026-10-18; the last note before this one was that comment. Its two loops move values that the loop reads: one value live across a C call, and, in a nested loop, the source and output bases. Mikolaj's note of 2026-08-29 says that the allocator keeps values in registers that the inner loop never reads; this loop shows that it also stores and reloads such values on every iteration, in one loop with no call. Found in orthotope's benchmark (item O08 of `docs/inlining-catalogue.md`): with `compareT` INLINE, each summed loop of the strided Storable cell makes 2 more C-stack loads and 1 more store an element than the forced one, and INLINABLE runs 2 to 5 fewer instructions an element in the large summed cells, at most views. Code checked at master f93d523c (2026-10-15); JoinToTargets.hs there is the same as in the HEAD build. The prose is ASD-STE100 Simplified Technical English. Stated as open: why the allocator evicts `u1` and `u2` and not `u3` and `u4`.

One more loop, smaller than the two above: one loop, no C call, and two of the values that move on every iteration are values that the loop never reads. `f` takes the eight fields of a record before its loop. The loop reads `x1` to `x4`. `u1` to `u4` are used only after the loop. With `-DUFIRST`, the `u` fields come first in the record. The linear allocator then keeps `u3` and `u4` in `%rdi` and `%r8` through the loop. It stores `u1` (in `%rdx`) and `u2` (in `%rsi`) on every iteration and reloads them in the fixup block of the back edge, `.LnE`. It also reads the array and the length from the C stack at each element:

```
.LcDM:
	movq 64(%rsp),%rdx
	movq 16(%rdx,%rcx,8),%rdx
	movq %rsi,88(%rsp)
	movq %rdx,%rsi
	xorq %r11,%rsi
	addq %rbx,%rsi
	addq %rsi,%r14
	imulq %r9,%rdx
	addq %r10,%rdx
	addq %rdx,%rax
	incq %rcx
.LnE:
	movq 88(%rsp),%rsi
	movq 80(%rsp),%rdx
.LcDE:
	movq %rdx,80(%rsp)
	movq 72(%rsp),%rdx
	cmpq %rdx,%rcx
	jl .LcDM
```

The loop head keeps the assignment of its first entry, where `u1` and `u2` are in registers ([JoinToTargets.hs, lines 134-139][first]), and each later jump to it gets fixup code that restores that assignment (`joinToTargets_again`, [line 144][again]). So each iteration pays two loads and two stores for values that it does not use. With `-fregs-graph`, the same loop has no store and two loads, the array and the length:

```
.LcDM:
	movq 64(%rsp),%rbx
	movq 16(%rbx,%rsi,8),%rcx
	movq %rcx,%rbx
	xorq %rax,%rbx
	addq %rdx,%rbx
	addq %rbx,%r14
	imulq %r8,%rcx
	addq %rdi,%rcx
	addq %rcx,%r9
	incq %rsi
.LcDE:
	movq 72(%rsp),%rbx
	cmpq %rbx,%rsi
	jl .LcDM
```

Instructions an element:

```
                 linear   -fregs-graph
-DUFIRST         17.00    13.00
no flag          18.00    13.00
```

Without `-DUFIRST`, the `x` fields come first. Then `u1` to `u4` stay in registers through the loop, and the loop moves its own `x1` and `x2` through the C stack. That is the form of the note of 2026-08-29. The field order picks which form occurs.

I found this in a benchmark of orthotope, where an INLINE comparison puts two comparisons in one function and the inputs of the second stay live through the loops of the first. There, the fixup block of the back edge reloads three values that the loop does not use, and the loop stores them again, on every iteration.

The loops of #27980 and #27981 also have fixup code on the back edge, but at a return continuation in the loop. This loop has no return continuation.

<details><summary>Reproducer 3</summary>

`Lib.hs`:

```haskell
{-# LANGUAGE CPP, MagicHash, UnboxedTuples, BangPatterns #-}
module Lib (R (..), f) where

-- A loop over an Int array that reads x1 to x4 of a record, while u1 to u4,
-- read from the same record before the loop, are used only after it.
-- UFIRST puts the u fields first in the record.

import GHC.Exts

data R = R !Int !Int !Int !Int !Int !Int !Int !Int

{-# OPAQUE f #-}
f :: ByteArray# -> Int -> R -> Int
#if defined(UFIRST)
f arr (I# n) (R (I# u1) (I# u2) (I# u3) (I# u4) (I# x1) (I# x2) (I# x3) (I# x4)) =
#else
f arr (I# n) (R (I# x1) (I# x2) (I# x3) (I# x4) (I# u1) (I# u2) (I# u3) (I# u4)) =
#endif
  let loop i acc1 acc2 = case i >=# n of
        1# -> (# acc1, acc2 #)
        _ -> let e = indexIntArray# arr i
             in loop (i +# 1#) (acc1 +# e *# x1 +# x2) (acc2 +# xorI# e x3 +# x4)
  in case loop 0# 0# 0# of
       (# a, b #) -> I# (a +# b +# u1 *# u2 +# u3 *# u4)
```

`Main.hs`:

```haskell
{-# LANGUAGE MagicHash, UnboxedTuples, BangPatterns #-}
module Main (main) where

import GHC.Exts
import GHC.IO (IO (..))
import System.Environment (getArgs)
import Lib

data BA = BA ByteArray#

-- An array of k Ints, 0 to k - 1.
mkArray :: Int -> IO BA
mkArray (I# k) = IO $ \ s0 ->
  case newByteArray# (k *# 8#) s0 of
    (# s1, m #) ->
      let fill i s | isTrue# (i >=# k) = s
                   | otherwise = fill (i +# 1#) (writeIntArray# m i i s)
      in case unsafeFreezeByteArray# m (fill 0# s1) of
           (# s2, a #) -> (# s2, BA a #)

main :: IO ()
main = do
  [ks, rs] <- getArgs
  let k = read ks :: Int
      reps = read rs :: Int
  BA arr <- mkArray k
  let go :: Int -> Int -> Int
      go 0 !acc = acc
      go r !acc = go (r - 1) (acc + f arr k (R r 2 3 4 5 6 7 8))
  print (go reps 0)
```

`ghc -O -DUFIRST -outputdir u -o Main-u -ddump-asm -ddump-to-file Main.hs`, and the same without `-DUFIRST` (`x`), and both again with `-fregs-graph`. `perf stat -e instructions:u ./Main-u 100000 100`, and the same with `200`; the difference divided by 10^7 is the count for one element. The loop is the `jl` loop of `Lib.f_info` in `u/Lib.dump-asm`.

</details>

[first]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/CmmToAsm/Reg/Linear/JoinToTargets.hs#L134-139
[again]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/CmmToAsm/Reg/Linear/JoinToTargets.hs#L144
