# GHC issue: a self-recursive loop stores its stack arguments on every iteration, even unchanged ones

Filed as GHC [#27991](https://gitlab.haskell.org/ghc/ghc/-/work_items/27991); the text from "## Summary" down is the body as drafted, in the tracker's bug template. Title: **Cmm stack layout: a self-recursive loop stores its stack arguments on every iteration, even unchanged ones**. Verified on 2026-10-19 with GHC HEAD 10.1.20260918, 9.14.1, 9.12.4, 9.10.3 and 9.8.4, which give the same stores, from the file as shown here. With `-fllvm` and LLVM 18, 9.14.1 deletes this loop entirely. A larger probe, three loops that compare two arrays of Doubles, keeps its stores with `-fllvm`, and with the native code generator of 9.14.1 its loops cost 15, 13 and 12 instructions an element with 3, 1 and 0 stores. Found in a probe written for a variant of orthotope that moved its comparison loops out of line as top-level self-recursive functions, its Storable worker taking eight arguments; that variant's own machine code was not read. A tracker search of 2026-10-19 found no report. The nearest items are GHC [#14068](https://gitlab.haskell.org/ghc/ghc/-/work_items/14068), loopification in Core, which would make such a loop a local join point; GHC [#8903](https://gitlab.haskell.org/ghc/ghc/-/work_items/8903), dead store elimination in general; and GHC [#25349](https://gitlab.haskell.org/ghc/ghc/-/work_items/25349), stores around the evaluation of a value in a loop. horde-ad's GHC [#27742](https://gitlab.haskell.org/ghc/ghc/-/work_items/27742), loop invariants that the linear allocator spills, and GHC [#27737](https://gitlab.haskell.org/ghc/ghc/-/work_items/27737), loop invariants read from a closure on every iteration, are about other loads and stores. The cited lines were checked at master 3d326d7d28, where the cited files are the same as in the HEAD build. Open: the possible fixes are not tested; targets other than x86-64 were not checked.

## Summary

GHC compiles a self-recursive tail call as a jump to a loop header in the same procedure (Note [Self-recursive tail calls] in GHC.StgToCmm.Expr). In the example below, the first five arguments are passed in registers and the other two on the stack. The entry block loads the stack arguments into local registers, and the loop uses only those registers. But the stack layout pass puts a block on the back edge that stores each stack argument to its slot, so every iteration pays one store per stack argument, even for the arguments that do not change. The loop does not read these slots.

The cause, in the code at master:

1. When a local register is loaded from a stack slot, `procMiddle` adds an entry to the stack map recording that the slot holds the register's value ([LayoutStack.hs, lines 394-414][procmiddle]). Any other assignment to the register deletes the entry, even a self-assignment such as `x = x`. The comment gives the purpose:

   ```
   -- Look for loads from stack slots, and update the StackMap.  This is
   -- purely for optimisation reasons, so that we can avoid saving a
   -- variable back to a different stack slot if it is already on the
   -- stack.
   ```

2. The pass visits the blocks in reverse postorder ([lines 72-75][order]), so the loop header gets its stack map from the entry path ([lines 569-577][first]). On that path, each stack argument has its entry.
3. The tail call assigns the argument registers with `emitMultiAssign` ([StgToCmm/Expr.hs, lines 1093-1098][jump]): a changed argument gets its new value, an unchanged one a self-assignment such as `_szd::I64 = _szd::I64`. So on the back edge no stack argument has an entry, and `fixupStack` stores each one to its slot to match the header's stack map ([LayoutStack.hs, lines 552-556][branch] and [lines 607-617][fixup]).

An entry is useful only at a call that must save its variable on the stack, and this loop has no call. So here the entries save nothing, and the stores are pure cost.

Possible fixes, not tested:

1. `procMiddle` keeps the entry of `x` on a self-assignment `x = x`, or `emitMultiAssign` does not emit such assignments. This removes the stores of unchanged arguments, here `n`, and leaves the store of `i`.
2. A loop header gets a stack map without entries for the registers that the loop assigns, self-assignments included. Then the back edge needs no stores at all, and if the loop has a call, the pass saves such a register before it, as it saves any other variable.

Related: #14068 proposes loopification in Core. That would turn such a function into a wrapper around a local join point, which has no stack arguments, and so avoid these stores, though the stack layout pass would stay as it is.

## Steps to reproduce

`Repro.hs`:

```haskell
{-# LANGUAGE MagicHash #-}
module Repro (f) where

import GHC.Exts

f :: Int# -> Int# -> Int# -> Int# -> Int# -> Int# -> Int# -> Int#
f a b c d e n i = case i >=# n of
  1# -> a +# b +# c +# d +# e
  _ -> f a b c d e n (i +# 1#)
```

`ghc -O -ddump-cmm-from-stg -ddump-cmm-sp -ddump-asm -ddump-to-file -c Repro.hs`

### Results

`a`, `b`, `c`, `d` and `e` are passed in registers, and `n` and `i` on the stack. Only `i` changes in the loop. The listings are from 9.14.1.

In `Repro.dump-cmm-from-stg`, the back edge only assigns registers (`_szd` is `n`, `_sze` is `i`):

```
       czu: // global
           _czL::I64 = _sze::I64 + 1;
           _szg::I64 = _czL::I64;
           _sze::I64 = _szg::I64;
           _szd::I64 = _szd::I64;
           _szc::I64 = _szc::I64;
           _szb::I64 = _szb::I64;
           _sza::I64 = _sza::I64;
           _sz9::I64 = _sz9::I64;
           _sz8::I64 = _sz8::I64;
           goto czo;
```

In `Repro.dump-cmm-sp`, the stack layout pass has put the block `n0`, which stores `n` and `i`, on this edge:

```
      goto n0;
  n0: // global
      I64[Sp] = _szd::I64;
      I64[Sp + 8] = _sze::I64;
      goto czo;
```

In `Repro.dump-asm`, the loop is `.Lczu` and `.Lczo`, and two of its five instructions store `n` (`%rax`) and `i` (`%rbx`):

```
Repro.f_info:
.Lczw:
	movq (%rbp),%rax
	movq 8(%rbp),%rbx
	jmp .Lczo
.Lczu:
	movq %rax,(%rbp)
	incq %rbx
	movq %rbx,8(%rbp)
.Lczo:
	cmpq %rax,%rbx
	jl .Lczu
```

## Expected behavior

The back edge stores nothing: the loop keeps `n` and `i` in registers.

## Environment

* GHC version used: HEAD 10.1.20260918 (`wip/T27737` at 6913545fd3, on master e2d5702699, with local simplifier patches; Cmm/LayoutStack.hs and StgToCmm/Expr.hs are the same as at master 3d326d7d28), 9.14.1, 9.12.4, 9.10.3 and 9.8.4, all with the same stores.

Optional:

* Operating System: Linux
* System Architecture: x86_64

[procmiddle]: https://gitlab.haskell.org/ghc/ghc/-/blob/3d326d7d28ee5d51c9ae42ae1baf1c5a4500d185/compiler/GHC/Cmm/LayoutStack.hs#L394-414
[order]: https://gitlab.haskell.org/ghc/ghc/-/blob/3d326d7d28ee5d51c9ae42ae1baf1c5a4500d185/compiler/GHC/Cmm/LayoutStack.hs#L72-75
[first]: https://gitlab.haskell.org/ghc/ghc/-/blob/3d326d7d28ee5d51c9ae42ae1baf1c5a4500d185/compiler/GHC/Cmm/LayoutStack.hs#L569-577
[jump]: https://gitlab.haskell.org/ghc/ghc/-/blob/3d326d7d28ee5d51c9ae42ae1baf1c5a4500d185/compiler/GHC/StgToCmm/Expr.hs#L1093-1098
[branch]: https://gitlab.haskell.org/ghc/ghc/-/blob/3d326d7d28ee5d51c9ae42ae1baf1c5a4500d185/compiler/GHC/Cmm/LayoutStack.hs#L552-556
[fixup]: https://gitlab.haskell.org/ghc/ghc/-/blob/3d326d7d28ee5d51c9ae42ae1baf1c5a4500d185/compiler/GHC/Cmm/LayoutStack.hs#L607-617

/label ~"T::bug"
/label ~"code generation"
/label ~"runtime perf"
/label ~"needs triage"
