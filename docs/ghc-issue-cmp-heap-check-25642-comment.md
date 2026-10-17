# GHC issue comment: the example of #1498 has its heap check in the loop again

Posted 2026-10-17 as a comment on GHC [#25642](https://gitlab.haskell.org/ghc/ghc/-/work_items/25642), "Revisit definition of `isTrue#`, and heap check placement" (open), which simonpj made the master ticket of the heap-check placement issues, GHC [#1498](https://gitlab.haskell.org/ghc/ghc/-/work_items/1498) among them; this file stays as the record of the comment, the text from "The example of #1498" down being the body as posted. Verified with GHC HEAD 10.1.20260918 and 9.14.1, which give the same eight instructions in the loop, in another order on 9.14.1. Read on 2026-10-17: the description and all notes of #25642 and #1498. The cause is already stated on GHC [#16064](https://gitlab.haskell.org/ghc/ghc/-/work_items/16064) (2020 and 2021) and GHC [#22936](https://gitlab.haskell.org/ghc/ghc/-/work_items/22936); what is new is only the current state of #1498's own example, so the comment cites them for the cause and adds only that. The instruction counts are read from the listing, and a measured run agrees: 8.00 and 6.00 instructions an element. That 6d14c1485c moved this example's check is not bisected; the comment states only its date. The prose is ASD-STE100 Simplified Technical English.

The example of #1498, which the comment of 2012-02-21 there found with its heap check in the right place, has the heap check in the loop again on HEAD (10.1.20260918, a build of `wip/T27737` on master e2d5702699 with local simplifier patches) and 9.14.1. In current syntax:

```haskell
{-# LANGUAGE MagicHash, UnboxedTuples #-}
module Repro (foo) where

import GHC.Exts

-- OPAQUE keeps foo whole: split by worker/wrapper, its worker returns
-- Double# and the loop does not allocate.
{-# OPAQUE foo #-}
foo :: ByteArray# -> Int# -> (# (), Double #)
foo as n = loop 0# 0.0##
  where
    loop i x = case i >=# n of
      1# -> (# (), D# x #)
      _  -> loop (i +# 1#) (x *## indexDoubleArray# as i)
```

With `ghc -O -c -ddump-asm Repro.hs`, the loop on HEAD is (9.14.1 has the same eight instructions in another order):

```
.Lcyt:
	mulsd 16(%r14,%rax,8),%xmm0
	addq $-16,%r12
	incq %rax
.Lcyg:
	addq $16,%r12
	cmpq 856(%r13),%r12
	ja .Lcyl
.Lcyk:
	cmpq %rsi,%rax
	jl .Lcyt
```

Four of its eight instructions are the heap check, which only the exit needs. As found on #16064 and #22936, the cause is the special case for comparison primops in `cgCase`, `do_gc  | is_cmp_op scrut  = False` ([StgToCmm/Expr.hs, line 608][cmp]; Note [GC for conditionals]), which came with 6d14c1485c in 2017. With the exit written as `case n -# i of 0# -> (# (), D# x #)`, the check is after the exit, and the loop has six instructions.

[cmp]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/StgToCmm/Expr.hs#L608
