# GHC issue comment: Cmm sinking still leaves a dead assignment in a loop, to an unused `SPEC` argument

Posted 2026-10-07 as [a comment](https://gitlab.haskell.org/ghc/ghc/-/work_items/8327#note_702570) on GHC [#8327](https://gitlab.haskell.org/ghc/ghc/-/work_items/8327); this file stays as the record of the comment, the text from "The original example" down being the body as posted, except that the program's module is `T` there and `Main` here, which `tools/check-doc-examples.py` skips as a self-contained program and GHC refuses for want of `main`. The comment before it, of 2026-03-07, found the issue's example clean on 9.14.1 and offered a regression test. The dead assignment was found in vector's loops at `-O1`, in orthotope's benchmark of its array operations.

The original example no longer shows it, but the deficiency is still there on HEAD (10.1.20260918), 9.14.1 and 9.12.4. At `-O1`, which runs no SpecConstr to remove the argument:

```haskell
{-# LANGUAGE BangPatterns, MagicHash #-}
module Main (sumTo) where

import GHC.Exts

sumTo :: Int -> Int
sumTo (I# n) = I# (go SPEC 0# 0#)
  where go !_ acc i | isTrue# (i >=# n) = acc
                    | otherwise = go SPEC (acc +# i) (i +# 1#)
```

With `ghc -O1 -ddump-cmm -ddump-asm -dsuppress-all T.hs`, the loop assigns `_ty4`, the `SPEC` argument, on every iteration, and nothing reads `_ty4`:

```
       cyL:
           _ty9::I64 = _ty5::I64 + _ty6::I64;
           _ty6::I64 = _ty6::I64 + 1;
           _ty5::I64 = _ty9::I64;
           _ty4::P64 = SPEC_closure+1;
           goto cyA;
```

On HEAD the loop then runs five instructions where four would do; 9.12.4 and 9.14.1 carry the same `leaq` in a longer loop:

```
.LcyL:
        addq %rbx,%rcx
        incq %rbx
        leaq SPEC_closure+1(%rip),%rdx
.LcyA:
        cmpq %rax,%rbx
        jl .LcyL
```

The one read of `_ty4` is the copy `_ty7::P64 = _ty4::P64;` for the binder of the bang's `case ds1<TagVal[TagEPT]> of ds2`, which nothing uses. The copy is there after stack layout (`-ddump-cmm-sp`) and gone after sinking (`-ddump-cmm-sink`), which keeps both assignments to `_ty4`.

`vector` hits this: at `-O1` on HEAD, `Data.Vector.Unboxed.maximum` on `Double`, whose `foldlM'` loop takes a `SPEC` argument, loads `SPEC`'s address into a register on every iteration and overwrites it before any read. At `-O2` SpecConstr removes the argument, and the load with it. The program above could serve as the regression test.
