# GHC issue comment: two small modules in which `-g1` changes the optimised Core, and the code that causes each

Posted 2026-10-17 as a comment on GHC [#21471](https://gitlab.haskell.org/ghc/ghc/-/work_items/21471) ("Source notes impact compilation results as evident by -dannot-lint failures when running GHC testsuite"); this file stays as the record of the comment, the text from "The test log linked" down being the body as posted. Verified with GHC HEAD 10.1.20260918 and ghc-9.14.1, 9.12.4 and 9.10.3: the Exitification half on all four, the CSE half on HEAD only. The issue's description and all its notes were read on 2026-10-17. The test log linked from the description already names both passes (Exitification for T5658b, CSE for several tests), so the comment says so and does not present the pass names as new. The link to GHC [#27687](https://gitlab.haskell.org/ghc/ghc/-/work_items/27687), horde-ad's own issue, follows its records `docs/ghc-issue-debug-changes-codegen.md` and `docs/ghc-issue-debug-changes-codegen-comment.md` and its notes on the tracker. The documentation sentence is also item 2 of GHC [#27973](https://gitlab.haskell.org/ghc/ghc/-/work_items/27973), filed from `docs/ghc-issue-doc-slips.md`, which the comment names. The prose is ASD-STE100 Simplified Technical English. Measured after drafting: in this module `-g1` costs nothing at run time, 4.00 instructions an iteration of the loop with and without it (HEAD, a `Main` running the loop 10^8 and 2 * 10^8 times); the issue's "negligible" (mpickering, 2023-09-07) is about a GHC built with source notes compiling Cabal. Stated as open: which change makes the CSE half appear on HEAD and not on 9.14.1, and whether either mechanism accounts for the large program of #27687.

The test log linked from the description has `-dannot-lint` warnings in Exitification (T5658b) and in CSE (determ017 and others). Here are both in one small module, with the code that causes each. This is on HEAD (10.1.20260918):

```haskell
module Repro (loop, f, g) where

loop :: Int -> Int -> Int -> Int
loop t n0 x0 = go n0 x0
  where
    go :: Int -> Int -> Int
    go 0 x = t * (x * x) + t * x + x
    go n x = go (n - 1) (x + t)

f :: Int -> Int
f n = errorWithoutStackTrace ("bad index: " ++ show n)

g :: Int -> String
g n = "bad index: " ++ show n
```

With `ghc -O -c -ddump-simpl -dsuppress-all -dsuppress-uniques Repro.hs`, the loop jumps to an exit join point, `0# -> jump exit ww3`, and the module has one string literal, which `f` uses: `errorWithoutStackTrace (unpackAppendCString# g1 (itos ww []))`. With `-g1` added, the loop has no exit join point, and the module has a second literal, `lvl = "bad index: "#`, which `f` uses: `errorWithoutStackTrace (unpackAppendCString# lvl (itos ww []))`. `-fobject-determinism` does not change this. With `-g1 -dannot-lint`, GHC prints:

```
*** Core Lint warning : in result of Exitification transformation ***
Core changes with annotations:
```

```
*** Core Lint warning : in result of Common sub-expression ***
Core changes with annotations:
  lvl /= lvl
    (in binding $wf)
```

The causes in the code:

1. Exitification looks for exit points only through `case` alternatives, `let` bodies and join-point right-hand sides ([Exitify.hs, lines 158-195][exitify-go]). Any other expression, a source note included, goes to `go _ ann_e = return (deAnnotate ann_e)`. With `-g1`, a source note encloses the body of the loop (with `-dno-suppress-ticks`: `$wgo ww2 ww3 = src<Repro.hs:(7,5)-(8,31)> case ww2 of ...`), so the traversal stops there.
2. CSE looks up an expression with its floatable ticks removed and gives back the hit inside those ticks ([CSE.hs, lines 684-694][try-for-cse]). For the second literal, the result is then a variable under a source note, not a variable. So `extendCSEnvWithBinding` does not add the substitution ([CSE.hs, lines 487-510][ext-env]) that Note [Take care with literal strings] depends on ([CSE.hs, lines 554-558][note-lit]), and `f` keeps the second copy.

The Exitification half is the same on 9.14.1, 9.12.4 and 9.10.3. On 9.14.1 and 9.12.4, `-g1` does not give a second literal; I did not find the change that makes the CSE half appear on HEAD.

The users' guide says the opposite of both ([debug-info.rst, lines 72-73][rst-g]): "Note that this debugging information does not affect the optimizations performed by GHC." #27973 item 2 asks to change it.

#27687 reports that `-g1` changes the machine code. Its small reproducer was traced to the uniques of block labels, and `-fobject-determinism` makes the two builds equal there. In a large program in that issue, `-g3` still changes the code with `-fobject-determinism`. The two Core changes above survive `-fobject-determinism`, so they are candidates for that part. I did not check whether they occur in that program.

[exitify-go]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Exitify.hs#L158-195
[try-for-cse]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/CSE.hs#L684-694
[ext-env]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/CSE.hs#L487-510
[note-lit]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/CSE.hs#L554-558
[rst-g]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/docs/users_guide/debug-info.rst#L72-73
