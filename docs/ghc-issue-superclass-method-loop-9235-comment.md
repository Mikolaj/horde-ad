# GHC issue comment: the inliner also runs away when a default method recurses through a superclass dictionary

Posted 2026-10-17 as a comment on GHC [#9235](https://gitlab.haskell.org/ghc/ghc/-/work_items/9235) ("Simplifier ticks exhausted on recursive class method"), the declared duplicate of GHC [#5722](https://gitlab.haskell.org/ghc/ghc/-/work_items/5722), which simonpj left open "as evidence that someone else has tripped up over it". The comment goes on #9235 and not on #5722 because its shape is that of #9235 (a recursive default method, a class constraint in the method's own context, inlining without a pragma accepted by the description's condition 1), because it reports on the program of #9235, and because #9235 is the issue kept open to collect such cases. This file stays as the record of the comment, the text from "Another form" down being the body as posted. Verified with GHC HEAD 10.1.20260918 and ghc-9.14.1 and 9.12.4. Dropping the INLINE pragma keeps the loop, and so does dropping the default method; no variant tried drops both. Both issues' descriptions and all their notes were read on 2026-10-17; neither mentions a superclass, and nobody reports that the program of #9235 now compiles at `-O`. The prose is ASD-STE100 Simplified Technical English. Stated as open: why the one-module and the two-module forms fail at different optimisation levels.

Another form, in which the recursion goes through a superclass dictionary. The method's context names a subclass of the class, not the class itself, so the special case that simonpj considered on #5722, "a class that mentions itself in the context of a class method", would not cover it. There is no INLINE pragma.

```haskell
module Lib where

class L t where
  app :: B t => Int -> t -> t
  app 0 x = x
  app n x = b (app (n - 1) x)

class L t => B t where
  b :: t -> t

newtype T s = T Int

instance Eq s => L (T s)
instance Eq s => B (T s) where
  b (T n) = T (n + 1)
```

```haskell
module Repro (f) where

import Lib

f :: Int -> Int
f k = case app k (T 0 :: T ()) of T n -> n
```

Save them as `Lib.hs` and `Repro.hs`. On HEAD (10.1.20260918), 9.14.1 and 9.12.4, `ghc -O Lib.hs Repro.hs` stops in `Repro` with `Simplifier ticks exhausted`. HEAD and 9.12.4 say `When trying RuleFired Class op $p1B`, and 9.14.1 says `When trying UnfoldingDone $fLT_$capp`. `ghc -O0 Lib.hs Repro.hs` compiles on all three.

In one module (`Lib.hs` with `f` added at the end), HEAD fails at `-O0` (`When trying RuleFired Class op app`) and compiles at `-O`. 9.14.1 and 9.12.4 fail at `-O` (`When trying RuleFired Class op b`) and compile at `-O0`.

The program in the description of this issue now compiles at `-O` on HEAD, 9.14.1 and 9.12.4, and it fails only at `-O0`.
