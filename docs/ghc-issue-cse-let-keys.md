# GHC issue: CSE misses identical bindings that hold a non-recursive let, because `CoreMap` stores and looks up such a let under swapped keys

Filed as GHC [#27892](https://gitlab.haskell.org/ghc/ghc/-/work_items/27892) on 2026-10-03; the text from "## Summary" down is the filed body, in the tracker's bug template. Title: **Core bloat from broken CSE: `CoreMap` looks up a non-recursive `let` under swapped keys**. Verified on ghc-9.10.3, 9.12.4, 9.14.1 and HEAD at 10.1.20260918. It bears on the compile time of orthotope's test suite, one of whose modules keeps 80 identical copies per element type of a floated constant.

## Summary

In `GHC.Core.Map.Expr`, `xtE` stores `Let (NonRec b r) e` keyed first on the body `e`, then on the right-hand side `r` ([`xtE`][xtE]), while `lkE` looks it up keyed first on `r`, then on `e` ([`lkE`][lkE]). While a trie level holds one entry, `GenMap` compares whole keys and the lookup succeeds; once it holds two, an identical expression is looked up under a path it was never stored under. So CSE stops merging identical bindings that hold a non-recursive `let` or join point as soon as a module has two different ones.

In one test module of the orthotope library at `-O`, this leaves 80 identical top-level copies per element type of a floated `Data.Vector.Unboxed.concat []`, each holding a non-recursive join point.

## Steps to reproduce

`ghc -O -c -ddump-cse -dsuppress-all -dsuppress-uniques Repro.hs` on:

```haskell
module Repro where

f, g, h :: Int -> Int -> Int
f x y = case (if x > y then x * 3 else y * 5) of m -> m * m + x * y
h x y = case (if x > y then x * 7 else y * 9) of m -> m * m + x * y
g x y = case (if x > y then x * 3 else y * 5) of m -> m * m + x * y

f2, g2 :: Int -> Int -> Int
f2 x y = x * y + 1
g2 x y = x * y + 1
```

CSE gives `f2 = g2` but keeps `f` and `g`, whose bodies are identical, each holding `I# (let { x = *# y 5# } in ...)`. Without `h`, it gives `f = g`.

## Expected behavior

`f = g`, as with `f2` and `g2`. Storing in `lkE`'s order should do it (untested):

```diff
 xtE (D env (Let (NonRec b r) e)) f m = m { cm_letn = cm_letn m
-                                                 |> xtG (D (extendCME env b) e)
-                                                 |>> xtG (D env r)
+                                                 |> xtG (D env r)
+                                                 |>> xtG (D (extendCME env b) e)
                                                  |>> xtBndr env b f }
```

Both orders are in commit 90dee6e134 (2015).

## Environment

GHC 9.10.3, 9.12.4, 9.14.1 and HEAD at 10.1.20260918, x86_64 Linux.

[xtE]: https://gitlab.haskell.org/ghc/ghc/-/blob/5236634abce50db7e8e7ecf375def90bf45d2476/compiler/GHC/Core/Map/Expr.hs#L376-L379
[lkE]: https://gitlab.haskell.org/ghc/ghc/-/blob/5236634abce50db7e8e7ecf375def90bf45d2476/compiler/GHC/Core/Map/Expr.hs#L346-L347
