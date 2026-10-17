# GHC issue comment: a Haskell reproducer for #20334, where a strict field and worker/wrapper's call-by-value evaluation load fields early

Posted 2026-10-17 as a comment on GHC [#20334](https://gitlab.haskell.org/ghc/ghc/-/work_items/20334), "Bad interaction between CmmSink limitations and unlifted data types." (open, with no activity between 2021-11-15 and the comment); this file stays as the record of the comment, the text from "A Haskell reproducer" down being the body as posted. Low priority: the cost is 5 instructions a call. Verified with GHC HEAD 10.1.20260918, 9.14.1 and 9.12.4, from the files as shown here. GHC [!6981](https://gitlab.haskell.org/ghc/ghc/-/merge_requests/6981) was merged (marge-bot, 2021-11-23; its commit 680ef2c8ea is in the HEAD build), though GitLab shows it closed. Read on 2026-10-17: the issue's description and all its notes. The issue has AndreasK's Cmm reproducer, which !6981 fixed, and his note that a compact one seemed hard to make; no Haskell reproducer and no Haskell-level trigger is on it, nor on GHC [#20333](https://gitlab.haskell.org/ghc/ghc/-/work_items/20333), GHC [#19445](https://gitlab.haskell.org/ghc/ghc/-/work_items/19445), GHC [#8905](https://gitlab.haskell.org/ghc/ghc/-/work_items/8905) or !6981, though they have programs of the same shape. horde-ad has no record of #20334. The prose is ASD-STE100 Simplified Technical English. Open: whether the cost is the same on master's code; the cited code is the same at master except a local patch of the HEAD build that exempts dictionaries from `mkStrictFieldSeqs`.

A Haskell reproducer, base only, with a common trigger: a strict field, the call-by-value evaluation that worker/wrapper adds for an argument from a strict field, and `refineDefaultAlt`. On HEAD (10.1.20260918, a build of `wip/T27737` on master e2d5702699 with local simplifier patches), 9.14.1 and 9.12.4 it still loads the fields at the worker's entry and saves them across a later evaluation.

1. The second field of `W` is strict. Worker/wrapper keeps `v` boxed in `$wg`, because `useBoxed` needs the box. Because `v` comes from a strict field, worker/wrapper also adds `case v of v' { __DEFAULT -> ... }` at the top of the worker ([`mkStrictFieldSeqs`][seqs], Note [Call-by-value for worker args]).
2. The simplifier refines this DEFAULT to the one constructor of `V` ([`refineDefaultAlt`][refine]), and the `case v of V a b c` in the branch then uses its binders. So the fields are bound at the worker's entry.
3. The code generator drops the evaluation itself, as the Note says ("The code generator will discard that "extra eval" case", [Core/Utils.hs, lines 3250-3251][discard]), but it loads the three fields at the entry. They are live across the evaluation of `x`, so they are saved to the stack, together with `v`, which the `x == 0` branch uses.

With the field lazy (`-DLAZY`), `$wg` takes `v` apart only in its branch.

`Lib.hs`:

```haskell
{-# LANGUAGE CPP #-}
module Lib (V (..), W (..), g) where

data V = V !Int !Int !Int
#ifdef LAZY
data W = W [Int] V
#else
data W = W [Int] !V
#endif

-- Opaque, so that g's use of v keeps v boxed.
{-# OPAQUE useBoxed #-}
useBoxed :: V -> Int
useBoxed (V a _ _) = a

{-# NOINLINE useFields #-}
useFields :: Int -> Int -> Int -> Int
useFields a b c = a + b + c

-- At x == 0 g uses v whole, its fields not at all.  NOINLINE keeps g out of
-- Main in both variants, so that each measures the same call.
{-# NOINLINE g #-}
g :: W -> Int
g (W osh v) = case osh of
  [] -> 0
  x : _ -> if x == 0 then useBoxed v else case v of V a b c -> useFields a b c
```

`Main.hs`:

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import Lib
import System.Environment (getArgs)

-- Opaque, so that each iteration calls g anew.
{-# OPAQUE pass #-}
pass :: Int -> a -> a
pass _ x = x

main :: IO ()
main = do
  [ns] <- getArgs
  let n = read ns :: Int
      w = W [0, 1] (V 1 2 3)
      loop :: Int -> Int -> Int
      loop 0 !acc = acc
      loop r !acc = loop (r - 1) (acc + g (pass r w))
  print (loop n 0)
```

With `ghc -O -c Lib.hs -ddump-stg-final -dsuppress-all -dsuppress-uniques`, on HEAD, `$wg` binds the fields first (9.14.1 and 9.12.4 print `<TagProper>` in place of `<TagVal[TagEPT]>`, and 9.12.4 other binder names):

```
$wg =
    \r [ww ww1]
        case ww1<TagVal[TagEPT]> of ww2 {
        V ipv ipv1 ipv2 ->
        case ww<TagVal[TagEPT]> of wild {
          [] -> lvl<TagVal[TagEPT]>;
          : x _ ->
              case x of wild1 {
              I# x1 ->
              case x1<TagVal[TagEPT]> of wild2 {
                __DEFAULT ->
                    case $wuseFields ipv ipv1 ipv2 of ww3 { __DEFAULT -> I# [ww3]; };
                0# -> useBoxed ww2;
```

With `-DLAZY`:

```
$wg =
    \r [ww ww1]
        case ww<TagVal[TagEPT]> of wild {
          [] -> lvl<TagVal[TagEPT]>;
          : x _ ->
              case x of wild1 {
              I# x1 ->
              case x1<TagVal[TagEPT]> of wild2 {
                __DEFAULT ->
                    case ww1 of wild3 {
                    V bx bx1 bx2 ->
                    case $wuseFields bx bx1 bx2 of ww2 { __DEFAULT -> I# [ww2]; };
                    };
                0# -> useBoxed ww1;
```

In the assembly (`-ddump-asm`), the strict version saves `v` and its three fields before it evaluates `x`:

```
	movq 6(%r14),%rbx
	movq %rsi,-32(%rbp)
	movq 7(%rsi),%rax
	movq %rax,-24(%rbp)
	movq 15(%rsi),%rax
	movq %rax,-16(%rbp)
	movq 23(%rsi),%rax
	movq %rax,-8(%rbp)
	addq $-40,%rbp
	testb $7,%bl
```

The lazy version saves only `v`:

```
	movq 6(%r14),%rbx
	movq %rsi,-8(%rbp)
	addq $-16,%rbp
	testb $7,%bl
```

With `ghc -O Lib.hs Main.hs -o Main` (and the same with `-DLAZY`), `perf stat -e instructions:u ./Main N` at N = 10^7 and 2 * 10^7, differenced, gives the instructions for one iteration of the loop, which calls `g` once with `x == 0`:

```
          strict    lazy
HEAD      82.364    77.364
9.14.1    81.288    76.288
9.12.4    81.288    76.288
```

[seqs]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Utils.hs#L3341-3355
[refine]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Utils.hs#L1099-1106
[discard]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Utils.hs#L3250-3251
