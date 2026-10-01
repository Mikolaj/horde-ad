# GHC issue: a join point taken for a freshly born one never gets an unfolding, so a worker's self tail call stays non-tail and the loop's stack grows with its iterations

Draft, not filed; the text from "## Summary" down is the body to file, in the tracker's bug template. Title: **A join point the occurrence analyser marks `ManyOccs` is taken for a freshly born one and never gets an unfolding, so a worker's self tail call is left as `case $wf … of r -> jump $j r K` and the loop needs stack proportional to its iterations**. Verified on 2026-10-01 on HEAD 10.1.20260929 (nightly bindist of commit `234bab0816`), the same commit with the fixes of GHC [#27873](https://gitlab.haskell.org/ghc/ghc/-/work_items/27873) and GHC [#27874](https://gitlab.haskell.org/ghc/ghc/-/work_items/27874), 9.14.1 and 9.12.4; 9.10.3 is not affected. Found in horde-ad: with `-flate-dmd-anal`, the loop of its reverse-mode backward pass became non-tail recursive, so the stack grew with the number of nodes of the delta expression, and every `unsafePerformIO` in the program then walked that stack in `threadPaused`, called from `noDuplicate#`. Its sequential test suite ran 12% slower, and one test executed 57% more instructions. The tracker was searched on 2026-10-01 for `freshly born join`, `join point unfolding`, `late-dmd-anal`, `tail call join point` and `freshly_born_join_point`, with no duplicate found; GHC [#25723](https://gitlab.haskell.org/ghc/ghc/-/work_items/25723) and GHC [#26569](https://gitlab.haskell.org/ghc/ghc/-/work_items/26569) are the nearest.

## Summary

In the reproducer below, `-O -flate-dmd-anal` turns the self tail call of the worker of `loop` into a non-tail call, and a loop of 10^6 iterations overflows a 1 MB stack. Without the flag it runs in constant stack. The final STG on HEAD is:

```
$w$wloop =
    \r [ww ww1]
        let-no-escape {
          $j = \j [us us] case us of wild1 { Tip -> us<TagVal[TagEPT]>; };
        } in
          case ww1<TagVal[TagEPT]> of ww2 {
            Tip -> $j ww Tip;
            Bin bx _ l r ->
                let-no-escape {
                  $j1 =
                      \j [y]
                          case r of wild {
                          __DEFAULT ->
                          case +# [ww y] of $w$wloop_sat {
                          __DEFAULT ->
                          case $w$wloop $w$wloop_sat wild of ww3 {
                          __DEFAULT -> $j ww3 Tip;
                          };
                          };
                          };
                } in
                ...
```

The late worker/wrapper splits the worker `$wloop` again: its result's second field is always `Tip`, so `$w$wloop` returns only the first field, and the post-late-ww simplifier pushes the continuation that rebuilds and checks it into a join point `$j`. Inlining `$j` at the jump `$j ww3 Tip` would leave `case $w$wloop … of ww3 { __DEFAULT -> ww3 }`, that is, the tail call. `$j` is not inlined, in any of the simplifier's iterations, and `-ddump-inlinings` records no decision about it, because it never has an unfolding:

* `$j` is made by [`mkDupableAlt`](https://gitlab.haskell.org/ghc/ghc/-/blob/234bab081682018da7d04b22eee4b80f70381d07/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4301-4351), which binds it without an unfolding, as Note [Do not add unfoldings to join points at birth] says it should.
* In the next iteration, [`simplLetUnfolding`](https://gitlab.haskell.org/ghc/ghc/-/blob/234bab081682018da7d04b22eee4b80f70381d07/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4826-4840) gives it none again, because `freshly_born_join_point id = is_join_point && isManyOccs (idOccInfo id)`. Wrinkle (JU1) of that Note assumes that "a freshly-born join point will have OccInfo of ManyOccs, unlike an existing join point which will have OneOcc", and that at worst this delays inlining by one iteration.
* Here the occurrence analyser does give the analysed `$j` `ManyOccs`. The late worker/wrapper also split the exit join point of the inlined `find` loop, and the stable unfolding of its wrapper jumps to the worker. Occurrences in a stable unfolding are made many ([`markAllMany`](https://gitlab.haskell.org/ghc/ghc/-/blob/234bab081682018da7d04b22eee4b80f70381d07/compiler/GHC/Core/Opt/OccurAnal.hs#L2400)), and [a jump to a join point brings in the usage of that join point's body](https://gitlab.haskell.org/ghc/ghc/-/blob/234bab081682018da7d04b22eee4b80f70381d07/compiler/GHC/Core/Opt/OccurAnal.hs#L3889), so `$j` is many through it.

So the same join point counts as freshly born in every iteration, the simplifier reaches its fixed point with it in place, and the loop keeps a frame per iteration. If `$j` had an unfolding, it would be inlined: its body scrutinises its first argument, which the jump passes as a constructor application, and the join-point rule of `tryUnfolding` accepts that.

The same shape arises without `-flate-dmd-anal` when the always-`Tip` field is visible to the first demand analysis (`Tip -> S n Tip` instead of `Tip -> s`). At `-O` and `-O2`, the late float-out pass floats the closed `$j` to the top level as an ordinary function and it is inlined, which hides the bug; with `-fno-full-laziness` the loop overflows the stack on HEAD, 9.14.1 and 9.12.4 at both `-O` and `-O2`, and on 9.10.3 at `-O` (but not `-O2`), so that variant has a second, older route.

A possible fix: tell a freshly born join point by what `newJoinId` gives it, no occurrence information at all, rather than by `ManyOccs`. An analysed join point always carries tail-call information, so `isNoOccInfo` separates the two:

```diff
-    freshly_born_join_point id = is_join_point && isManyOccs (idOccInfo id)
+    freshly_born_join_point id = is_join_point && isNoOccInfo (idOccInfo id)
```

It keeps the protection that (JU1) was added for, since a join point re-simplified in the iteration of its birth still has no occurrence information. Tested on top of commit `234bab0816`, it restores the tail call in the reproducer below and in its variant over `IntMap`, and the loop runs in a 1 MB stack again. In horde-ad, built with `-flate-dmd-anal`, the test that the bug slowed most executes 7.03 G instructions instead of 11.07 G, as many as without the flag. With it, on top of the fixes of #27873 and #27874, the full testsuite passes on x86_64 Linux (flavour `default+no_profiled_libs+no_dynamic_libs`): 11382 tests, 0 unexpected failures, 0 unexpected passes, 0 framework failures. In `testsuite/tests/perf/compiler`, every test passes with and without it, and all 101 `compile_time/bytes allocated` metrics change by less than 0.21%, T15630 and T15630a by -0.04%. On nofib at `-O2` (117 programs, under cachegrind), the geometric mean of instructions executed changes by -0.01% and that of bytes allocated by +0.002%, with no program beyond -0.6% and +0.2% in either; compiler allocation over its 435 modules changes by +0.04%. The tests and examples of earlier issues about join-point inlining and duplication (#15630, the one (JU1) cites, and #13253, #18304, #20049, #22317, #22423, #23767 and #25723 among them), and T15630 scaled up to 30 fields, compile to identical Core and object code with and without it.

It does not cover a second route, in which `$j` gets `OnceL2` inside a lambda and `simplLetUnfolding` takes it for an exit join point instead: [`isExitJoinId`](https://gitlab.haskell.org/ghc/ghc/-/blob/234bab081682018da7d04b22eee4b80f70381d07/compiler/GHC/Core/Opt/Simplify/Utils.hs#L3051-3056) recognises exit join points by that occurrence information, not by their having been made by exitification. The variant `MinExit` below takes this route, and the loop still overflows the stack with the fix above. Recording in the join point itself that exitification made it, for `simplLetUnfolding` to test instead of the occurrence information, would close both routes, but it is more than a one-line change.

A different change covers both routes for this shape, by not making `$j` at all. `mkDupableAlt` already skips the join point when `uncondInlineJoin` judges the alternative small enough to duplicate, points (DJ2) and (DJ3) of Note [Duplicating join points]. Letting that test also accept a single-alternative `case` on one of the join point's parameters whose alternative passes it in turn, with the case binder counted among the parameters, duplicates `case us of Tip -> us` instead:

```diff
--- a/compiler/GHC/Core/Unfold.hs
+++ b/compiler/GHC/Core/Unfold.hs
@@ -516,6 +516,14 @@ uncondInlineJoin bndrs body
   | indirectionOrAppWithoutFVs
   = True
 
+  -- (DJ3)(d): a single-alternative case on a binder, whose alternative
+  -- passes the same test with the pattern's binders in scope, e.g.
+  -- - $j a b = case b of Nil -> a              -- YES
+  -- - $j t = case t of (# a, b, c #) -> (# a, b #)  -- YES
+  | Case (Var v) case_bndr _ [Alt _ alt_bndrs rhs] <- body
+  , v `elem` bndrs
+  = uncondInlineJoin (case_bndr : alt_bndrs ++ bndrs) rhs
+
   | otherwise
   = False
 
--- a/compiler/GHC/Core/Opt/Simplify/Iteration.hs
+++ b/compiler/GHC/Core/Opt/Simplify/Iteration.hs
@@ -4299,7 +4299,7 @@ mkDupableAlt :: SimplEnv -> OutId
              -> JoinFloats -> OutAlt
              -> SimplM (JoinFloats, OutAlt)
 mkDupableAlt _env case_bndr jfloats (Alt con alt_bndrs alt_rhs_in)
-  | uncondInlineJoin alt_bndrs alt_rhs_in
+  | uncondInlineJoin (case_bndr : alt_bndrs) alt_rhs_in
     -- See point (DJ2) of Note [Duplicating join points]
   = return (jfloats, Alt con alt_bndrs alt_rhs_in)
```

Prototyped on the same commit, without the fix above, it restores the tail call in all the variants below, `MinExit` and the one without the flag at `-O` included, and the full testsuite passes. It is not free, though: it shifts worker/wrapper and inlining outcomes in unrelated code. On nofib, instructions and allocation stay level, but `real/hidden` grows by 0.6%, two of its modules by 18% and 34%, because a loop of `Vectors` that its importers used to call is now duplicated into each of them as a local specialisation. The causes of this regression were not investigated beyond that observation. So it complements the fix above rather than replacing it.

### Related

- #25723: the same symptom, a join point that re-boxes a result and blocks a self tail call; it was fixed by letting `uncondInlineJoin` inline join points whose body is a constructor application without free variables. Here the body is a `case`, so that does not apply, and the join point then never gets an unfolding to be inlined by.
- #26569: wrong occurrence information for join points with unfoldings, the source of the `ManyOccs` here.
- #27873 and #27874: found while measuring the same horde-ad flags.

## Steps to reproduce

```haskell
module Lib (S (..), T (..), loop) where

data T = Tip | Bin !Int Int T T

data S = S !Int !T

find :: Int -> T -> Int
find k = go
  where
    go Tip = 0
    go (Bin k' v l r)
      | k < k' = go l
      | otherwise = v

loop :: S -> S
loop s@(S n t) = case t of
  Bin k _ l r -> loop (S (n + find k l) r)
  Tip -> s
```

```haskell
import Lib

main :: IO ()
main = do
  let t = foldr (\k r -> Bin k k Tip r) Tip [1 .. 1000000]
      S n _ = loop (S 0 t)
  print n
```

Save the modules as `Lib.hs` and `Repro.hs`, then:

```
ghc -O -rtsopts Repro.hs -o Repro && ./Repro +RTS -K1m
ghc -O -flate-dmd-anal -rtsopts -fforce-recomp Repro.hs -o Repro && ./Repro +RTS -K1m
```

| compiler | `-O` | `-O -flate-dmd-anal` |
|---|---|---|
| HEAD 10.1.20260929 | prints `0` | stack overflow |
| 9.14.1 | prints `0` | stack overflow |
| 9.12.4 | prints `0` | stack overflow |
| 9.10.3 | prints `0` | prints `0` |

`ghc -O -flate-dmd-anal -c Lib.hs -ddump-stg-final -dsuppress-all -dsuppress-uniques` shows the STG above. The variant without the flag is `Lib.hs` with `Tip -> S n Tip` as the last line and `Bin !Int !Int T T` as the constructor, compiled with `-O -fno-full-laziness`. The variant `MinExit`, with the second field of `Bin` strict as well, gives `$j` `OnceL2` instead and shows the `isExitJoinId` route.

## Expected behavior

The worker's recursive call stays a tail call, and the loop runs in constant stack with and without `-flate-dmd-anal`, as it does on 9.10.3.

## Environment

* GHC version used: HEAD 10.1.20260929 (commit 234bab0816), 9.14.1, 9.12.4, 9.10.3

Optional:

* Operating System: Ubuntu 24.04
* System Architecture: x86_64

/label ~"T::bug"
/label ~"needs triage"
