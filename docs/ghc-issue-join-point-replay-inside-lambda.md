# GHC issue: a join point reached only through join points that a loop jumps to is marked as inside a lambda and never inlined

Filed as GHC [#27982](https://gitlab.haskell.org/ghc/ghc/-/work_items/27982) on 2026-10-17; the text from "## Summary" down is the filed body, in the tracker's bug template. Title: **Since 9.10, a join point jumped to only from other join points, which a loop jumps to, is marked as inside a lambda and is never inlined**. Verified with GHC HEAD 10.1.20260918 and ghc-9.14.1, 9.12.4 and 9.10.3 (show it) and ghc-9.8.4 (does not). Code and Note text checked at master f93d523c (2026-10-15); OccurAnal.hs, Simplify/Inline.hs and the cited guards are the same there as in the HEAD build, and 9.10.3 to 9.14.1, which carry none of the HEAD build's local patches, show the same result. GHC [#27885](https://gitlab.haskell.org/ghc/ghc/-/work_items/27885), horde-ad's own, says that `isExitJoinId` goes by occurrence information and proposes to record where a join point came from; its MinExit variant has a direct jump inside the loop, the route of GHC [#21148](https://gitlab.haskell.org/ghc/ghc/-/work_items/21148) (checked by compiling it). Tracker search 2026-10-17: every issue created since 2026-10-15 (16 issues, titles read), none related. The prose is ASD-STE100 Simplified Technical English. Stated as open: no GHC was built at d036980238 or with the replay changed, so the cause rests on the code and on the release boundary; the cost in orthotope was not measured for this draft.

## Summary

Since GHC 9.10, the occurrence analyser can mark a non-recursive join point as used once inside a lambda (`OnceL`) when none of its jumps is inside a lambda. This happens when the join point is jumped to only from other join points, which a recursive group jumps to. `isExitJoinId` then takes it for an exit join point, and the simplifier never inlines it. Each jump keeps its arguments, so a constructor in an argument is allocated at each jump.

In the example below, Exitification moves the two exits of the loop `go` into the join points `exit` and `exit1`. Each of them jumps to `j2` with a new `Q`. No jump to `j2` is inside the loop. On HEAD, 9.14.1, 9.12.4 and 9.10.3, `j2` gets `Occ=OnceL2`, it is not inlined, and each call of `f` allocates a `Q`, 24 bytes. On 9.8.4, `j2` is inlined into both exits, and `f` allocates nothing.

Note [Do not inline exit join points] ([Exitify.hs, lines 421-448][exit-note]) defines exit join points as "join points with an occurrence in a recursive group". It says that `isExitJoinId` can test `occ_in_lam` "because the lambdas of a non-recursive join point are not considered for `occ_in_lam`". The analyser no longer keeps that premise.

How the mark gets there, as read in OccurAnal.hs at master:

1. At the binding of `exit`, `addJoinPoint` records a zeroed copy of each tracked occurrence in the right-hand side of `exit` ([lines 3353-3367][add-jp]). The tracked Ids include join points, "so that the trick works recursively" ([lines 785-792][tracked]). So it records the occurrence of `j2`.
2. At each jump to `exit`, `mkOneOcc` adds that copy to the usage ([lines 3880-3889][mk-one-occ]).
3. The jumps to `exit` are in the right-hand side of the recursive `go`, whose lambdas get `NoOneShotInfo` ([lines 3224-3229][no-one-shot]). Thus `adjustTailUsage` marks all that usage as inside a lambda ([lines 4053-4060][adjust]), the copy of the occurrence of `j2` included.
4. The in-lambda sets of two usages are combined by union ([line 3997][union]). Thus the occurrence of `j2` in the right-hand side of `exit`, which is not inside a lambda, does not remove the mark.

Then `isExitJoinId` holds for `j2` ([Simplify/Utils.hs, lines 3050-3055][is-exit]). `preInlineUnconditionally` refuses it ([line 1658][pre-inline]), `simplLetUnfolding` gives it no unfolding ([Simplify/Iteration.hs, lines 4817-4833][let-unf]), and `callSiteInline` returns `Nothing` for `NoUnfolding` without a trace ([Simplify/Inline.hs, line 114][no-unf]).

This replay came with commit [d036980238][d036980238], "Make the occurrence analyser smarter about join points", for #22404. It is in 9.10.1 and later releases, and not in 9.8.4. The example changes at the same release boundary.

The same route in a larger program, a benchmark module of the orthotope library compiled with HEAD at `-O`, is wider than the example:

1. No Exitification is necessary. The join point that takes the boxed value is `OnceL3` from the first analysis in which it occurs, three analyses before Exitification runs.
2. The join points between it and the loops are workers `$w$j` of the continuation join points of `vector`'s `foldlM'`, each jumped to from inside its own `joinrec`.
3. One of its three jumps is under no lambda, and the mark stays.

In that module, eight join points of this shape take a Storable vector boxed, and each jump builds the box of the vector. I do not have a small reproducer of this wider form that keeps a box in the final Core.

#27885 proposes that a join point records that Exitification made it, and that `isExitJoinId` tests that record. That would also correct this case. In #21148 and in the MinExit variant of #27885, a jump is inside the loop, which the definition of the Note covers. Here, no jump to `j2` is.

Related: #15091 first proposed this kind of occurrence analysis. #22274 discusses this replay (!9614) for a recursive join point, where it does not help. !8901 (#22084) inhibited the inlining of exit join points only in the Simplifier run after Exitification, and commit 7eac2468a7 reverted it for regressions in the bytestring benchmarks (#22893), so a fix here wants the same benchmarks.

## Steps to reproduce

1. Save the two modules below as `ReproLib.hs` and `Repro.hs`, in an empty directory.
2. `ghc -O -rtsopts -ddump-simpl -dsuppress-all -dsuppress-uniques -ddump-to-file Repro.hs`
3. `./Repro 1000000 +RTS -s` and `./Repro 2000000 +RTS -s`, and `perf stat -e instructions:u -x,` on the same commands. The cost a call is the difference between the two runs, divided by 1000000.
4. `mkdir occ chk`
5. `ghc -O -fforce-recomp -c -outputdir occ -ddump-occur-anal -dsuppress-uniques -dsuppress-coercions -dsuppress-type-applications -dsuppress-module-prefixes -ddump-to-file ReproLib.hs`, then find in `occ/ReproLib.dump-occur-anal` the first analysis that binds `exit`.
6. `ghc -O -fforce-recomp -c -outputdir chk -dinline-check j2 ReproLib.hs`

```haskell
{-# LANGUAGE BangPatterns #-}
module ReproLib (f) where

data Q = Q !Int !Int

{-# NOINLINE f #-}
f :: Int -> Int -> Int
f n k =
  let j2 :: Q -> Int
      j2 q = if k > 0 then case q of Q a b -> a * b else k
      go :: Int -> Int -> Int
      go !i !acc
        | i >= n = j2 (Q acc i)
        | acc > k = j2 (Q i acc)
        | otherwise = go (i + 1) (acc + i)
  in go 0 0
```

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import ReproLib (f)
import System.Environment (getArgs)

main :: IO ()
main = do
  [s] <- getArgs
  let iters = read s :: Int
      loop :: Int -> Int -> Int
      loop !i !acc
        | i == 0 = acc
        | otherwise = loop (i - 1) (acc + f (i `rem` 4) 3)
  print (loop iters 0)
```

### Results

The cost a call of `f`, from step 3; each program prints 2750000 for 1000000 calls:

```
GHC      bytes a call   instructions a call
HEAD     24.00          58.55
9.14.1   24.00          58.51
9.12.4   24.00          58.51
9.10.3   24.00          58.51
9.8.4     0.00          42.00
```

The final Core on HEAD (`ReproLib.dump-simpl`); 9.14.1, 9.12.4 and 9.10.3 print the same `$wf`:

```
$wf
  = \ ww ww1 ->
      join {
        j2 q
          = case ># ww1 0# of {
              __DEFAULT -> ww1;
              1# -> case q of { Q bx bx1 -> *# bx bx1 }
            } } in
      join { exit ww2 ww3 = jump j2 (Q ww2 ww3) } in
      join { exit1 ww2 ww3 = jump j2 (Q ww3 ww2) } in
      joinrec {
        $wgo ww2 ww3
          = case >=# ww2 ww of {
              __DEFAULT ->
                case ># ww3 ww1 of {
                  __DEFAULT -> jump $wgo (+# ww2 1#) (+# ww3 ww2);
                  1# -> jump exit ww2 ww3
                };
              1# -> jump exit1 ww2 ww3
            }; } in
      jump $wgo 0# 0#
```

On 9.8.4, `j2` is inlined into both exits, and no `Q` is built:

```
      join {
        exit ww2 ww3
          = case ># ww1 0# of {
              __DEFAULT -> ww1;
              1# -> *# ww2 ww3
            } } in
```

The first occurrence analysis after Exitification, step 5, on HEAD, 9.14.1, 9.12.4 and 9.10.3:

```
j2 [Occ=OnceL2!T[1], Dmd=SC(S,!P(L))] :: Q -> Int#
```

On 9.8.4:

```
j2 [Occ=T[1], Dmd=SC(S,!P(L))] :: Q -> Int#
```

Step 6 prints no `Considering inlining: j2` on HEAD, 9.14.1, 9.12.4 or 9.10.3. On 9.8.4 it prints two decisions, each with `ANSWER = YES`.

## Expected behavior

A join point that no recursive group jumps to is not taken for an exit join point. Here `j2` is inlined into both exits, as in 9.8.4, and `f` allocates nothing.

## Environment

* GHC version used: HEAD 10.1.20260918 (`wip/T27737` at 6913545fd3, on master e2d5702699, with local patches) shows the problem, and so do 9.14.1, 9.12.4 and 9.10.3, without those patches; 9.8.4 does not.

Optional:

* Operating System: Linux
* System Architecture: x86_64

[exit-note]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Exitify.hs#L421-448
[add-jp]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/OccurAnal.hs#L3353-3367
[tracked]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/OccurAnal.hs#L785-792
[mk-one-occ]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/OccurAnal.hs#L3880-3889
[no-one-shot]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/OccurAnal.hs#L3224-3229
[adjust]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/OccurAnal.hs#L4053-4060
[union]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/OccurAnal.hs#L3997
[is-exit]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Simplify/Utils.hs#L3050-3055
[pre-inline]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1658
[let-unf]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4817-4833
[no-unf]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Simplify/Inline.hs#L114
[d036980238]: https://gitlab.haskell.org/ghc/ghc/-/commit/d03698023891b9d474915ad1cccdef8c8ba78e78

/label ~"T::bug"
/label ~"regression"
/label ~"occurrence analysis"
/label ~"join points"
/label ~"needs triage"
