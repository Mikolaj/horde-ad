# GHC issue: removing a bang that -Wredundant-bang-patterns reports changes the optimised Core, for worse or for better

Filed 2026-09-27 as [GHC work item 27862](https://gitlab.haskell.org/ghc/ghc/-/work_items/27862); this file stays as the filed record, the text from "## Summary" down being the filed body, verified on HEAD at 10.1.20260918 (checkout 6913545fd3) and on ghc-9.14.1, 9.12.4, 9.10.3 and 9.8.4. Title: **Removing a bang that `-Wredundant-bang-patterns` reports can make the optimised Core worse or better, because the desugarer does not group an equation that has `!x` with one that has `x`**. The prose is ASD-STE100 Simplified Technical English. Found while porting routines to orthotope's `pr-mikolaj-toVectorListT` branch, where the flag reports eight bangs in `absAxesAndStartT`, `routeT` and `unorderedRouteT` of `Data/Array/Internal.hs`. The tracker search of 2026-09-27 found no report of the effect. Two items are adjacent and different: GHC [#17340](https://gitlab.haskell.org/ghc/ghc/-/work_items/17340), where the flag was designed, and whose discussion says that a redundant pattern never makes code worse; and GHC [#25723](https://gitlab.haskell.org/ghc/ghc/-/work_items/25723), whose fix added clause (c) to (DJ3), the join-point inlining rule that the third item of the summary meets. The rule itself came with GHC commit `e026bdf275` (2024-03-22), which 9.12.1 and 9.12.4 contain and no 9.10 release does: the window in which item 3 appears, though not bisected.

## Summary

`-Wredundant-bang-patterns` reports a bang on a variable when an earlier equation has already forced the same argument on every path to this equation. About the semantics, the warning is correct. But when you remove such a bang, the optimised Core can change. It can become worse, and it can become better. Thus the warning is not a safe guide for clean-up.

The cause is in the desugarer. `groupEquations` in `GHC.HsToCore.Match` puts consecutive equations in one group only when their first patterns have the same `PatGroup`. A bang pattern is `PgBang`, a variable is `PgAny`, and `sameGroup PgBang PgAny` is `False`. Thus, when one equation has `!x` and the next equation has `x` in the same column, the match splits into two groups. The second group matches the remaining columns again, inside the failure join point of the first group.

The reproducer has three functions. They are the same, except for which equations have a bang on `off`. On HEAD with `-O`:

1. `allBangs` has a bang on all three equations. The flag reports the bangs on equations 2 and 3.
2. `firstBang` keeps only the bang that the flag does not report. Its worker matches both lists two times: the second match is in a join point `fail`, and the first match jumps to it. In the second match, GHC does not know that `n` is evaluated. Thus it builds the strict-field constructor `Axis x n` inside `case n of I#`, and in STG this is an updatable thunk, one for each axis with an extent other than 1 and a non-negative stride. `allBangs` allocates no thunk.
3. `lastLazy` removes only the bang on equation 3. Its worker is better than the worker of `allBangs`. `allBangs` keeps a join point `fail _ = (# axes, ww #)`, and its two `[]` alternatives jump to it. In `lastLazy`, the two `[]` alternatives return `(# axes, ww #)` directly.

Item 3 is also a change between versions. GHC 9.8.4 and 9.10.3 give the same Core for `allBangs` and `lastLazy`: CSE makes `allBangs` an alias of `lastLazy`. GHC 9.12.4, 9.14.1 and HEAD keep the join point in `allBangs`. The body of this join point has free variables, and (DJ3) in `Note [Duplicating join points]` does not inline such a join point unconditionally. Which pass keeps the join point in `allBangs` and removes it in `lastLazy` is not known. The desugared Core of the two functions is different only in the position of the join point: in `allBangs` it is inside `case off of off`, and in `lastLazy` it is outside.

## Steps to reproduce

1. Save the program below as `Repro.hs`.
2. `ghc -O -fforce-recomp -Wredundant-bang-patterns -ddump-simpl -dsuppress-all -dsuppress-uniques -c Repro.hs`
3. Read the three warnings. Then compare the workers `$wallBangs`, `$wfirstBang` and `$wlastLazy`.
4. To see the thunk, add `-ddump-stg-final` and find the `\u` closure in `$wfirstBang`.

`Repro.hs`:

```haskell
{-# LANGUAGE BangPatterns #-}
module Repro (allBangs, firstBang, lastLazy) where

data Axis = Axis !Int !Int

-- The axes of extent other than 1, their strides made positive, and
-- the offset moved by each negative stride. The three functions are
-- the same, except for the bangs on 'off'.

allBangs :: [Axis] -> Int -> [Int] -> [Int] -> ([Axis], Int)
allBangs axes !off (_ : sts) (1 : ns) = allBangs axes off sts ns
allBangs axes !off (st : sts) (n : ns)
  | st < 0 = allBangs (Axis (negate st) n : axes) (off + (n - 1) * st) sts ns
  | otherwise = allBangs (Axis st n : axes) off sts ns
allBangs axes !off _ _ = (axes, off)

-- Both bangs that the flag reports are removed.
firstBang :: [Axis] -> Int -> [Int] -> [Int] -> ([Axis], Int)
firstBang axes !off (_ : sts) (1 : ns) = firstBang axes off sts ns
firstBang axes off (st : sts) (n : ns)
  | st < 0 = firstBang (Axis (negate st) n : axes) (off + (n - 1) * st) sts ns
  | otherwise = firstBang (Axis st n : axes) off sts ns
firstBang axes off _ _ = (axes, off)

-- Only the last bang that the flag reports is removed.
lastLazy :: [Axis] -> Int -> [Int] -> [Int] -> ([Axis], Int)
lastLazy axes !off (_ : sts) (1 : ns) = lastLazy axes off sts ns
lastLazy axes !off (st : sts) (n : ns)
  | st < 0 = lastLazy (Axis (negate st) n : axes) (off + (n - 1) * st) sts ns
  | otherwise = lastLazy (Axis st n : axes) off sts ns
lastLazy axes off _ _ = (axes, off)
```

## Expected behavior

A bang that `-Wredundant-bang-patterns` reports has no effect on the optimised Core.

A possible change, not tested: in `groupEquations`, let an equation whose first pattern is `PgAny` join a `PgBang` group immediately before it. The semantics do not change. The first equation of the `PgBang` group forces the variable before GHC tries a later equation, so the variable is already evaluated when GHC tries the `PgAny` equation. The opposite order is not safe: a `PgAny` equation before a `PgBang` equation must not force the variable. With this change, `firstBang` and `lastLazy` get the desugaring of `allBangs`.

If the grouping stays as it is, the documentation of the warning can tell that the removal of a reported bang can change the generated code.

## Workarounds

Keep each reported bang, or put the bang on the argument in every equation, and use `-Wno-redundant-bang-patterns`. Before you remove a reported bang, compare the Core with the bang and without it.

## Environment

- GHC HEAD at 10.1.20260918 (6913545fd3), GHC 9.14.1, 9.12.4, 9.10.3 and 9.8.4. Items 1 and 2 on all five. Item 3 on 9.12.4, 9.14.1 and HEAD.
- On HEAD and on 9.8.4, `-O2` gives the same result as `-O`.
- x86-64 Linux.

/label ~"T::bug"

/label ~"needs triage"
