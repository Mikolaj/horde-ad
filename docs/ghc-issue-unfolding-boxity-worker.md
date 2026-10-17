# GHC issue: on HEAD, a boxed use of an argument in an INLINABLE unfolding keeps the worker from unboxing it

Filed as GHC [#27976](https://gitlab.haskell.org/ghc/ghc/-/work_items/27976) on 2026-10-17; the text from "## Summary" down is the filed body, in the tracker's bug template. Title: **HEAD regression: when an INLINABLE unfolding uses an argument boxed, the worker takes the argument boxed**. Verified with GHC HEAD 10.1.20260918 (shows it) and ghc-9.14.1 and 9.12.4 (do not). A tracker search of 2026-10-16 found no report, and none of the notes of GHC MR [!15238](https://gitlab.haskell.org/ghc/ghc/-/merge_requests/15238), the fix of GHC [#26416](https://gitlab.haskell.org/ghc/ghc/-/work_items/26416), discusses this. Code and Note text checked at master f93d523c (2026-10-15); DmdAnal.hs there is the same as in the HEAD build, and Types/Demand.hs differs by f76464cf and ea5c054d, neither in the lines cited. Tracker search 2026-10-17: every issue created since 2026-10-15 (16 issues, titles read), none related. The prose is ASD-STE100 Simplified Technical English. Stated as open: the cause, commit 870243e4, is suspected and not confirmed, since no GHC was built at it or its parent.

## Summary

On HEAD, an INLINABLE pragma can stop worker/wrapper from unboxing a strict argument. This happens when the stable unfolding uses the argument boxed and the optimised right-hand side uses it unboxed. The worker then takes the argument boxed, and each caller boxes it. GHC 9.14.1 and 9.12.4 unbox the argument. In the example below, the cost on HEAD is 16 bytes and about 7 instructions a call.

In the example, `fPlain` and `fInlb` differ only in the INLINABLE pragma. A phase-1 rule removes the call of `g` from the right-hand side, which then uses `x` unboxed. The unfolding is simplified in the initial phase and keeps the call of `g`, which uses `x` boxed.

The suspected cause is commit [870243e4][870243e4], "DmdAnal: Take stable unfoldings into account when determining argument demands", the fix of #26416. It is in 10.0.1-alpha1, and it is not in 9.14.1, 9.14.2-rc2 or 9.12.4. I did not build GHC at it or at its parent. Since that commit, `addUnfoldingDemands` combines the demands of the right-hand side and of the unfolding with `maxDmdType` ([Core/Opt/DmdAnal.hs, lines 1181-1191][add-unf]). `maxSubDmd` combines the boxities with `lubBoxity` ([Types/Demand.hs, lines 940-950][max-sub]), and `lubBoxity = boxedWins` ([lines 374-376][lub]). Note [Combining demands for stable unfoldings] ([lines 870-911][note-comb]) gives the reasons for the combination of strictness and of usage. It does not mention boxity.

## Steps to reproduce

1. Save the two modules below as `ReproLib.hs` and `Repro.hs`, in an empty directory.
2. `ghc -O -rtsopts -ddump-simpl -dsuppress-all -dsuppress-uniques -ddump-to-file Repro.hs`
3. `./Repro plain 10000000 +RTS -s` and `./Repro inlb 10000000 +RTS -s`
4. `perf stat -e instructions:u -x, ./Repro plain 10000000`, and the same with `inlb`
5. `ghc --show-iface ReproLib.hi`

```haskell
module ReproLib (fPlain, fInlb) where

-- Lazy in x and returns it, so a boxed use; a phase-1 rule removes the call.
g :: Bool -> Int -> Int
{-# NOINLINE g #-}
g b x = if b then x else 0
{-# RULES "g/True" [1] forall x. g True x = x #-}

-- After phase 1 the right-hand side uses x unboxed; the INLINABLE
-- unfolding, simplified in the initial phase, keeps the call of g.
fPlain :: Int -> Int
fPlain x = big (g True x) 2

fInlb :: Int -> Int
{-# INLINABLE fInlb #-}
fInlb x = big (g True x) 3

-- Large enough that neither is inlined and worker/wrapper splits both.
big :: Int -> Int -> Int
{-# INLINE big #-}
big r k
  | r > 1000 = r * k + 7 * r
  | r > 500 = r - k * 3 + 11
  | r > 300 = (r + k) * (r - k) + 5
  | r > 200 = r * r * k - 13
  | r > 100 = r * k * k + 17 * r
  | r > 50 = (r - 7) * (k + 9) - r * 21
  | otherwise = (r + 43) * (k - 47) * r
```

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import ReproLib
import System.Environment (getArgs)

loopP, loopI :: Int -> Int -> Int
loopP 0 !acc = acc
loopP k !acc = loopP (k - 1) (acc + fPlain k)
loopI 0 !acc = acc
loopI k !acc = loopI (k - 1) (acc + fInlb k)

main :: IO ()
main = do
  [what, n] <- getArgs
  print $ if what == "plain" then loopP (read n) 0 else loopI (read n) 0
```

### Results

Bytes allocated and `instructions:u` for one run of 10^7 calls:

```
GHC      plain                          inlb
HEAD     58,096 B, 180,665,042 instr    160,057,800 B, 254,080,173 instr
9.14.1   58,616 B, 180,594,838 instr    58,320 B, 180,594,333 instr
9.12.4   58,720 B, 180,573,714 instr    58,424 B, 180,573,245 instr
```

On HEAD, the interface of `ReproLib` gives `fInlb` the boxed demand `<1L>` in place of `<1!P(L)>`, and a worker that takes `Int`:

```
  $wfInlb :: GHC.Internal.Types.Int -> GHC.Internal.Prim.Int#
  $wfPlain :: GHC.Internal.Prim.Int# -> GHC.Internal.Prim.Int#
  fInlb :: GHC.Internal.Types.Int -> GHC.Internal.Types.Int
   LambdaFormInfo: LFReEntrant 1, Arity: 1, Strictness: <1L>, CPR: 1,
  fPlain :: GHC.Internal.Types.Int -> GHC.Internal.Types.Int
   LambdaFormInfo: LFReEntrant 1, Arity: 1, Strictness: <1!P(L)>,
```

On 9.14.1, the two functions are alike:

```
  $wfInlb :: GHC.Internal.Prim.Int# -> GHC.Internal.Prim.Int#
  fInlb :: GHC.Internal.Types.Int -> GHC.Internal.Types.Int
   Arity: 1, Strictness: <1!P(L)>, CPR: 1, Inline: [2],
```

On HEAD, the loop in `Repro.hs` boxes its counter at each iteration to call the worker (`Repro.dump-simpl`):

```
$wloopI
  = \ ds ww ->
      case ds of wild { I# ds1 ->
      case ds1 of wild1 {
        __DEFAULT ->
          case $wfInlb wild of ww1 { __DEFAULT ->
          $wloopI (I# (-# wild1 1#)) (+# ww ww1)
          };
        0# -> ww
      }
      }
```

## Expected behavior

As in 9.14.1: the worker of `fInlb` takes `Int#`, and the loop allocates nothing.

## Environment

* GHC version used: HEAD 10.1.20260918 (`wip/T27737` at 6913545fd3, on master e2d5702699, with local patches that do not touch demand analysis) shows the problem; 9.14.1 and 9.12.4 do not.

Optional:

* Operating System: Linux
* System Architecture: x86_64

[870243e4]: https://gitlab.haskell.org/ghc/ghc/-/commit/870243e4f2a24730539f01ee8e3f3949c42ff312
[add-unf]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/DmdAnal.hs#L1181-1191
[max-sub]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Types/Demand.hs#L940-950
[lub]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Types/Demand.hs#L374-376
[note-comb]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Types/Demand.hs#L870-911

/label ~"T::bug"
/label ~"regression"
/label ~"demand analysis"
/label ~"CPR/boxity analysis"
/label ~"needs triage"
