# GHC issue: when an INLINABLE caller gets a worker, importers lose the SPECIALISE rule of a function that it calls

Filed as GHC [#27921](https://gitlab.haskell.org/ghc/ghc/-/work_items/27921) on 2026-10-10; the text from "## Summary" down is the body as drafted, in the tracker's bug template. Title: **An INLINABLE function that gets a worker hides the SPECIALISE rule of its callee from importing modules**. Verified on 2026-10-10 on HEAD 10.1.20260918 (checkout 6913545fd3), 9.14.1, 9.12.4, 9.10.3, 9.8.4 and 9.6.7. Found when a library `SPECIALISE` of orthotope's `fromStorable`, tried as a workaround for GHC [#27920](https://gitlab.haskell.org/ghc/ghc/-/work_items/27920), had no effect. The comment posted on GHC [#20364](https://gitlab.haskell.org/ghc/ghc/-/work_items/20364) on 2026-10-10 to point here is recorded in `docs/ghc-issue-specialise-hidden-by-worker-20364-comment.md`. The prose is ASD-STE100 Simplified Technical English.

## Summary

In the reproducer below, `Lib` has a `SPECIALISE` pragma for `helper` at `Double`, and an INLINABLE function `f` that calls `helper`. `Repro` uses `f` at `Double`. Because of the bangs in `f`, `f` gets a worker, and `Repro` then calls the worker of `helper` with the dictionary `$fNumDouble`, although `Lib` exports the specialisation `helper_$shelper`. Without the bangs, `Repro` calls the worker of that specialisation, `$w$shelper`. GHC 9.6.7, 9.8.4, 9.10.3, 9.12.4, 9.14.1 and HEAD all do the same, and none gives a warning.

The cause is in the interface of `Lib` (`ghc --show-iface Lib.hi` on HEAD). Without the bangs, the INLINABLE unfolding of `f` calls `helper`, and `Lib.hi` has the rule "USPEC helper @Double", which sends `helper @Double` to `helper_$shelper`. Thus the specialisation of `f` in `Repro` gets to `helper_$shelper`. With the bangs, `f` is a wrapper that calls `$wf`, and the INLINABLE unfolding is on `$wf` (Note [Worker/wrapper for INLINABLE functions]). That unfolding has the activation `[2]`, and it calls `$whelper`: the wrapper of `helper`, which is also active from phase 2, was inlined into it. The rule is only for `helper`, thus it cannot apply to `$whelper`. `helper` has no INLINABLE pragma, thus `Repro` cannot specialise `$whelper` itself.

Item 4 of Note [Wrapper activation] wants to prevent exactly this: a wrapper that inlines before a specialisation rule can fire. Here the wrapper inlines in the defining module, so no importing module can fire the rule.

### Related

- #20364: rules do not fire on workers. This issue is a case of it, with a run-time cost and no user rule.
- #21851 and #22097: fixed by making rules win over inlining. That fix needs the call of `helper` to reach the importing module, but here the defining module has already replaced it.
- #27920: a `SPECIALISE` on the callee was tried there as a workaround, and this issue is why it had no effect.

## Steps to reproduce

```haskell
{-# LANGUAGE BangPatterns #-}
module Lib (f, helper) where

helper :: Num t => Int -> t -> t
helper 0 acc = acc
helper n acc = helper (n - 1) (acc + fromIntegral n)
{-# SPECIALISE helper :: Int -> Double -> Double #-}

f :: Num t => Int -> [Int] -> t -> t
{-# INLINABLE f #-}
f !_ [] acc = acc
f !k (n : ns) acc = helper (n + k) (f k ns acc)
```

```haskell
module Repro where

import Lib

run :: [Int] -> Double -> Double
run = f 1
```

```
ghc -O -c Lib.hs
ghc -O -c Repro.hs -ddump-simpl -dsuppress-all -dno-typeable-binds
```

On HEAD, `Repro` specialises `f`, but it calls `$whelper` with the dictionary:

```
Rec {
$s$wf
  = \ ww_aAQ ds_aAR acc_aAS ->
      case ds_aAR of {
        [] -> acc_aAS;
        : n_aAV ns_aAW ->
          case n_aAV of { I# x_aB0 ->
          $whelper
            $fNumDouble (+# x_aB0 ww_aAQ) ($s$wf ww_aAQ ns_aAW acc_aAS)
          }
      }
end Rec }
```

## Expected behavior

`Repro` calls the specialisation that `Lib` exports, as it does when `f` has no bangs (`f _ [] acc = acc` and `f k (n : ns) acc = ...`). Then the final Core calls `$w$shelper`, and no call passes a dictionary.

### Workarounds

Each was tested on the reproducer with HEAD.

- `INLINABLE` on `helper`. Then `Repro` makes its own specialisation, `$w$s$whelper`, and does not use the one in `Lib`.
- `-fno-worker-wrapper` on `Lib`. Then `Repro` calls `helper_$shelper`.

These have no effect: `-flate-specialise` or `-fspecialise-aggressively` on `Repro`, and `-fexpose-all-unfoldings` or `-fexpose-overloaded-unfoldings` on `Lib`.

## Environment

* GHC version used: HEAD 10.1.20260918 (commit 6913545fd3), 9.14.1, 9.12.4, 9.10.3, 9.8.4, 9.6.7

Optional:

* Operating System: Ubuntu 24.04
* System Architecture: x86_64

/label ~"T::bug"
/label ~"needs triage"
