# GHC issue: CSE drops the INLINE unfolding of a function whose right-hand side equals that of another function

Filed as GHC [#27974](https://gitlab.haskell.org/ghc/ghc/-/work_items/27974) on 2026-10-17; the text from "## Summary" down is the filed body, in the tracker's bug template. Title: **CSE drops the INLINE or INLINABLE unfolding of a function whose right-hand side equals that of another function**. Verified with GHC HEAD 10.1.20260918 and ghc-9.14.1, 9.12.4 and 9.10.3, which all give the result shown; the INLINABLE form was run on HEAD and 9.14.1. A tracker search of 2026-10-16 found no report, and GHC MR [!13509](https://gitlab.haskell.org/ghc/ghc/-/merge_requests/13509) keeps the zap. Code and Note text checked at master f93d523c (2026-10-15); CSE.hs there is the same as in the HEAD build. Tracker search 2026-10-17: every issue created since 2026-10-15 (16 issues, titles read), none related. The prose is ASD-STE100 Simplified Technical English. Nothing is stated as open.

## Summary

An INLINE or INLINABLE pragma gives a function a stable unfolding with the code that the user wrote. If another function in the module has the same optimised right-hand side, CSE can replace the right-hand side of the pragma function by the other function. Then CSE also deletes the stable unfolding. The INLINE pragma stays, but the unfolding is now only the name of the other function. An importing module inlines that name and calls the other function out of line. In the example below, this stops list fusion in the importing module.

In the example, the INLINE function comes first in the source, and CSE still replaces its right-hand side.

The code, in CSE.hs: [`cse_bind`][cse-bind] deletes the stable unfolding of each binding whose right-hand side CSE replaced. It does not look at the source of the unfolding:

```
    out_id'' | cse_done  = zapStableUnfolding $
                           delayInlining toplevel out_id'
```

[`noCSE`][nocse] tests `isStableUserUnfolding`. For a single recursive binding, `cseBind` tests `noCSE` first ([lines 400-402][rec-nocse]) and then does not change the binding. For a non-recursive binding, and for each binding of a larger recursive group, only `extendCSEnvWithBinding` tests it ([line 489][ext-env]). There the test keeps the binding out of the reverse mapping, but `cse_bind` still replaces the right-hand side and deletes the unfolding.

Note [CSE for stable unfoldings] says of a binding with a user pragma ([lines 239-245][note-promise]): "we promised to inline foo as what the user wrote". Its wrinkle about the zap ([lines 267-282][note-wrinkle]) is about an unfolding "added by strictness analysis, say". The open !13509 rewrites the text of that wrinkle and keeps the zap.

Related: #13340 added the `isStableUserUnfolding` test to `noCSE`, for the other direction. #25526 is a different order dependence in CSE, where a SPECIALISE rule is lost.

## Steps to reproduce

1. Save the two modules below as `ReproLib.hs` and `Repro.hs`, in an empty directory.
2. `ghc -O -ddump-cse -ddump-simpl -dsuppress-all -dsuppress-uniques -ddump-to-file ReproLib.hs Repro.hs`
3. `ghc --show-iface ReproLib.hi`
4. For comparison, do steps 2 and 3 again in another empty directory, with `-fno-cse` added to step 2.

```haskell
module ReproLib (sumSq, sumSqInl) where

sumSqInl :: [Integer] -> Integer
{-# INLINE sumSqInl #-}
sumSqInl xs = foldr (\x acc -> x * x + acc) 0 xs

sumSq :: [Integer] -> Integer
sumSq xs = foldr (\x acc -> x * x + acc) 0 xs
```

```haskell
module Repro (total) where

import ReproLib

total :: Integer -> Integer
total n = sumSqInl [1 .. n]
```

### Results

`ReproLib.dump-cse` has:

```
sumSqInl = sumSq
```

The interface of `ReproLib` keeps the INLINE pragma, but the unfolding is only `sumSq`:

```
  sumSqInl ::
    [GHC.Internal.Bignum.Integer.Integer]
    -> GHC.Internal.Bignum.Integer.Integer
  [TagSig: <TagFun[TagDunno]>, LambdaFormInfo: LFReEntrant 1,
   Arity: 1, Strictness: <1L>, Inline: (sat-args=1),
   Unfolding: Core: <vanilla> sumSq]
```

Thus `Repro` builds the list and calls `sumSq` (`Repro.dump-simpl`):

```
total = \ n -> sumSq (enumDeltaToInteger1 total1 n)
```

With `-fno-cse`, the interface has `Unfolding: Core: StableUser <1,FalseFalse>` with the `foldr` template, and `total` is one fused loop:

```
total
  = \ n ->
      letrec {
        go2
          = \ x ->
              case x of x1 { __DEFAULT ->
              case n of y1 { __DEFAULT ->
              case integerGt# x1 y1 of {
                __DEFAULT ->
                  integerAdd (integerMul x1 x1) (go2 (integerAdd x1 total3));
                1# -> total2
              }
              }
              }; } in
      go2 total1
```

With `{-# INLINABLE sumSqInl #-}` in place of the INLINE pragma, the result is the same: `sumSqInl = sumSq`, and `total` calls `sumSq`.

## Expected behavior

A function with an INLINE or INLINABLE pragma keeps the stable unfolding that the user wrote, as with `-fno-cse`. CSE can replace its right-hand side, but not its user unfolding.

## Environment

* GHC version used: HEAD 10.1.20260918 (`wip/T27737` at 6913545fd3, on master e2d5702699, with local patches that do not touch CSE.hs), 9.14.1, 9.12.4 and 9.10.3, all with the same result.

Optional:

* Operating System: Linux
* System Architecture: x86_64

[cse-bind]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/CSE.hs#L450-457
[nocse]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/CSE.hs#L514-522
[rec-nocse]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/CSE.hs#L400-402
[ext-env]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/CSE.hs#L489
[note-promise]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/CSE.hs#L239-245
[note-wrinkle]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/CSE.hs#L267-282

/label ~"T::bug"
/label ~"CSE"
/label ~"inlining"
/label ~"needs triage"
