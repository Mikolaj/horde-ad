# GHC issue: a SPECIALISE pragma on an INLINE function makes a copy without the INLINE unfolding

Filed as GHC [#27975](https://gitlab.haskell.org/ghc/ghc/-/work_items/27975) on 2026-10-17; the text from "## Summary" down is the filed body, in the tracker's bug template. Title: **The copy that a SPECIALISE pragma makes of an INLINE function gets no INLINE unfolding, so importing modules lose fusion**. Verified with GHC HEAD 10.1.20260918 and ghc-9.14.1, 9.12.4 and 9.10.3, which all give the result shown; the `-ddump-ec-trace` lines were taken on HEAD only. Code and Note text checked at master f93d523c (2026-10-15). HsToCore/Binds.hs at master differs from the HEAD build in two hunks, neither in the lines cited. A tracker search of 2026-10-16 found no report. Tracker search 2026-10-17: every issue created since 2026-10-15 (16 issues, titles read), none related. The prose is ASD-STE100 Simplified Technical English. Nothing is stated as open.

## Summary

A SPECIALISE pragma on an INLINE function makes a specialised copy and a rule that rewrites calls to the copy. The copy does not get the INLINE unfolding. An importing module rewrites its call to the copy and then calls the worker of the copy out of line. In the example below, the importing module thus builds a list. Without the SPECIALISE pragma, it builds no list. `SPECIALISE INLINE` gives the same result as `SPECIALISE`.

The cause is an order in `dsAbsBinds`. It runs `dsSpecs` before `makeCorePair` gives the function its INLINE unfolding ([HsToCore/Binds.hs, lines 303-308][ds-order]). `dsSpec_help` takes the unfolding of the function, `fn_unf = realIdUnfolding poly_id` ([lines 1045-1046][fn-unf]). That unfolding is still empty, thus `specUnfolding` goes to its last equation, `specUnfolding _ _ _ _ _ = noUnfolding` ([Unfold/Make.hs, lines 205-221][spec-unf]). On HEAD, `ghc -O -c -ddump-ec-trace ReproLib.hs` shows this:

```
dsSpec(new route)
  poly_id sumSq
  unfolding No unfolding
```

The code means to give the copy the unfolding:

1. Note [Specialising unfoldings] ([Unfold/Make.hs, lines 232-237][note-spec]): "it would be very odd if a function marked INLINE was specialised (because of some local use), and then forever after (including importing modules) the specialised version wasn't INLINEd!"
2. The comment in `dsSpec_help` ([HsToCore/Binds.hs, lines 1053-1058][comment-body]): "We also use mk_spec_body to specialise the methods in f's stable unfolding".
3. The comment after it ([lines 1068-1070][comment-pair]): "NB: do *not* use makeCorePair on (spec_id,spec_rhs), because makeCorePair overwrites the unfolding, which we have just created using specUnfolding".

## Steps to reproduce

1. Save the two modules below as `ReproLib.hs` and `Repro.hs`, in an empty directory.
2. `ghc -O -ddump-simpl -ddump-rule-firings -dsuppress-all -dsuppress-uniques -ddump-to-file ReproLib.hs Repro.hs`
3. `ghc --show-iface ReproLib.hi`
4. For comparison, delete the SPECIALISE line from `ReproLib.hs` and do steps 2 and 3 again in another empty directory.

```haskell
module ReproLib (sumSq) where

sumSq :: Num a => [a] -> a
{-# INLINE sumSq #-}
{-# SPECIALISE sumSq :: [Int] -> Int #-}
sumSq xs = foldr (\x acc -> x * x + acc) 0 xs
```

```haskell
module Repro (total) where

import ReproLib

total :: Int -> Int
total n = sumSq [1 .. n]
```

### Results

With the SPECIALISE pragma, `Repro.dump-rule-firings` has `Rule fired: USPEC sumSq @Int (ReproLib)`, and `Repro.dump-simpl` builds the list and gives it to the worker of the copy:

```
$wtotal
  = \ ww ->
      case ># 1# ww of {
        __DEFAULT ->
          letrec {
            go2
              = \ x ->
                  : (I# x)
                    (case ==# x ww of {
                       __DEFAULT -> go2 (+# x 1#);
                       1# -> []
                     }); } in
          $wgo1 (go2 1#);
        1# -> case total1 of { I# v1 -> v1 }
      }
```

In the interface, the unfolding of the copy is the worker/wrapper wrapper, not the template that the user wrote:

```
  sumSq_$ssumSq :: [GHC.Internal.Types.Int] -> GHC.Internal.Types.Int
  [HasNoCafRefs, TagSig: <TagFun[TagEPT]>,
   LambdaFormInfo: LFReEntrant 1, Arity: 1, Strictness: <1L>, CPR: 1,
   Inline: [2],
   Unfolding: Core: StableSystem <1,TrueFalse>
              \ (xs['GHC.Internal.Types.Many] :: [GHC.Internal.Types.Int]) ->
              case $wgo1 xs of ww { DEFAULT -> GHC.Internal.Types.I# ww }]
```

Without the SPECIALISE pragma, `Repro.dump-rule-firings` has `Rule fired: fold/build (GHC.Internal.Base)`, and there is no list:

```
$wtotal
  = \ ww ->
      case ># 1# ww of {
        __DEFAULT ->
          letrec {
            $wgo2
              = \ x ->
                  join { $j y = +# (*# x x) y } in
                  case ==# x ww of {
                    __DEFAULT ->
                      case $wgo2 (+# x 1#) of ww1 { __DEFAULT -> jump $j ww1 };
                    1# -> jump $j 0#
                  }; } in
          $wgo2 1#;
        1# -> 0#
      }
```

With `{-# SPECIALISE INLINE sumSq :: [Int] -> Int #-}`, the result is the same as with `SPECIALISE`.

## Expected behavior

The specialised copy of an INLINE function gets the specialised INLINE unfolding, as Note [Specialising unfoldings] says. Then `Repro` fuses with the pragma as it does without it.

## Environment

* GHC version used: HEAD 10.1.20260918 (`wip/T27737` at 6913545fd3, on master e2d5702699, with local patches that do not touch the desugarer), 9.14.1, 9.12.4 and 9.10.3, all with the same result.

Optional:

* Operating System: Linux
* System Architecture: x86_64

[ds-order]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/HsToCore/Binds.hs#L303-308
[fn-unf]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/HsToCore/Binds.hs#L1045-1046
[spec-unf]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Unfold/Make.hs#L205-221
[note-spec]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Unfold/Make.hs#L232-237
[comment-body]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/HsToCore/Binds.hs#L1053-1058
[comment-pair]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/HsToCore/Binds.hs#L1068-1070

/label ~"T::bug"
/label ~"specialisation"
/label ~"desugaring"
/label ~"needs triage"
