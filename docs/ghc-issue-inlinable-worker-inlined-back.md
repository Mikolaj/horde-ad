# GHC issue: the worker of an INLINABLE function is inlined back into its wrapper from its INLINABLE unfolding, so a loop that worker/wrapper unboxed is built again with boxed arguments

Filed as GHC [#27984](https://gitlab.haskell.org/ghc/ghc/-/work_items/27984) on 2026-10-18; the text from "## Summary" down is the filed body, in the tracker's bug template. Title: **After worker/wrapper splits an INLINABLE function, the worker is inlined back into the wrapper from its INLINABLE unfolding, so the wrapper's loop takes boxed arguments at `-O`**. Verified on 2026-10-18 with GHC HEAD 10.1.20260918 (`wip/T27737` at 6913545fd3 on master e2d5702699, with uncommitted patches in Core/Map/Expr.hs, Simplify/Iteration.hs, Specialise.hs, Core/Utils.hs and rts/include/rts/prof/LDV.h) and ghc-9.14.1, 9.12.4, 9.10.3, 9.8.4 and 9.6.7, which all show it. Found in orthotope, item O25 of `docs/inlining-catalogue.md`: at orthotope 5f7f9da1, where `scalar` is INLINABLE, `Data.Array.Internal.Dynamic.scalar1` loops by a boxed counter and allocates one `I#` a call; the reproducer puts a loop of its own where orthotope has vector's fusion functions. The tracker was searched on 2026-10-18 for `worker inlined into wrapper`, `worker back into wrapper`, `INLINABLE worker unfolding`, `Worker/wrapper for INLINABLE`, `worker wrapper INLINABLE boxed`, `mkWorkerUnfolding` and `late-dmd-anal`, for the phrases "inlined into the wrapper", "back into the wrapper", "worker is inlined" and "inline the worker", and for titles with `INLINABLE` and `slower`, `allocates` or `reboxing`; every issue created since 2026-10-15 was listed. No duplicate was found; the nearest are GHC [#27976](https://gitlab.haskell.org/ghc/ghc/-/work_items/27976) (horde-ad's own, `docs/ghc-issue-unfolding-boxity-worker.md`), GHC [#20746](https://gitlab.haskell.org/ghc/ghc/-/work_items/20746) and GHC [#6087](https://gitlab.haskell.org/ghc/ghc/-/work_items/6087). Code and Note text checked at master f93d523c (2026-10-15); WorkWrap.hs, Unfold/Make.hs and Pipeline.hs there are the same as in the HEAD build, and so is the cited section of Simplify/Utils.hs, which is item 8 of GHC [#27973](https://gitlab.haskell.org/ghc/ghc/-/work_items/27973) for its names only (`docs/ghc-issue-doc-slips.md`). The prose is ASD-STE100 Simplified Technical English. Stated as open: no fix was tried.

## Summary

At `-O`, worker/wrapper can split an INLINABLE function. The worker then gets the INLINABLE unfolding ([Note [Worker/wrapper for INLINABLE functions]][note-ww-inl]). In the simplifier run after worker/wrapper, that unfolding can become small enough to inline, and the simplifier inlines the worker into its wrapper. It inlines the unfolding, which is the source form, and not the optimised right-hand side of the worker. Thus the wrapper builds again a loop that worker/wrapper had split. At `-O`, no worker/wrapper pass comes after this run ([Pipeline.hs, lines 174-181][pipeline-ww] and [lines 321-323][pipeline-late]), so the new loop takes its arguments boxed.

In the example below, `mkPlain` and `mkInlb` are the same except for the INLINABLE pragma. The loop in `mkInlb` takes two `I#` arguments, 32 bytes an iteration. `./Repro inlb 10000000` allocates 640 MB, against 58 KB for `./Repro plain 10000000`, and executes 2.3 times as many instructions. With `-flate-dmd-anal`, the loop in `mkInlb` takes `Int#` arguments. GHC 9.6.7, 9.8.4, 9.10.3, 9.12.4, 9.14.1 and HEAD all give this result.

The section "A note about wrappers" of Note [Simplifying inside stable unfoldings] says ([Simplify/Utils.hs, lines 1481-1490][note-wrappers]): "It's also important not to inline a worker back into a wrapper." Item 8 of #27973 is about the names in that section that the code does not have.

## Steps to reproduce

1. Save the two modules below as `ReproLib.hs` and `Repro.hs`, in an empty directory.
2. `ghc -O -rtsopts -ddump-simpl -dsuppress-all -dsuppress-uniques -ddump-to-file -dinline-check '$wmkInlb' Repro.hs`
3. `./Repro plain 10000000 +RTS -s` and `./Repro inlb 10000000 +RTS -s`
4. `perf stat -e instructions:u -x, ./Repro plain 10000000`, and the same with `inlb`
5. Do steps 2 to 4 again, with `-fforce-recomp -flate-dmd-anal` added in step 2.

```haskell
{-# LANGUAGE BangPatterns #-}
module ReproLib (G (..), T (..), mkPlain, mkInlb) where

data T = T ![Int] !Int !Int
data G = A ![Int] !T

-- A loop, inlined only from phase 1 on, as vector's fusion functions are.
{-# INLINE [1] sumFromTo #-}
sumFromTo :: Int -> Int -> Int -> Int
sumFromTo lo hi step = go lo 0
  where
    go :: Int -> Int -> Int
    go !i !acc
      | i > hi = acc
      | otherwise = go (i + step) (acc + i)

-- The same but for the pragma (and a constant, so that CSE does not merge them).
mkPlain :: Int -> G
mkPlain x = A [] (T [] 0 (sumFromTo (x - 7) (x * 3) 1))

mkInlb :: Int -> G
{-# INLINABLE mkInlb #-}
mkInlb x = A [] (T [] 0 (sumFromTo (x - 8) (x * 3) 1))
```

```haskell
module Main (main) where

import ReproLib
import System.Environment (getArgs)

-- NOINLINE, so that these run the code compiled in ReproLib, as a call
-- that does not inline mkPlain or mkInlb does.
plain, inlb :: Int -> G
{-# NOINLINE plain #-}
plain = mkPlain
{-# NOINLINE inlb #-}
inlb = mkInlb

main :: IO ()
main = do
  [what, n] <- getArgs
  let f = if what == "plain" then plain else inlb
  case f (read n) of A _ (T _ _ s) -> print s
```

### Results

Bytes allocated and `instructions:u` for one run with argument 10000000:

```
GHC      plain                          inlb                             inlb, -flate-dmd-anal
HEAD     58,144 B, 160,661,575 instr    640,058,152 B, 375,027,129 instr   57,848 B, 160,661,141 instr
9.14.1   58,664 B, 160,592,314 instr    640,058,672 B, 374,958,592 instr   58,368 B, 160,590,668 instr
9.12.4   58,768 B, 160,571,398 instr    640,058,776 B, 374,925,588 instr   58,472 B, 160,569,719 instr
9.10.3   58,728 B, 160,559,736 instr    640,058,736 B, 374,916,567 instr   58,432 B, 160,558,011 instr
9.8.4    58,728 B, 160,553,525 instr    640,058,736 B, 374,897,577 instr   58,432 B, 160,553,090 instr
9.6.7    59,064 B, 160,545,187 instr    640,059,072 B, 374,903,267 instr   58,768 B, 160,545,281 instr
```

On HEAD, `ReproLib.dump-simpl` has the two loops:

```
mkPlain
  = \ x ->
      case x of { I# ww ->
      let { hi = *# ww 3# } in
      joinrec {
        $wgo ww1 ww2
          = case ># ww1 hi of {
              __DEFAULT -> jump $wgo (+# ww1 1#) (+# ww2 ww1);
              1# -> A [] (T [] 0# ww2)
            }; } in
      jump $wgo (-# ww 7#) 0#
      }

lvl = I# 0#

mkInlb
  = \ x ->
      case x of { I# ww ->
      let { hi = *# ww 3# } in
      joinrec {
        go i acc
          = case i of { I# ipv ->
            case acc of { I# ipv1 ->
            case ># ipv hi of {
              __DEFAULT -> jump go (I# (+# ipv 1#)) (I# (+# ipv1 ipv));
              1# -> A [] (T [] 0# ipv1)
            }
            }
            }; } in
      jump go (I# (-# ww 8#)) lvl
      }
```

The steps, as the dumps show them on HEAD:

1. Before worker/wrapper, the INLINABLE unfolding of `mkInlb` has `Guidance=IF_ARGS [40] 152 10`, too large for `certainlyWillInline` (152 - 10 * 2 > 90; [WorkWrap.hs, line 785][cwi], [Unfold/Make.hs, line 429][cwi-size]), so worker/wrapper splits `mkInlb`. In `-ddump-worker-wrapper`, the worker `$wmkInlb` has the unfolding of `mkInlb` with the worker's code around it, `Src=StableUser` and `Guidance=IF_ARGS [0] 222 10` ([WorkWrap.hs, line 862][work-unf], and `mkWorkerUnfolding` in [Unfold/Make.hs, lines 126-135][mkwu]). Its template calls `sumFromTo`. Its right-hand side has the loop `$wgo :: Int# -> Int# -> G`.
2. In the simplifier run after worker/wrapper, the template becomes smaller (`-ddump-simpl-iterations`): its first iteration removes `A` (size 162), and its second removes `T` (size 102). For the call of `$wmkInlb` in the right-hand side of the wrapper and the call in its stable unfolding, `-dinline-check '$wmkInlb'` gives `guidance IF_ARGS [0] 162 10`, `adjusted size = 132`, `ANSWER = NO` in the first iteration, and `guidance IF_ARGS [0] 102 10`, `adjusted size = 72`, `ANSWER = YES` in the second.
3. In the wrapper, `sumFromTo` is then inlined, and the loop `go` is built again from its source. At `-O`, no pass after this splits `go`. With `-flate-dmd-anal`, the late worker/wrapper splits it. At `-O2`, SpecConstr specialises it on its `I#` arguments, and the loop `$sgo` takes `Int#`s (HEAD and 9.14.1).

The worker of `mkPlain` is also inlined back (`guidance IF_ARGS [0] 65 0`, `ANSWER = YES` with `-dinline-check '$wmkPlain'`), but its unfolding is made from its optimised right-hand side, so its loop keeps the `Int#` arguments. With a plain `INLINE` pragma or no pragma on `sumFromTo`, every decision on `$wmkInlb` is `ANSWER = NO`, and both loops take `Int#` arguments.

The interface of `ReproLib` gives `mkInlb` a `StableSystem` unfolding whose template calls `sumFromTo`. A client that scrutinises the result of a call, as in `case mkInlb (read n) of A _ (T _ _ s) -> print s`, inlines that unfolding and gets a loop with `Int#` arguments. The cost is in the code compiled in `ReproLib`, which every call that does not inline `mkInlb` runs.

## Expected behavior

As without the pragma: the loop in `mkInlb` takes `Int#` arguments, and `./Repro inlb 10000000` allocates 58 KB.

A possible fix, not tested: do not inline a worker that has an INLINABLE unfolding into its own wrapper. The section "A note about wrappers" says this of every worker.

### Related

- #27976: on HEAD, an INLINABLE unfolding that uses an argument boxed makes the worker take the argument boxed. Here the loop of the worker takes `Int#` arguments, and the inlining of the unfolding of the worker builds the boxed loop again. This occurs on 9.6.7 too.
- #20746: its description proposes to let a worker inline back into its wrapper where the split gives no benefit. Here the split gives a benefit, and the inlining removes it.
- #6087: whether `-O2` should include `-flate-dmd-anal`.
- #27973, item 8: the stale names in "A note about wrappers".

## Environment

* GHC version used: HEAD 10.1.20260918 (`wip/T27737` at 6913545fd3, on master e2d5702699, with local patches), 9.14.1, 9.12.4, 9.10.3, 9.8.4, 9.6.7

Optional:

* Operating System: Linux
* System Architecture: x86_64

[note-ww-inl]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/WorkWrap.hs#L186
[pipeline-ww]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Pipeline.hs#L174-181
[pipeline-late]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Pipeline.hs#L321-323
[note-wrappers]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1481-1490
[cwi]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/WorkWrap.hs#L785
[cwi-size]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Unfold/Make.hs#L429
[work-unf]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/WorkWrap.hs#L862
[mkwu]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Unfold/Make.hs#L126-135

/label ~"T::bug"
/label ~"needs triage"
