# GHC issue: on HEAD, the INLINE unfolding of a list producer stays unfused, so a late inlining builds the list

Filed as GHC [#27977](https://gitlab.haskell.org/ghc/ghc/-/work_items/27977) on 2026-10-17; the text from "## Summary" down is the filed body, in the tracker's bug template. Title: **HEAD regression: rules active only in early phases never fire in an always-active INLINE unfolding, so a list producer inlined in phase 0 builds its list**. Verified with GHC HEAD 10.1.20260918 (shows it) and ghc-9.14.1 and 9.12.4 (do not). Code and Note text checked at master f93d523c (2026-10-15); the cited code is the same there as in the HEAD build. Tracker search 2026-10-17: every issue created since 2026-10-15 (16 issues, titles read); GHC [#27963](https://gitlab.haskell.org/ghc/ghc/-/work_items/27963), "Rule fails to fire", is about a rule lost through a cast and is not related. The prose is ASD-STE100 Simplified Technical English. Stated as open: the cause, commit 2da84b7a83, is inferred and not bisected, since no GHC was built at it or its parent.

## Summary

On HEAD, an INLINE pragma on a list producer can make a program slower than no pragma. In the example below, the INLINE version of `pairs` costs 269,526 instructions and 256,032 bytes a call. Without the pragma, it costs 168,825 instructions and 224,032 bytes. GHC 9.14.1 and 9.12.4 give the two versions the same cost.

Two things combine:

1. HEAD does not fuse the stable unfolding of `pairs`. After the phase-1 pass, the template of the unfolding is `foldr (...) n (eftInt 0# 1999#)`. On 9.14.1, it is `eftIntFB (...) n 0# 1999#`.
2. GHC inlines `pairs` late. Its argument is a variable until phase 0, so `callSiteInline` refuses it, with the lines `arg infos [TrivArg]`, `interesting continuation BoringCtxt` and `some_benefit False`, and inlines it only once the argument is a value. The call of `pairs` is still there after the phase-1 pass and is gone after the phase-0 pass. In phase 0, the rule `"eftInt" [~1]` ([GHC/Internal/Enum.hs, line 617][eftint]) is not active. Thus the inlined `foldr` stays, and the list is built, floated to top level and mapped.

9.14.1 inlines `pairs` at the same point, but its unfolding is already fused, so nothing is lost.

Why the unfolding is not fused: Note [What is active in the RHS of a RULE or unfolding?] ([Simplify/Utils.hs, lines 1359-1385][note-war]) says that GHC fires, in the right-hand side of a rule with activation range A, only the rules that are active "(WAR1) throughout all of A" and "(WAR2) in the current phase", and that this applies "equally to the RHSs of stable unfoldings". `updModeForStableUnfoldings` and `phaseForRuleOrUnf` do this ([lines 1195-1249][upd]). An INLINE pragma with no phase is active in all phases, and `"eftInt" [~1]` is not active in phases 1 and 0. Thus the rule never fires in this unfolding. The Note does not mention fusion.

(WAR1), with its use for stable unfoldings, came with commit [2da84b7a83][2da84b7a83], "Only use active rules when simplifying rule RHSs", which fixed #26323. That commit is in 10.0.1-alpha1, and it is not in 9.14.1, 9.14.2-rc2 or 9.12.4. (WAR2) came later, with commit 269c408797 for #26826. I did not bisect, so that 2da84b7a83 causes the change is an inference.

Related: #15056 has the same pattern, a function inlined in phase 0 too late for rules, from a different cause. #21721 proposes to stabilise unfoldings before the phase in which a rule can fire.

## Steps to reproduce

1. Save the program below as `Repro.hs`.
2. `ghc -O -rtsopts -outputdir inl -o inline Repro.hs`
3. `ghc -O -rtsopts -DNOPRAGMA -outputdir nop -o nopragma Repro.hs`
4. Run `./inline K +RTS -s` and `./nopragma K +RTS -s`, and `perf stat -e instructions:u -x,` on the same commands, for K = 1000 and K = 2000. The cost a call is the difference between the two runs, divided by 1000.
5. To see the inlining decisions: `ghc -O -c -fforce-recomp -dinline-check pairs Repro.hs`
6. To see the unfolding after each pass: `ghc -O -c -fforce-recomp -dverbose-core2core -dsuppress-uniques -dsuppress-module-prefixes -dsuppress-type-applications -dsuppress-coercions -ddump-to-file Repro.hs`, then read `Repro.verbose-core2core`.
7. To see the final Core: `ghc -O -c -fforce-recomp -ddump-simpl -dsuppress-all -dsuppress-uniques Repro.hs`, with and without `-DNOPRAGMA`.

```haskell
{-# LANGUAGE CPP #-}
module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (forM_)
import System.Environment (getArgs)

-- A consumer called out of line.
{-# NOINLINE consume #-}
consume :: [(Int, Double)] -> Double
consume us = sum (map snd us)

-- A producer whose comprehension fuses with its generator; INLINE unless
-- -DNOPRAGMA.
#if !defined(NOPRAGMA)
{-# INLINE pairs #-}
#endif
pairs :: Int -> [(Int, Double)]
pairs i = [ (j, fromIntegral (j + i)) | j <- [0 .. 1999] ]

main :: IO ()
main = do
  [ks] <- getArgs
  forM_ [1 .. read ks] $ \ i -> evaluate (consume (pairs i))
```

### Results

The cost a call, from step 4:

```
GHC      INLINE pairs                           no pragma
HEAD     269,526 instructions, 256,032 bytes    168,825 instructions, 224,032 bytes
9.14.1   176,825 instructions, 224,032 bytes    176,825 instructions, 224,032 bytes
9.12.4   176,823 instructions, 224,032 bytes    176,823 instructions, 224,032 bytes
```

Step 5 gives the same decisions on HEAD and on 9.14.1: 16 refusals, each with the lines `arg infos [TrivArg]`, `interesting continuation BoringCtxt` and `some_benefit False`, then one `ANSWER = YES` with the lines `arg infos [ValueArg]`, `interesting continuation BoringCtxt` and `some_benefit True`.

The unfolding of `pairs` in the output of the phase-1 pass (`Phase = 1 [main]`), step 6, on HEAD:

```
         Tmpl= \ (i [Occ=OnceL1!] :: Int) ->
                 build
                   (\ (@a)
                      (c [Occ=OnceL1!, OS=OneShot] :: (Int, Double) -> a -> a)
                      (n [Occ=Once1, OS=OneShot] :: a) ->
                      foldr
                        (\ (ds :: Int) (ds [Occ=Once1, OS=OneShot] :: a) ->
                           c (ds,
                              D#
                                (case ds of { I# x [Occ=Once1] ->
                                 case i of { I# y [Occ=Once1] -> int2Double# (+# x y) }
                                 }))
                             ds)
                        n
                        (eftInt 0# 1999#))}]
```

On 9.14.1:

```
         Tmpl= \ (i [Occ=OnceL1!] :: Int) ->
                 build
                   (\ (@a)
                      (c [Occ=OnceL1!, OS=OneShot] :: (Int, Double) -> a -> a)
                      (n [Occ=Once1, OS=OneShot] :: a) ->
                      eftIntFB
                        (\ (ds :: Int) (ds [Occ=Once1, OS=OneShot] :: a) ->
                           c (ds,
                              case ds of { I# x [Occ=Once1] ->
                              case i of { I# y [Occ=Once1] -> D# (int2Double# (+# x y)) }
                              })
                             ds)
                        n
                        0#
                        1999#)}]
```

The final Core on HEAD with the INLINE pragma, step 7, builds the list of `[0 .. 1999]` once at top level and maps it in each call:

```
main2 = main_go2 0#
```

```
main_go2
  = \ x ->
      : (I# x)
        (case x of wild {
           __DEFAULT -> main_go2 (+# wild 1#);
           1999# -> []
         })
```

```
                                        case $wconsume (go1 main2) of ww1 { __DEFAULT -> D# ww1 })
```

Without the pragma, one producer makes the pairs directly: `case $wconsume (go1 0#) of ww1 { __DEFAULT -> D# ww1 })`.

## Expected behavior

An INLINE pragma on a list producer does not stop fusion, as in 9.14.1. For example, rules that are active in the phase where the unfolding is simplified could fire in an always-active unfolding.

## Environment

* GHC version used: HEAD 10.1.20260918 (`wip/T27737` at 6913545fd3, on master e2d5702699, with local patches that do not touch rule activation) shows the problem; 9.14.1 and 9.12.4 do not.

Optional:

* Operating System: Linux
* System Architecture: x86_64

[eftint]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/libraries/ghc-internal/src/GHC/Internal/Enum.hs#L617
[note-war]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1359-1385
[upd]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1195-1249
[2da84b7a83]: https://gitlab.haskell.org/ghc/ghc/-/commit/2da84b7a83f723dc6531cdad5ef3c7e624fda2fe

/label ~"T::bug"
/label ~"regression"
/label ~"fusion"
/label ~"rules"
/label ~"inlining"
/label ~"needs triage"
