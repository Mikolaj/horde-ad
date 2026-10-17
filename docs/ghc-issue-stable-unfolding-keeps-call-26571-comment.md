# GHC issue comment: a real program where a worker/wrapper stable unfolding keeps a once-called worker out of line

Posted 2026-10-17 as a comment on GHC [#26571](https://gitlab.haskell.org/ghc/ghc/-/work_items/26571) ("Occurence analysis: GHC is likely to give non-exported top level bindings OccMany if they are mentioned in bindings with rules or unfoldings."), which simonpj ruled by design ("Actually this is by-design"); this file stays as the record of the comment, the text from "On #26570" down being the body as posted. Verified with GHC HEAD 10.1.20260918 and ghc-9.14.1, which give the same result for the small module. The orthotope steps are read from the dumps of an earlier orthotope build; orthotope was not rebuilt for this draft. The 40 bytes a call is an earlier orthotope measurement (the cost of an edit to orthotope that leaves this call in place), not re-measured. Both issues' descriptions and all their notes were read on 2026-10-17; neither has a program in which the unfolding comes from worker/wrapper. The prose is ASD-STE100 Simplified Technical English. Stated as open: a base-only reproducer of orthotope's own route (a worker inlined back into its wrapper), which was not made.

On #26570, simonpj asked of a related rule: "would there be any benefit in a real program?" Here is a cost of the rule of this issue in a real program. The stable unfolding is not the user's: worker/wrapper made it, for a binding that is not exported and never inlined.

In a benchmark module of the orthotope library, compiled with HEAD at `-O`, worker/wrapper splits a summing function `lvl` into a worker and a wrapper with a `StableSystem` unfolding. The worker is then inlined back into the wrapper, into its right-hand side and into its unfolding (as read from the dumps before and after that Simplifier run). Thus the one call of `$w$dSummed`, the worker of a specialised dictionary, occurs twice in `lvl`: once in its right-hand side and once in its stable unfolding. By Note [Occurrences in stable unfoldings and RULES] the second occurrence counts as many. So `$w$dSummed` has no `Occ=` in each iteration of the final Simplifier, `preInlineUnconditionally` does not inline it, and `callSiteInline` refuses it at `adjusted size = 91`, one above `unfoldingUseThreshold = 90`. Tidy then drops the unfolding of `lvl`, and the final Core has one call, out of line. In one row of that benchmark, the build with this call allocates 40 bytes a call more than a build in which the call is inlined.

A small module shows a related cost of a worker/wrapper unfolding, by another route:

```haskell
module Repro (f1, f2) where

h :: Either [Char] Int -> Double
h (Left _) = 0
h (Right a) = go 0 0 + go2 0 0
  where
    go :: Int -> Double -> Double
    go i acc | i >= a = acc
             | otherwise = go (i + 1) (acc + fromIntegral (i * a `mod` 7))
    go2 :: Int -> Double -> Double
    go2 i acc | i >= a = acc
              | otherwise = go2 (i + 1) (acc + fromIntegral (i * a `mod` 5))

f1, f2 :: Int -> Double
f1 x = h (Right x)
f2 x = h (Right x)
```

With `ghc -O -c -ddump-simpl -dsuppress-all -dsuppress-uniques -dinline-check '$wh' Repro.hs` on HEAD (10.1.20260918) and 9.14.1, worker/wrapper does not split the small `f1`. It gives `f1` a stable unfolding instead (on HEAD, `ghc --show-iface Repro.hi`):

```
  f1 :: GHC.Internal.Types.Int -> GHC.Internal.Types.Double
  [HasNoCafRefs, TagSig: <TagFun[TagEPT]>,
   LambdaFormInfo: LFReEntrant 1, Arity: 1, Strictness: <L>, CPR: 1,
   Unfolding: Core: StableSystem <1,TrueFalse>
              \ (x['GHC.Internal.Types.Many] :: GHC.Internal.Types.Int) ->
              h (GHC.Internal.Data.Either.Right
                   @[GHC.Internal.Types.Char]
                   @GHC.Internal.Types.Int
                   x)]
```

That unfolding keeps `h`, the wrapper of `$wh`, alive, so `$wh` occurs in `h` and in `f1`. In the last occurrence analysis (`-ddump-occur-anal`), `$wh` is `$wh [InlPrag=[2]]`, with no `Occ=`. Each call-site decision about `$wh` says `ANSWER = NO`; the last one says `adjusted size = 93`. The final Core keeps the call:

```
h = \ ds -> case $wh ds of ww { __DEFAULT -> D# ww }

f1 = \ x -> case $wh (Right x) of ww { __DEFAULT -> D# ww }

f2 = f1
```

With `-fno-worker-wrapper`, `f1` has no stable unfolding, `h` is inlined into `f1`, and neither `h` nor `$wh` is left. Note [Inline pragma for certainlyWillInline] ([WorkWrap.hs, lines 736-759][note-cwi]) describes this keep-alive: "So I decided to live with the problem." Its reason, "so there is no great harm", is about an absent binding, and does not cover a callee left out of line.

[note-cwi]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/WorkWrap.hs#L736-759
