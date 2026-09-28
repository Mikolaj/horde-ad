# GHC issue: an INLINE pragma on a self-recursive function stops worker/wrapper since 9.12.4

Filed 2026-09-29 as [GHC work item 27868](https://gitlab.haskell.org/ghc/ghc/-/work_items/27868); this file stays as the filed record, the text from "## Summary" down being the filed body. Title: **Since 9.12.4, an INLINE pragma on a self-recursive function stops worker/wrapper**. Verified with ghc-9.6.7, 9.10.3, 9.12.4, 9.14.1 and HEAD at 10.1.20260918 (checkout 6913545fd3). The prose is ASD-STE100 Simplified Technical English. Found while measuring the INLINE pragmas of horde-ad's tensor-kind dispatchers. The tracker search of 2026-09-29 found no report of the effect. The change that probably causes it came with GHC [#26903](https://gitlab.haskell.org/ghc/ghc/-/work_items/26903); the INLINABLE and NOINLINE forms of the problem were corrected in GHC [#6056](https://gitlab.haskell.org/ghc/ghc/-/work_items/6056) and GHC [#13143](https://gitlab.haskell.org/ghc/ghc/-/work_items/13143).

## Summary

GHC cannot inline a self-recursive function, because the function is its own loop breaker. Thus an INLINE pragma on such a function has no effect in 9.6.7, 9.10.3 and 9.14.1: the function gets the same worker as without the pragma. In 9.12.4 and HEAD, the pragma stops worker/wrapper. The strict arguments stay boxed and each recursive call allocates them.

The probable cause is commit 99d8c146c1, "Fix subtle bug in cast worker/wrapper", for #26903. It changes `hasInlineUnfolding` to use `realUnfoldingInfo`, which makes it true for a loop breaker with an INLINE pragma. `tryWW` in `GHC.Core.Opt.WorkWrap` does no worker/wrapper when `hasInlineUnfolding` is true. Backports of it are in 9.12.4 and 9.14.2-rc1, and 9.14.1 does not have it. I did not bisect. (CWW4) in Note [Cast worker/wrapper] accepts this cost for cast worker/wrapper: "an INLINE pragma on a genuninely-recursive function will kill worker-wrapper. Well, so be it." But the change also stops worker/wrapper for strictness and CPR (see Note [Don't w/w INLINE things]), and the example below shows that cost.

## Steps to reproduce

1. Save the program below as `Repro.hs`.
2. `ghc -O1 -rtsopts Repro.hs`
3. `./Repro plain 10000000 +RTS -s` and `./Repro inline 10000000 +RTS -s`
4. To see the Core, add `-fforce-recomp -ddump-simpl -dsuppress-all -dsuppress-uniques` to step 2.

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import System.Environment (getArgs)

sumCountPlain :: Int -> Int -> Int -> (Int, Int)
sumCountPlain !n !s !c =
  if n == 0 then (s, c) else sumCountPlain (n - 1) (s + n) (c + 1)

sumCountInline :: Int -> Int -> Int -> (Int, Int)
{-# INLINE sumCountInline #-}
sumCountInline !n !s !c =
  if n == 0 then (s, c) else sumCountInline (n - 1) (s + n) (c + 1)

main :: IO ()
main = do
  [which, nStr] <- getArgs
  let n = read nStr
      f = case which of
        "plain" -> sumCountPlain
        "inline" -> sumCountInline
        _ -> error "plain or inline"
  print (f n 0 0)
```

## Results

Bytes allocated and `perf stat -e instructions:u` for one run, n = 10^7, `-O1`:

| GHC | plain | inline |
|---|---|---|
| 9.6.7 | 59,528 B, 50.5 M | 59,552 B, 50.5 M |
| 9.10.3 | 59,192 B, 50.6 M | 59,216 B, 50.6 M |
| 9.12.4 | 59,200 B, 50.6 M | 480,059,248 B, 450.6 M |
| 9.14.1 | 59,096 B, 50.6 M | 59,120 B, 50.6 M |
| HEAD | 58,576 B, 50.7 M | 480,058,624 B, 450.7 M |

In 9.12.4 and HEAD, the Core has no worker for `sumCountInline`. Each recursive call boxes three new `I#` values, which is 48 bytes for each iteration:

```
sumCountInline
  = \ n s c ->
      case n of { I# ipv ->
      case s of s1 { I# ipv1 ->
      case c of c1 { I# ipv2 ->
      case ipv of wild {
        __DEFAULT ->
          sumCountInline
            (I# (-# wild 1#)) (I# (+# ipv1 wild)) (I# (+# ipv2 1#));
        0# -> (s1, c1)
      }
      }
      }
      }
```

In 9.6.7, 9.10.3 and 9.14.1, `$wsumCountInline` is the same as `$wsumCountPlain`: it loops on `Int#` and returns `(# ww1, ww2 #)`.

At `-O2`, 9.12.4 and HEAD do not allocate in this example, probably because SpecConstr specialises the loop. With `-O2 -fno-spec-constr`, HEAD allocates 480,058,624 bytes again.

## Expected behaviour

An INLINE pragma that GHC cannot use because the function is a loop breaker does not make the function slower, as in 9.14.1.

## Environment

- GHC HEAD at 10.1.20260918 (6913545fd3), GHC 9.14.1, 9.12.4, 9.10.3 and 9.6.7.
- x86-64 Linux; `perf` for the instruction counts.

/label ~"T::bug"

/label ~"regression"

/label ~"worker/wrapper transformation"

/label ~"needs triage"
