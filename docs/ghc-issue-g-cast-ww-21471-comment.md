# GHC issue comment: under `-g1`, cast worker/wrapper keeps a cast that a source note covers, and the CSE half also occurs on 9.12.4 and 9.14.1

Posted 2026-10-18 as a comment on GHC [#21471](https://gitlab.haskell.org/ghc/ghc/-/work_items/21471) ("Source notes impact compilation results as evident by -dannot-lint failures when running GHC testsuite"), after the comment that `docs/ghc-issue-g-changes-core-21471-comment.md` records; this file stays as the record of the comment, the text from "Two additions" down being the body as posted. Verified on 2026-10-18 with GHC HEAD 10.1.20260918 (`wip/T27737` at 6913545fd3 on master e2d5702699, with uncommitted patches in five files) and ghc-9.14.1 and 9.12.4; both points show on 9.12.4, so they do not depend on those patches. The issue's description and all its notes were read on 2026-10-18; the last note before this one was that comment, posted on 2026-10-17. The test log linked from the description has Simplifier warnings for T15970 and str-rules, neither about a cast. Point 1 is the third repro of A31 in `docs/inlining-catalogue.md` (`~/r/horde-ad/dist-inlcat/cases/A31-cast-under-note`). Point 2 corrects the comment's sentence "On 9.14.1 and 9.12.4, `-g1` does not give a second literal", which is true of its own module (checked again on 2026-10-18) and not of orthotope's DynamicTest, whose count in point 2 is at orthotope e1a7194. Code checked at master f93d523c (2026-10-15); the cited lines are the same in the HEAD build. The prose is ASD-STE100 Simplified Technical English. Stated as open: why the desugarer of 9.14.1 puts the note inside the cast, and why the comment's module keeps one literal on 9.12.4 and 9.14.1 where the module below does not.

Two additions to my comment above, each with a small module. Both occur on HEAD (10.1.20260918) and 9.12.4.

1. With `-g1`, cast worker/wrapper does not split a binding whose source note is above the cast. In this module:

```haskell
module N (N (..), n1, ns) where

-- A newtype, so that N's constructor is a cast.
newtype N = N Int

{-# NOINLINE f #-}
f :: Int -> Int
f x = x * x + 1

-- A right-hand side `f 3 |> co`: a saturated call, so not eta-expanded.
n1 :: N
n1 = N (f 3)

ns :: [N]
ns = [n1, n1]
```

With `ghc -O -c -ddump-simpl -dsuppress-all -dsuppress-uniques -dno-suppress-ticks N.hs`, cast worker/wrapper splits `n1`, and `ns` uses the worker `n2`:

```
n2 = case $wf 3# of ww { __DEFAULT -> I# ww }

n1 = n2 `cast` <Co:2>

ns1 = : (n2 `cast` <Co:2>) []

ns = : (n2 `cast` <Co:2>) ns1
```

With `-g1` added, `n1` keeps the cast under its source note, and `ns` uses `n1` (here and below, I replaced the spans of the source notes by `...`):

```
n1
  = src<...>
    case $wf 3# of ww { __DEFAULT -> (I# ww) `cast` <Co:2> }
```

```
ns = src<...> : (src<...> n1) ns1
```

`tryCastWorkerWrapper` splits a binding only when its right-hand side is a `Cast` ([Iteration.hs, line 617][tcww]). Any other right-hand side, a cast under a source note included, goes to the equation for "All other bindings" ([line 685][tcww-no]). `ghc -O -c -g1 -ddump-simpl-trace -dsuppress-uniques -dsuppress-module-prefixes N.hs` records `n1` there, `tcww:no` with ``rhs: src<...> (f (src<...> I# 3#)) `cast` (Sym N:N :: Int ~R# N)``. With `-g1 -dannot-lint`, HEAD and 9.12.4 print five warnings in result of the Simplifier, and 9.14.1 none. The first starts:

```
*** Core Lint warning : in result of Simplifier ***
Core changes with annotations:
  f (src<...> I# 3#) /= n1_sC7
    (in binding n1)
  n1 /= n1_sC7 `cast` (Sym N:N :: Int ~R# N)
    (in binding ns)
```

9.14.1 splits `n1` with `-g1` too. Its desugarer output (`-ddump-ds` in place of `-ddump-simpl-trace`) has the source note inside the cast, ``(src<...> f (src<...> I# 3#)) `cast` (Sym N:N :: Int ~R# N)``, where HEAD and 9.12.4 have it outside.

2. A correction. I wrote: "On 9.14.1 and 9.12.4, `-g1` does not give a second literal". That is true of the module in my comment, but not in general. In this module, `-g1` keeps copies of the call-stack literals apart on HEAD, 9.14.1 and 9.12.4:

```haskell
module L (t) where

import GHC.Stack (HasCallStack, callStack, prettyCallStack)

{-# NOINLINE check #-}
check :: HasCallStack => String -> Int -> Int -> IO ()
check name x y =
  if x == y then pure () else error (name ++ prettyCallStack callStack)

t :: [IO ()]
t =
  let c1 = check "1" 1 (length "a")
      c2 = check "2" 2 (length "ab")
  in [c1, c2]
```

With `ghc -O -c -ddump-simpl -dsuppress-all -dsuppress-uniques L.hs`, the final Core binds each of `"main"#`, `"L"#`, `"L.hs"#` and `"check"#` one time. With `-g1` added, it binds each of `"main"#`, `"L"#` and `"L.hs"#` three times, under the source notes of `check` (for its call of `error`), of `c1` and of `c2`, and `"check"#` two times, under those of `c1` and `c2`. With `-dno-suppress-ticks` also added, the three bindings of `"main"#` on HEAD are these, under the notes of `check`, of `t` and `c1`, and of `t` and `c2`:

```
lvl2 = src<...> "main"#
t28 = src<...> src<...> "main"#
t12 = src<...> src<...> "main"#
```

With `-g1 -dannot-lint`, GHC prints a warning in result of Common sub-expression on all three versions. HEAD and 9.12.4 also print a warning in result of the Simplifier, for a cast in `t`. I found this in a test module of the orthotope library, which has many `HasCallStack` assertions: with `-g1`, 9.12.4 and 9.14.1 bind the literal `"DynamicTest"#` 82 times, and one time without `-g1`.

I did not measure a run-time cost of either change.

[tcww]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L617
[tcww-no]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L685
