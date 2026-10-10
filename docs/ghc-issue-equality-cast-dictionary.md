# GHC issue: the specialiser does not specialise on equality evidence, so a call whose dictionary is cast with an equality given stays overloaded

Filed as GHC [#27920](https://gitlab.haskell.org/ghc/ghc/-/work_items/27920) on 2026-10-10; the text from "## Summary" down is the filed body, in the tracker's bug template. Title: **Specialiser: a dictionary cast with an equality given is not specialised on, so the specialisation of a function with `a ~ b` leaves its callees overloaded**. Verified on 2026-10-10 on HEAD 10.1.20260918 (checkout 6913545fd3) and on 9.14.1, 9.12.4, 9.10.3, 9.8.4 and 9.6.7. The source links pin `origin/master` at 5236634abc, whose cited files are identical to the checkout's. Found in orthotope's `Convert` instances on the review branch `pr-mikolaj-toVectorListT`, where `INLINE` on `fromStorable` works around it. It gives the reproducer that GHC [#14941](https://gitlab.haskell.org/ghc/ghc/-/work_items/14941) asked for in 2018, and it answers the open question at the end of GHC [#23798](https://gitlab.haskell.org/ghc/ghc/-/work_items/23798); the comments posted there on 2026-10-10 to point here are recorded in `docs/ghc-issue-equality-cast-dictionary-14941-comment.md` and `docs/ghc-issue-equality-cast-dictionary-23798-comment.md`. The prose is ASD-STE100 Simplified Technical English.

## Summary

In the reproducer below, `Repro` specialises the imported `outer` at `Double`, but not the imported `sumTo` that `outer` calls. The specialisation of `outer` calls the worker of `sumTo` with the dictionary `$fNumDouble`. The cause is the equality constraint `t ~ u` in the type of `outer`. Without it (`outer :: Num t => [Int] -> t -> t`), `Repro` specialises both functions. GHC 9.6.7, 9.8.4, 9.10.3, 9.12.4, 9.14.1 and HEAD all do the same.

`outer` calls `sumTo` at `u`. Thus the dictionary of that call is the `Num t` dictionary, cast with the coercion from the given `t ~ u`. The specialiser does not specialise on the equality evidence, thus the specialisation of `outer` keeps the evidence as a parameter, and the cast dictionary refers to that parameter. The output of the specialiser on HEAD, before the simplifier runs on it, shows this (`ghc -O -c Repro.hs -ddump-spec -dsuppress-idinfo -dsuppress-uniques -dsuppress-module-prefixes`, after the steps below):

```
$s$wouter :: (Double ~# Double) => [Int] -> Double -> Double
$s$wouter
  = \ (ww :: Double ~# Double) (eta :: [Int]) (eta1 :: Double) ->
      ...
          $wsumTo
            @Double
            ($fNumDouble `cast` ((Num ww)_R :: Num Double ~R# Num Double))
            ...
```

The dictionary argument of `$wsumTo` refers to `ww`. Thus the call cannot float out of `$s$wouter` to a specialisation of `$wsumTo`. Later, the simplifier removes the reflexive cast, but the specialiser does not run again. The wrapper `$souter :: (Double ~ Double) => [Int] -> Double -> Double` keeps the boxed evidence as a parameter in the same way.

The specialiser does not specialise on the evidence because, in [`mkCallUDs'`](https://gitlab.haskell.org/ghc/ghc/-/blob/5236634abce50db7e8e7ecf375def90bf45d2476/compiler/GHC/Core/Opt/Specialise.hs#L3100-3106), an evidence argument gets a `SpecDict` only if `interestingDict` accepts it, and an `UnspecArg` otherwise.

For the boxed evidence `Eq# co`, [`interestingDict`](https://gitlab.haskell.org/ghc/ghc/-/blob/5236634abce50db7e8e7ecf375def90bf45d2476/compiler/GHC/Core/Opt/Specialise.hs#L3151-3159) finds the class `(~)`, which has no methods. Thus (ID6) applies, and `interestingDict` examines the arguments of the constructor. The only argument is the coercion `co`, and `exprIsTrivial` is true for a coercion. Thus the result is `UnspecArg`. The unboxed evidence `ww` of the worker is a coercion argument, and it gets `UnspecArg` for the same reason.

This agrees with the diagnosis in #14941, in the comment of 2018-07-05: "Now, we can't float that call up to the definition of `f` because it mentions `g`. But we could in principle specialise `f` for `Num Int`, and then use that specialised version at the call." That comment asks for an example "that a specialisation is created and used without the equality, but not with". The reproducer below is such an example.

### Motivation

The constraint `a ~ b` in an instance context is a common idiom: instance resolution selects the instance before it knows that the two types are equal, and type inference then gets the equality from the instance. The `Convert` class of orthotope uses this idiom for its conversions between boxed and unboxed arrays, for example `instance (a ~ b, DS.Unbox a) => Convert (DS.Array a) (D.Array b)`. This conversion calls the overloaded function `fromStorable` at `b`, with the `Storable a` dictionary cast with the coercion from `a ~ b`. When `fromStorable` is INLINABLE, a client on HEAD that converts a dense array of 200000 `Double` values and sums the result runs 3.45 times the instructions that it runs when `fromStorable` is `INLINE`.

### Related

- #14941: the original report (2018), with the diagnosis above. Its later comments are about a different effect: a `NOINLINE` function with `a ~ Int` and worker/wrapper.
- #23798: a `SPECIALISE` pragma with an equality constraint fails to desugar. Its last comment reports the expectation that equality constraints do not affect the automatic specialisation. This issue shows a case where they do.

## Steps to reproduce

```haskell
{-# LANGUAGE TypeFamilies #-}
module Lib where

sumTo :: Num t => Int -> t -> t
{-# INLINABLE sumTo #-}
sumTo 0 acc = acc
sumTo n acc = sumTo (n - 1) (acc + fromIntegral n)

outer :: (t ~ u, Num t) => [Int] -> t -> u
{-# INLINABLE outer #-}
outer [] acc = acc
outer (n : ns) acc = sumTo n (outer ns acc)
```

```haskell
module Repro where

import Lib

run :: [Int] -> Double -> Double
run = outer
```

```
ghc -O -c Lib.hs
ghc -O -c Repro.hs -ddump-simpl -dsuppress-all -dno-typeable-binds
```

On HEAD, the final Core of `Repro` specialises `outer`, but not `sumTo`. The cast is gone, but the call still passes `$fNumDouble`:

```
Rec {
$s$wouter
  = \ ww_aAS eta_aAU eta1_aAV ->
      case eta_aAU of {
        [] -> eta1_aAV;
        : n_aAY ns_aAZ ->
          case n_aAY of { I# ww1_aB3 ->
          $wsumTo $fNumDouble ww1_aB3 ($s$wouter @~<Co:1> ns_aAZ eta1_aAV)
          }
      }
end Rec }

run = \ eta_aAF eta1_aAG -> $s$wouter @~<Co:1> eta_aAF eta1_aAG
```

## Expected behavior

`Repro` specialises both `outer` and `sumTo` at `Double`, as it does when `outer` has no equality constraint (`outer :: Num t => [Int] -> t -> t`). Then the final Core has `$w$s$wsumTo`, a loop on `Int#` and `Double#`, and no call in it passes a dictionary.

### Workarounds

Each was tested on the reproducer with HEAD, 9.14.1 and 9.6.7.

- `-flate-specialise` on the importing module.
- A `SPECIALISE` pragma in the importing module for the callee: `{-# SPECIALISE sumTo :: Int -> Double -> Double #-}`.

`INLINE` on the callee also helps, if the callee is not recursive. This was tested on HEAD with orthotope's `fromStorable`.

A call of the callee at the type of the given dictionary also helps, because then the dictionary is not cast. In the reproducer, write `outer :: forall t u. (t ~ u, Num t) => [Int] -> t -> u` and `sumTo @t n (outer ns acc)`, with `ScopedTypeVariables` and `TypeApplications`. This was tested on 9.6.7, 9.8.4, 9.10.3, 9.12.4, 9.14.1 and HEAD. In orthotope, this (`fromStorable @a`) is as fast as `INLINE`, but the Core of the importing module is 29% larger.

These have no effect on HEAD: `-fspecialise-aggressively` on the importing module, and `-fexpose-all-unfoldings` on `Lib`. A `SPECIALISE` pragma for `outer` (`{-# SPECIALISE outer :: [Int] -> Double -> Double #-}`) helps on 9.6.7, but not on 9.8.4, 9.10.3, 9.12.4, 9.14.1 or HEAD.

## Environment

* GHC version used: HEAD 10.1.20260918 (commit 6913545fd3), 9.14.1, 9.12.4, 9.10.3, 9.8.4, 9.6.7

Optional:

* Operating System: Ubuntu 24.04
* System Architecture: x86_64

/label ~"T::bug"
/label ~"needs triage"
