# GHC issue: under `-fworker-wrapper-cbv`, a worker evaluates its dictionary argument with `case`, and importers stop specialising what it calls

Draft, not filed yet; the text from "## Summary" down is the body to file, in the tracker's bug template. Title: **HEAD: with `-fworker-wrapper-cbv`, a worker evaluates its dictionary argument with `case`, and the specialisation of an imported function no longer cascades to the functions it calls**. Verified on 2026-09-29 on HEAD 10.1.20260925 (nightly bindist of commit `9f48a5b908`, and the same commit built from source), against 9.14.1 and 9.14.2-rc2 (bindist `9.14.1.20260916`), which are not affected, with a constraint-tuple version of the reproducer. On 2026-09-30 the history below was traced from `-dverbose-core2core` and the commits it names, without bisecting, and the reproducer, now with `Num t`, the workarounds and the proposed fix were verified on HEAD and 9.14.1. Found while reducing GHC [#26895](https://gitlab.haskell.org/ghc/ghc/-/work_items/26895), whose HEAD-only slowdown of `INLINEABLE` it causes; it is separate from GHC [#27873](https://gitlab.haskell.org/ghc/ghc/-/work_items/27873), filed from `docs/ghc-issue-already-covered-direction.md`.

## Summary

In the reproducer below, `Repro` specialises the imported `f` at `Double`, but not the imported `g` that `f` calls: the specialised `f` calls `g`'s worker with the constant dictionary `$fNumDouble`. This happens only when `Lib` is compiled with `-fworker-wrapper-cbv`, and only on HEAD: 9.14.1 with the same flag specialises both functions. Any class constraint does it: `Num t` as here, a constraint tuple, a class with superclasses, and a unary class.

Worker/wrapper used to unbox tuple dictionaries, which put a `case` on a dictionary into the worker (#23398), and since 2010 `specCase` had a special case so that such a `case` did not stop specialisation. Then wrinkle (DNB1) of [Note [Do not unbox class dictionaries]](https://gitlab.haskell.org/ghc/ghc/-/blob/9f48a5b908f572847bc8ba4657c9f5a5d4284556/compiler/GHC/Core/Opt/WorkWrap/Utils.hs#L727-741) stopped the unboxing, so that GHC does superclass selection "with superclass selectors, never with `case` expressions". On that premise, be7296c909 "Remove complex special case from the type-class specialiser" (!14272) removed the special case: its [Historical Note [Floating dictionaries out of cases]](https://gitlab.haskell.org/ghc/ghc/-/blob/9f48a5b908f572847bc8ba4657c9f5a5d4284556/compiler/GHC/Core/Opt/Specialise.hs#L1380-1399) says "We never explicitly case-analyse a dictionary". But c56567ec "Add evals for strict data-con args in worker-functions" (#26722) broke the premise again. A CBV worker now evaluates each strict argument even when its body already uses it strictly, and that includes a dictionary: `case $dNum of $dNum1 { __DEFAULT -> ... }`. The simplifier then refines that `DEFAULT` alternative to the single constructor of the dictionary type, in `refineDefaultAlt`, except for unary classes since 05094993 (#27071). So with `-fworker-wrapper-cbv`, the worker of `f` takes its `Num` dictionary apart with `case` and passes the case binder on:

```
$wf = \ @t $dNum ds ->
      case $dNum of $dNum1 { C:Num ipv ipv1 ipv2 ipv3 ipv4 ipv5 ipv6 ->
      case ds of {
        ...
        B e -> $wg $dNum1 e
      } }
```

9.14.1 with the same flag gives the same worker without the `case`: it calls `+ $dNum` and passes `$dNum` on. Before c56567ec, `wantCbvForId` skipped the eval for a strictly demanded argument (`not (isStrictDmd dmd) || cbv_for_strict`), and the dictionary here is strictly demanded. None of be7296c909, c56567ec and 05094993 is in 9.14.1 or 9.14.2-rc2.

In function `specCase`:

[Specialise.hs, lines 1296-1317](https://gitlab.haskell.org/ghc/ghc/-/blob/9f48a5b908f572847bc8ba4657c9f5a5d4284556/compiler/GHC/Core/Opt/Specialise.hs#L1296-1317):

```haskell
specCase :: SpecEnv
         -> OutExpr             -- Scrutinee, already done
         -> InId -> [InAlt]
         -> SpecM ( OutExpr     -- New scrutinee
                  , OutId
                  , [OutAlt]
                  , UsageDetails)
-- We used to have a complex special case for
--    case d of { CTuple2 d1 d2 -> blah }
-- but we no longer do so.
-- See Historical Note [Floating dictionaries out of cases]
specCase env scrut case_bndr alts
  = do { (alts', uds_alts) <- mapAndCombineSM spec_alt alts
       ; return (scrut, case_bndr', alts', uds_alts) }
  where
    (env_alt, case_bndr') = substBndr env case_bndr
    spec_alt (Alt con args rhs)
      = do { (rhs', uds) <- specExpr env_rhs rhs
           ; let (free_uds, dumped_dbs) = dumpUDs (case_bndr' : args') uds
           ; return (Alt con args' (wrapDictBindsE dumped_dbs rhs'), free_uds) }
        where
          (env_rhs, args') = substBndrs env_alt args
```

When `Repro` specialises `$wf` at `Double`, the scrutinee becomes the constant dictionary, but the case binder `$dNum1` gets nothing from it: it is a variable with no unfolding. So `interestingDict` does not see the argument of `$wg $dNum1 e` as a dictionary it can specialise on, and the call stays. The removed special case gave the case binder the scrutinee as its dictionary unfolding, and the specialisation continued into `$wg`. Thus either the CBV worker must not evaluate the dictionary with `case`, or `specCase` must handle a `case` on a dictionary again. The refinement to a constructor is not what breaks it: for a unary class the eval stays `case $dU of $dU1 { __DEFAULT -> ... }`, and the calls pass `$dU1` all the same.

### Proposed fix

Add no eval for a dictionary argument, as before c56567ec, in [`mkStrictFieldSeqs`](https://gitlab.haskell.org/ghc/ghc/-/blob/9f48a5b908f572847bc8ba4657c9f5a5d4284556/compiler/GHC/Core/Utils.hs#L3341-3355):

```diff
         | isMarkedStrict arg_cbv
         , wantCbvForId arg_id
+        -- No eval on a dictionary: it would become a case that takes the
+        -- dictionary apart. See (DNB1) in Note [Do not unbox class dictionaries]
+        , not (isDictId arg_id)
```

With it, `Repro` specialises both functions, for each of the four kinds of constraint above, and the exported unfolding of `$wf` has no `case` on the dictionary. The GHC testsuite has not been run with it yet.

On horde-ad's test from #26895 with plain `INLINEABLE` (HEAD with the fix of #27873; times are medians of three interleaved runs), the fix restores the allocation of a build without the flag exactly, and keeps the speed that the flag buys:

| horde-ad compiled | allocated | time |
|---|---|---|
| with `-fworker-wrapper-cbv` and the fix | 70.8 GB | 34.8 s |
| with `-fworker-wrapper-cbv`, without the fix | 79.0 GB | 60.1 s |
| without `-fworker-wrapper-cbv` | 70.8 GB | 46.5 s |

### Related

- #26895: on HEAD, plain `INLINEABLE` on horde-ad's recursive `interpretAst` is as slow as the phase-annotated variants. There, the specialisation of `interpretAst` at the target type stops after one of its per-span copies for this reason; the table above shows what the fix does to it.
- #27873: the other bug behind #26895, a wrong direction in the specialiser's `alreadyCovered`; the measurements above include its fix.
- !14272, #26158, #19747: the removal of the dictionary-case special case, and why.
- #26722: the eval on strict worker arguments; #27071: why `refineDefaultAlt` skips unary classes.

## Steps to reproduce

```haskell
module Lib where

data E = L Int | A E E | B E

f :: Num t => E -> t
{-# INLINABLE f #-}
f (L n) = fromIntegral n
f (A a b) = f a + f b
f (B e) = g e

g :: Num t => E -> t
{-# INLINABLE g #-}
g (L n) = fromIntegral (n + 1)
g (A a b) = g a * g b
g (B e) = f e
```

```haskell
module Repro where

import Lib

run :: E -> Double
run = f
```

```
ghc -O -fworker-wrapper-cbv -c Lib.hs
ghc -O -c Repro.hs -ddump-simpl -dsuppress-all -dno-typeable-binds
```

On HEAD, `Repro` specialises `f`, but not `g`:

```
$s$wf = ... B e -> $wg $fNumDouble e ...
run = $s$wf
```

## Expected behavior

`Repro` specialises both `f` and `g` at `Double`, as 9.14.1 does with the same flags, and HEAD with the proposed fix:

```
$w$s$wg = ... B e -> $w$s$wf e ...
$w$s$wf = ... B e -> $w$s$wg e ...
```

HEAD also does this when `Lib` is compiled without `-fworker-wrapper-cbv`.

### Workarounds

Each was tested on the reproducer with HEAD.

- Compile the defining module without `-fworker-wrapper-cbv`.
- A `SPECIALISE` pragma in the importing module for the function that is not specialised: `{-# SPECIALISE g :: E -> Double #-}`.
- `-flate-specialise` on the importing module.

Changing the constraint does not help: a constraint tuple, a class with superclasses and a unary class are all affected.

These have no effect: `-fspecialise-aggressively` on the importing module, `-fexpose-all-unfoldings` on `Lib`. `-fworker-wrapper-cbv` on the importing module only does no harm.

## Environment

* GHC version used: HEAD 10.1.20260925 (commit 9f48a5b908); not 9.14.1, not 9.14.2-rc2

Optional:

* Operating System: Ubuntu 24.04
* System Architecture: x86_64

/label ~"T::bug"
/label ~"needs triage"
