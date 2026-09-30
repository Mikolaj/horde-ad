# GHC issue: wrong direction in the `isAutoRule` check of `alreadyCovered`

Filed as GHC [#27873](https://gitlab.haskell.org/ghc/ghc/-/work_items/27873) on 2026-09-30; the text from "## Summary" down is the filed body, in the tracker's bug template. Title: **Specialise: wrong direction in the `isAutoRule` check of `alreadyCovered`, so an imported, more general auto rule blocks a specialisation**. Verified on 2026-09-29 on HEAD 10.1.20260925 (nightly bindist of commit `9f48a5b908`, and the same commit built with and without the fix), on 9.14.1, on 9.14.2-rc2 (bindist `9.14.1.20260916`) and on 9.12.2; re-verified on 2026-09-30, claim by claim, including with the fix for the sibling draft `docs/ghc-issue-cbv-dictionary-case.md` applied as well. Found while reducing GHC [#26895](https://gitlab.haskell.org/ghc/ghc/-/work_items/26895).

## Summary

When a library calls one of its own overloaded `INLINABLE [n]` functions at a partly known type, even once, client modules that call that function at fully known types get slower code. Their calls pass class dictionaries at run time instead of running a specialised copy. So adding one innocuous call inside the library slows its clients down; in horde-ad, a test runs 1.33x slower (#26895).

Up to 9.12, a less specific rule blocked a more specific specialisation on purpose, as Note [Specialisations already covered] said. ce616f4976 "Fix infelicities in the Specialiser" (9.14) set out to change this. It rewrote the Note as (SC2): "If the existing one is auto-generated, we generate a second RULE for the more specialised version. The latter is important because we don't want the accidental order of calls to determine what specialisations we generate." And it added an `isAutoRule` branch to `alreadyCovered` for this. ce616f4976 tried to change this behaviour but implemented the check backwards, so the old behaviour never actually changed. My fix completes what that commit intended.

In function `alreadyCovered`:

[Specialise.hs, lines 1799-1806](https://gitlab.haskell.org/ghc/ghc/-/blob/9f48a5b908f572847bc8ba4657c9f5a5d4284556/compiler/GHC/Core/Opt/Specialise.hs#L1799-1806):

```haskell
alreadyCovered env bndrs fn args is_active rules
  = case specLookupRule env fn args is_active rules of
      Nothing             -> False
      Just (rule, _)
        | isAutoRule rule -> -- Discard identical rules
                             -- We know that (fn args) is an instance of RULE
                             -- Check if RULE is an instance of (fn args)
                             ruleLhsIsMoreSpecific in_scope bndrs args rule
```

`specLookupRule` has already found that the call `(fn args)` is an instance of the existing `rule`. The branch must then check the other direction, whether `rule` is an instance of `(fn args)`, as its own comment says. But [`ruleLhsIsMoreSpecific in_scope bndrs1 args1 rule2`](https://gitlab.haskell.org/ghc/ghc/-/blob/9f48a5b908f572847bc8ba4657c9f5a5d4284556/compiler/GHC/Core/Rules.hs#L628-636) uses the LHS of `rule2` as the template and `args1` as the target. So it checks again that `(fn args)` is an instance of `rule`, and the result is always `True`. Thus an existing auto rule that is more general than a call always suppresses the more specific specialisation.

### Proposed fix

```diff
         | isAutoRule rule -> -- Discard identical rules
                              -- We know that (fn args) is an instance of RULE
                              -- Check if RULE is an instance of (fn args)
-                             ruleLhsIsMoreSpecific in_scope bndrs args rule
+                             rule_is_instance rule
         | otherwise       -> True  -- User rules dominate
   where
     in_scope = substInScopeSet (se_subst env)
+
+    rule_is_instance (Rule { ru_bndrs = rule_bndrs, ru_args = rule_args })
+      = isJust (matchExprs (ISE (in_scope `extendInScopeSetList` rule_bndrs)
+                                noUnfoldingFun)
+                           bndrs args rule_args)
+    rule_is_instance BuiltinRule{} = False
```

With the fix, the full testsuite passes on x86_64 Linux (flavour `default+no_profiled_libs+no_dynamic_libs`): 11381 tests, 0 unexpected failures, 0 framework failures. Against the same build without the fix, all 105 `compile_time/bytes allocated` metrics of `perf/compiler` change by less than 0.01%. The reproducer below can be the regression test: `Repro` must get a `SPEC/Repro interp` rule.

### Related

- #26895: a 2x slowdown from `INLINE [99]` on a recursive function. There, the Core diff shows the same pattern: an imported partial specialisation called with a constant dictionary, where `INLINE` gives a full specialisation. The fix takes the `INLINE [99]` test from 50.6 s to 38.0 s, against 26.9 s for `INLINE`, and does not change the `INLINEABLE` variants; thus this bug is only a part of #26895.
- #23050: a partial specialisation has no unfolding, so importers cannot specialise it further. That makes this bug cost more: when the specialiser skips the call, nothing specialises the result of the rule later.
- #23559: turning `-fpolymorphic-specialisation` on by default, which exposes this bug at plain `-O`.
- #26827: the original report, closed as subsumed by #26851, #26826 and #26895.

## Steps to reproduce

```haskell
{-# LANGUAGE AllowAmbiguousTypes #-}
module Lib where

class Tgt t where
  lit :: Int -> t
  add :: t -> t -> t

class KS s where
  ksVal :: Int

data Full
instance KS Full where
  ksVal = 1

data Expr = Lit Int | Add Expr Expr

interp :: forall t s. (Tgt t, KS s) => Expr -> t
{-# INLINABLE [1] interp #-}
interp (Lit n) = lit (n + ksVal @s)
interp (Add a b) = add (interp @t @s a) (interp @t @s b)

-- Makes the auto rule "SPEC interp @_ @Full" [1]
interpFull :: forall t. Tgt t => Expr -> t
interpFull = interp @t @Full
```

```haskell
module Repro where

import Lib

newtype D = D Int

instance Tgt D where
  lit = D
  add (D x) (D y) = D (x + y)

run :: Expr -> D
run = interp @D @Full
```

```
ghc -O -c Lib.hs
ghc -O -c Repro.hs -ddump-rules -ddump-simpl -dsuppress-all -dno-typeable-binds
```

`Repro` calls the imported `interp` at `@D @Full`, but gets no specialisation for that call. The cause is the more general auto rule that `Lib` exports (abridged from `ghc --show-iface Lib.hi`):

```
"SPEC interp @_ @Full" [1] forall @t ($dTgt :: Tgt t) ($dKS :: KS Full).
  interp @t @Full $dTgt $dKS = interpFull @t $dTgt
```

On HEAD, `-O` alone makes this rule, because 1fd259874d (#23559) switched `-fpolymorphic-specialisation` on by default; 9.14.1, 9.14.2-rc2 and 9.12.2 make it only with `-fpolymorphic-specialisation`. The call `interp @D @Full` in `Repro` is an instance of the rule, so `alreadyCovered` returns `True` and `Repro` gets no SPEC rule. The rule is not active yet when the specialiser runs in `Repro`, so it does not rewrite the call either. It fires later, in phase 1, and the dictionary stays:

```
run = interpFull $fTgtD
```

## Expected behavior

`Repro` gets `"SPEC/Repro interp @(*) @D @Full" [1]`, and `run` is specialised to `D`: a worker on `Int#`, with no dictionary. This is what the proposed fix gives, and also for `[0]` and `[99]`. If `interpFull` is removed from `Lib`, HEAD, 9.14.1 and 9.14.2-rc2 give it already. Without a phase, HEAD gives `run = interpFull $fTgtD` with and without the fix: that is #23050, because the rule fires before the specialiser runs.

### Workarounds

Each was tested on the reproducer with HEAD.

- A `SPECIALISE` pragma for the call types in the calling module, `{-# SPECIALISE interp @D @Full #-}`: user rules dominate.
- No more general auto rule: `-fno-specialise` or `-fno-polymorphic-specialisation` on `Lib`, or no call at a fixed `s` with an abstract `t` in `Lib`.
- `-fexpose-overloaded-unfoldings` on `Lib` together with `-flate-specialise` on `Repro`: the late specialiser specialises the result of the rule. The phase stays.
- `-fexpose-overloaded-unfoldings` on `Lib` and no phase, or `[~1]`: the rule fires before the specialiser, which then specialises its result (the workaround for #23050). This is not an option when the phase is necessary to let other RULEs fire first.

These have no effect: `-flate-specialise` alone, `-fexpose-overloaded-unfoldings` or `-fexpose-all-unfoldings` alone, `-fspecialise-aggressively`, `-fno-cross-module-specialise`.

## Environment

* GHC version used: HEAD 10.1.20260925 (commit 9f48a5b908) with `-O`; 9.14.1, 9.14.2-rc2 and 9.12.2 with `-O -fpolymorphic-specialisation`

Optional:

* Operating System: Ubuntu 24.04
* System Architecture: x86_64

/label ~"T::bug"
/label ~"needs triage"
