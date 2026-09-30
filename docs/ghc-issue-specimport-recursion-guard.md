# GHC issue: specImport's recursion guard refuses a less specialised recursive call, so a phase on a recursive `INLINABLE` function leaves its recursion overloaded

Filed as GHC [#27880](https://gitlab.haskell.org/ghc/ghc/-/work_items/27880) on 2026-09-30; the text from "## Summary" down is the filed body, in the tracker's bug template. Title: **Specialise: the specImport recursion guard also stops recursive calls that are strictly less specialised, so the specialisation of a recursive function over a GADT with existential dictionaries calls the overloaded function; a phase on its `INLINABLE` pragma exposes this**. Verified on 2026-09-30 on HEAD 10.1.20260925 (commit `9f48a5b908`) built from source with the fixes of GHC [#27873](https://gitlab.haskell.org/ghc/ghc/-/work_items/27873) and GHC [#27874](https://gitlab.haskell.org/ghc/ghc/-/work_items/27874), on the nightly bindist of the same commit, and on 9.14.1 and 9.12.2. This is the remaining cause of the phase-annotated slowdown of GHC [#26827](https://gitlab.haskell.org/ghc/ghc/-/work_items/26827) in horde-ad, after the two bugs found in GHC [#26895](https://gitlab.haskell.org/ghc/ghc/-/work_items/26895). The proposed fix was run through the full testsuite and the `perf/compiler` metrics on 2026-09-30.

## Summary

Adding a phase to the `INLINABLE` pragma of a recursive function makes its specialised callers slower: in the reproducer below, `INLINABLE [1]` instead of `INLINABLE` makes the program allocate 5x more and run twice as slow, because the specialised recursion calls the overloaded function with dictionaries at run time. The phase is needed for phase control: without it, a RULE that mentions the function may never fire, as `-Winline-rule-shadowing` warns.

When `Repro` specialises the imported recursive `interp` at `D` and `Full`, the specialised copy still calls the overloaded `interp` for the recursive call under the constructor `Sub`, which binds another span `s2` and its dictionary:

```
Sub @s2 $dKS e1 -> interp $fTgtD $dKS e1
```

The call `interp @D @s2 $fTgtD $dKS` could be specialised at `@D @_`, since `$fTgtD` is a constant dictionary. But `specImport` never tries: `interp` is on its call stack, and [Note [Avoiding recursive specialisation]](https://gitlab.haskell.org/ghc/ghc/-/blob/9f48a5b908f572847bc8ba4657c9f5a5d4284556/compiler/GHC/Core/Opt/Specialise.hs#L1155-1163) stops every recursive call. The Note's reason is a recursive call that is "yet-more-specialised", which could diverge. This call is less specialised, so it cannot.

On HEAD this shows as a cost of a phase. Without a phase on `interp`, the auto rule `"SPEC interp @_ @Full"` from `Lib`, active from the start, rewrites the call in `Repro` to `Lib`'s own specialisation `interp_$sinterp` before the specialiser runs. `interp` is then not on the stack when its recursive call is met, and `Repro` gets `"SPEC/Main interp @D @_"`. With `INLINABLE [1]`, the rule is inactive when the specialiser runs, the recursion guard stops the call, and the program allocates 5x more. On 9.14.1 and 9.12.2, where `-fpolymorphic-specialisation` is off by default, `Lib` makes no such rule and the guard stops the call with and without a phase.

### Proposed fix

Let `specImport` specialise a call of a function on its stack if the call is strictly more general than every call of that function being specialised: it specialises strictly fewer arguments, and those it specialises at the same types. Each such step specialises fewer arguments, so it cannot diverge. A type argument that is a type variable, such as `s2`, counts as not specialised, because the specialisation quantifies over it. The patch keeps the call keys on the stack:

```diff
--- a/compiler/GHC/Core/Opt/Specialise.hs
+++ b/compiler/GHC/Core/Opt/Specialise.hs
@@ -34,6 +34,7 @@
                           , stripTicksTop, mkInScopeSetBndrs )
 import GHC.Core.FVs
 import GHC.Core.TyCo.FVs
+import GHC.Core.TyCo.Compare ( eqType )
 import GHC.Core.Opt.Arity( collectBindersPushingCo )
 import GHC.Core.Opt.Monad
 import GHC.Core.Opt.Simplify.Env ( SimplPhase(..), isActive )
@@ -793,7 +794,8 @@
 -- | Specialise a set of calls to imported bindings
 spec_imports :: SpecEnv          -- Passed in so that all top-level Ids are in scope
                                  ---In-scope set includes the FloatedDictBinds
-             -> [Id]             -- Stack of imported functions being specialised
+             -> [(Id, [[SpecArg]])]  -- Stack of imported functions being specialised,
+                                     -- with the call keys they were specialised at
                                  -- See Note [specImport call stack]
              -> FloatedDictBinds -- Dict bindings, used /only/ for filterCalls
                                  -- See Note [Avoiding loops in specImports]
@@ -826,7 +828,7 @@
 
 spec_import :: SpecEnv               -- Passed in so that all top-level Ids are in scope
                                      ---In-scope set includes the FloatedDictBinds
-            -> [Id]                  -- Stack of imported functions being specialised
+            -> [(Id, [[SpecArg]])]   -- Stack of imported functions being specialised
                                      -- See Note [specImport call stack]
             -> FloatedDictBinds      -- Dict bindings, used /only/ for filterCalls
                                      -- See Note [Avoiding loops in specImports]
@@ -835,15 +837,6 @@
                      , [CoreRule]    -- New rules
                      , [CoreBind] )  -- Specialised bindings
 spec_import env callers dict_binds cis@(CIS fn _)
-  | isIn "specImport" fn callers
-  = do {
---         debugTraceMsg (text "specImport1-bad" <+> (ppr fn $$ text "callers" <+> ppr callers))
-       ; return (env, [], []) }
-    -- No warning.  This actually happens all the time
-    -- when specialising a recursive function, because
-    -- the RHS of the specialised function contains a recursive
-    -- call to the original function
-
   | null good_calls
   = do {
 --        debugTraceMsg (text "specImport1-no-good" <+> (ppr cis $$ text "dict_binds" <+> ppr dict_binds))
@@ -886,7 +879,7 @@
 --           , text "new_calls" <+> ppr new_calls ])
 
        ; (env, rules2, spec_binds2)
-            <- spec_imports new_env (fn:callers)
+            <- spec_imports new_env ((fn, map ci_key good_calls) : callers)
                                     (dict_binds `thenFDBs` dict_binds1)
                                     new_calls
 
@@ -899,15 +892,49 @@
   = do {
 --         debugTraceMsg (hang (text "specImport1-missed")
 --                          2 (vcat [ppr cis, text "can-spec" <+> ppr (canSpecImport dflags fn)]))
-       ; tryWarnMissingSpecs dflags callers fn good_calls
+       ; tryWarnMissingSpecs dflags (map fst callers) fn good_calls
        ; return (env, [], [])}
 
   where
     dflags = se_dflags env
-    good_calls = filterCalls cis dict_binds
+    good_calls = filter not_on_stack (filterCalls cis dict_binds)
        -- SUPER IMPORTANT!  Drop calls that (directly or indirectly) refer to fn
        -- See Note [Avoiding loops in specImports]
 
+    -- See Note [Avoiding recursive specialisation]: a call of a function
+    -- that is on the stack is specialised only if it is strictly more
+    -- general than every call of that function being specialised.
+    -- No warning when a call is dropped: this happens all the time when
+    -- specialising a recursive function, because the RHS of the
+    -- specialised function contains a recursive call to the original one.
+    stack_keys = [ key | (caller, keys) <- callers, caller == fn, key <- keys ]
+    not_on_stack ci = all (ci_key ci `strictlyMoreGeneral`) stack_keys
+
+-- | @new `strictlyMoreGeneral` old@: every argument that @new@ specialises,
+-- @old@ specialises too (at the same type), and @old@ specialises at least one
+-- more.  So @new@ specialises strictly fewer arguments, which bounds how often
+-- a function on the specImport stack can be specialised again.
+strictlyMoreGeneral :: [SpecArg] -> [SpecArg] -> Bool
+strictlyMoreGeneral = go False
+  where
+    go more (n:ns) (o:os)
+      | is_spec n, is_spec o = same n o && go more ns os
+      | is_spec n            = False
+      | is_spec o            = go True ns os
+      | otherwise            = go more ns os
+    go more ns [] = more && not (any is_spec ns)
+    go more [] os = more || any is_spec os
+
+    same (SpecType t1) (SpecType t2) = t1 `eqType` t2
+    same (SpecDict {}) (SpecDict {}) = True  -- determined by the types
+    same _             _             = False
+
+    -- A type variable, e.g. one bound by a pattern match, is generalised
+    -- over in the specialisation, so it specialises nothing
+    is_spec (SpecType ty) = not (isTyVarTy ty)
+    is_spec (SpecDict {}) = True
+    is_spec _             = False
+
 canSpecImport :: DynFlags -> Id -> Maybe CoreExpr
 canSpecImport dflags fn
   | isDataConWrapId fn
@@ -1162,6 +1189,14 @@
 Avoiding this recursive specialisation loop is one reason for the
 'callers' stack passed to specImports and specImport.
 
+A recursive call that is strictly /less/ specialised is different: e.g.
+    f :: forall t s. (C t, D s) => T s -> t
+where the specialisation of `f @Int @A` meets a call `f @Int @s` at a
+type `s` bound by a pattern match, with a dictionary that is not
+interesting.  Specialising that call at `@Int @_` cannot diverge, since
+each such step specialises strictly fewer arguments, and without it the
+recursion runs the fully overloaded `f`.  See `strictlyMoreGeneral`.
+
 
 ************************************************************************
 *                                                                      *
```

With the fix, on top of those of #27873 and #27874, the full testsuite passes on x86_64 Linux (flavour `default+no_profiled_libs+no_dynamic_libs`) apart from 25 tests of the `optllvm` way, which could not run because LLVM was not installed: 11777 expected passes, the same tests that pass without the fix except those 25. Against the same build without it, all 101 `compile_time/bytes allocated` metrics of `perf/compiler` change by less than 0.015%. `Repro` gets `"SPEC/Main interp @D @_" [1]`, and the phase costs nothing:

| compiler | no phase | `INLINABLE [1]` |
|---|---|---|
| 9.12.2 | 39.7 MB | 39.7 MB |
| 9.14.1 | 39.7 MB | 39.7 MB |
| HEAD with the fixes of #27873 and #27874 | 7.3 MB | 36.8 MB |
| the same with the proposed fix | 7.3 MB | 7.3 MB |

On horde-ad's test from #26895 (`INLINEABLE [1]` on the recursive interpreter, 3 interleaved runs each), the fix removes the cost of the phase: 46.1 s without it, 31.5 s with it, against 31.8 s without a phase. The build of the test suite takes 1054 s instead of 984 s.

### Related

- #26827: the slowdown of phase-annotated pragmas on horde-ad's interpreter; this is its remaining cause.
- #26895, #27873, #27874: the two bugs that hid it on HEAD.
- #23559: `-fpolymorphic-specialisation` on by default, which makes the auto rule that avoids the guard without a phase.

## Steps to reproduce

```haskell
{-# LANGUAGE GADTs, AllowAmbiguousTypes, ScopedTypeVariables, TypeApplications #-}
module Lib where

class Tgt t where
  lit :: Int -> t
  add :: t -> t -> t

class KS s where
  ksVal :: Int

data Full
data Dual
instance KS Full where ksVal = 1
instance KS Dual where ksVal = 2

data Expr s where
  Lit :: Int -> Expr s
  Add :: Expr s -> Expr s -> Expr s
  Sub :: KS s2 => Expr s2 -> Expr s   -- span bound by the constructor
  Prim :: Expr Full -> Expr Dual      -- span fixed by the constructor

interp :: forall t s. (Tgt t, KS s) => Expr s -> t
{-# INLINABLE [1] interp #-}
interp (Lit n) = lit (n + ksVal @s)
interp (Add a b) = add (interp a) (interp b)
interp (Sub e) = interp e
interp (Prim e) = interp e
```

```haskell
import Lib

newtype D = D Int
instance Tgt D where
  lit = D
  add (D a) (D b) = D (a + b)

mk :: Int -> Expr Full
mk 0 = Lit 1
mk n = Add (Sub (mk' (n - 1))) (mk (n - 1))
  where mk' :: Int -> Expr Dual
        mk' 0 = Lit 2
        mk' k = Add (Prim (mk (k - 1))) (Lit k)

run :: Expr Full -> D
run = interp

main :: IO ()
main = do
  let e = mk 22
  mapM_ (\i -> let D r = run (Add e (Lit i)) in print r) [1 .. 3]
```

Save the modules as `Lib.hs` and `Repro.hs`, and compile with horde-ad's specialisation flags:

```
F="-O -fexpose-overloaded-unfoldings -fspecialise-aggressively -fdicts-cheap -fkeep-auto-rules"
ghc $F -c Lib.hs
ghc $F -c Repro.hs -ddump-simpl -dsuppress-all -dsuppress-uniques -dno-typeable-binds
ghc -o Repro Lib.o Repro.o && ./Repro +RTS -s
```

## Expected behavior

`Repro` specialises the recursive call under `Sub` at `@D @_`, with and without the phase.

## Environment

* GHC version used: HEAD 10.1.20260925 (commit 9f48a5b908), 9.14.1, 9.12.2

Optional:

* Operating System: Ubuntu 24.04
* System Architecture: x86_64

/label ~"T::bug"
/label ~"needs triage"
