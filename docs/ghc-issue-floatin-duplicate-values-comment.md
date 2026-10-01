# GHC issue comment: duplicating small values into the case alternatives that use them, measured against the other obvious fixes

Staged 2026-10-01, revised 2026-10-02, as a comment for GHC [#24466](https://gitlab.haskell.org/ghc/ghc/-/work_items/24466) ("Improve FloatIn for case expressions"); not posted. The text from "Here is a case from practice" down is the body. It replaces a draft of a new issue, staged the same day and never filed, which first proposed the float-out rule of GHC [#15606](https://gitlab.haskell.org/ghc/ghc/-/work_items/15606) and then measured it losing sharing; the tracker search of 2026-10-01 found #24466, whose float-in direction is where every measurement below points. Found in horde-ad, in the GHC [#26827](https://gitlab.haskell.org/ghc/ghc/-/work_items/26827) work: specialising the interpreter in its defining module, with `SPECIALISE` pragmas, allocated 10.5% more on an MNIST benchmark than letting each importer specialise it. The body names the compilers measured: HEAD with the fixes proposed in GHC [#27873](https://gitlab.haskell.org/ghc/ghc/-/work_items/27873), GHC [#27874](https://gitlab.haskell.org/ghc/ghc/-/work_items/27874) and GHC [#27880](https://gitlab.haskell.org/ghc/ghc/-/work_items/27880), plus each prototype. The programs, scripts and raw results are in the session's scratch tree, not in this repository. Still running when this was written: nofib and horde-ad with the prototype extended to thunks, and the main measurements on HEAD without the three fixes.

Here is a case from practice for floating into several alternatives, restricted at first to values (from horde-ad, where it made specialising the interpreter in its defining module, with `SPECIALISE` pragmas, allocate 10.5% more on an MNIST benchmark than specialisation in each importer), with measurements of several size policies and of the other obvious fixes, including the float-out rule of #15606. The collection of programs written to break each fix is probably the most useful part. All compilers measured are builds of HEAD `9f48a5b908` (10.1.20260925) with the fixes proposed in #27873 and #27880 (`GHC.Core.Opt.Specialise`) and #27874 (`GHC.Core.Utils`), "guard" below, each plus the prototype measured, in `GHC.Core.Opt.FloatIn`, `GHC.Core.Opt.SetLevels`, `GHC.Core.Opt.CSE` or `GHC.Core.Opt.Pipeline`; `perf/compiler` and nofib figures are relative to guard.

### The case

```haskell
eval :: Int -> E -> Int
eval k | check k = \case                     -- check is NOINLINE
  Lit n -> n
  Add a b -> eval k a + eval k b
  I1 a ix -> eval k a + sum (mapS (ev k) ix) -- mapS: INLINE map, ev: NOINLINE
  I2 a ix -> eval k a * sum (mapS (ev k) ix)
  I3 a ix -> eval k a - sum (mapS (ev k) ix)
eval _ = const 0
```

This allocates 582 MB where the same function with the term as an argument, `eval k t | check k = case t of ...`, allocates 320 MB (9.12.2, 9.14.1 and HEAD alike). `mapS (ev k)` inlines to a local recursive `go` in each of the three alternatives. The first float-out pass, which runs before arity analysis, floats the three `go`s out of `\ds` (the `\case` lambda), since they don't mention `ds`. After Call Arity the simplifier eta-expands `eval`, so nothing is shared any more, and CSE merges the three identical `go`s into one. The float-in pass after CSE then leaves the merged `go` above the case, because three alternatives use it and it is not `exprIsDupable`: one closure is allocated on every call, also for `Lit` and `Add`. With `-fno-cse`, float-in sinks each copy into its alternative and the program allocates 320 MB.

### The obvious fixes

| fix | where | the case | worst loss found |
|---|---|---|---|
| don't float out of a lambda separated from the binding's own lambdas only by lets and cases (#15606), first float-out pass only | SetLevels | fixed | #15606's own example with a shared partial application, about 60x slower (W3); a cheap guard before `\y -> expensive x + y`, about 35x (W8) |
| the same in every pass, as #15606 proposes | SetLevels | fixed | W8 as above |
| the same, but only for values (functions and constructor applications), whose float saves only allocation | SetLevels | fixed in one module, half fixed across modules | a local function and a call `go 1000` to it under the lambda, with a shared partial application, about 60x slower (W13): keeping the value in keeps the work that depends on it |
| (SW2) of `Note [Saving work]`, which keeps HNF expressions in, extended to let-bound values: no float out of an alternative of a case with several alternatives | SetLevels | fixed | a loop whose `otherwise` branch defines `go` and calls `go 1000`: 3.2 GB instead of 13 MB, 136x slower (L5): loop-invariant code motion is lost; three other loops allocate 5% to 33% more (D, I, P3) |
| CSE doesn't merge let-bound lambdas | CSE | fixed, and three of four variations across modules | P3 allocates 37% more (88 MB instead of 64); a variation where the function is never eta-expanded 32% more (1264 MB instead of 957), since there all copies are allocated on every call and merging them helped; S6 and S7 9% more |
| an extra float-in pass before CSE | pipeline | fixed, half fixed across modules (262 and 387 MB where the argument form has 198 and 323) | S6 and S7 allocate 9% more (1958 MB instead of 1798) |
| float-in duplicates a value (or a thunk, below) into the alternatives that use it | FloatIn | fixed | no sharing can be lost, since float-out is untouched; a size limit that stops partway down nested cases allocates up to 13% more (M, below), unless a simplifier pass runs between the late CSE and float-in, for 0.6% to 0.9% more compile-time allocation; the cost is code, up to 2.3 times in the size family and 6 times in nested cases unless the copies share one budget |
| arity worker/wrapper (#19230), written by hand | source | fixed: 291 MB, below the argument form's 320 | not a GHC change yet; it also removes the remaining variations, where the function is never eta-expanded (957 MB to 192 MB in one, below the argument form) |

Every restriction of float-out tried has an unbounded loss: a float of a value out of a lambda that is later eta-expanded saves nothing, but before arity analysis SetLevels cannot know which lambdas will be eta-expanded, and the floated value is often what lets work that depends on it float too, which keeps the lambda from being eta-expanded at all. Float-in runs after eta-expansion and never moves anything into a lambda, so duplicating values there cannot lose sharing. Allocation can still go up, by a closure per call, when a size limit stops partway down nested cases (below). The 41 programs written to find a loss of sharing (below, apart from the size and nested families) allocate exactly as much with each of the size policies below as without the change.

### Size policies

Duplication only costs code. Three policies for how much, in a family of programs where local functions are used in some alternatives of a 6-to-21-alternative case; the argument form, `eval k t | check k = case t of ...`, is the target. MB allocated / bytes of `.text` in `Main.o`:

| program | guard | inline threshold (size ≤ 90 after discounts) | budget ((n−1) × size ≤ 750) | creation threshold (size ≤ 750) | float-in before CSE | CSE doesn't merge lambdas | argument form |
|---|---|---|---|---|---|---|---|
| S1, `go` (size 100) in 3 of 6 alternatives | 582 / 4687 | 320 / 5359 | 320 / 5359 | 320 / 5359 | 320 / 5359 | 320 / 5359 | 320 / 5359 |
| S1, size 130 (one more call) | 646 / 4719 | 646 / 4719 | 384 / 5455 | 384 / 5455 | 384 / 5455 | 384 / 5455 | 384 / 5455 |
| S1, size 283 | 1030 / 4983 | 1030 / 4983 | 768 / 6247 | 768 / 6247 | 768 / 6247 | 768 / 6247 | 768 / 6247 |
| S1, size 385 | 1286 / 5159 | 1286 / 5159 | 1286 / 5159 | 1024 / 6775 | 1024 / 6775 | 1024 / 6775 | 1024 / 6775 |
| S1, size 691 | 2054 / 5687 | 2054 / 5687 | 2054 / 5687 | 1792 / 8359 | 1792 / 8359 | 1792 / 8359 | 1792 / 8359 |
| S1, size 793 | 2310 / 5863 | 2310 / 5863 | 2310 / 5863 | 2310 / 5863 | 2048 / 8887 | 2048 / 8887 | 2048 / 8887 |
| S2, an independent small (100) and big (691) function in the same 3 of 6 | 2378 / 6631 | 2246 / 7375 | 2246 / 7375 | 1984 / 10207 | 1984 / 10207 | 1984 / 10207 | 1984 / 10207 |
| S3, a big function (773) that calls a small one, in 3 of 6 | 2875 / 6327 | 2875 / 6327 | 2875 / 6327 | 2875 / 6327 | 2416 / 10279 | 2416 / 10279 | 2416 / 10279 |
| S4, `go` (100) in 20 of 21 alternatives | 582 / 12127 | 320 / 18919 | 582 / 12127 | 320 / 18919 | 320 / 18919 | 320 / 18919 | 320 / 18919 |
| S5, ten functions (100 to 120), each in 9 of 10 alternatives | 3331 / 28759 | 3005 / 31639 | 3331 / 28759 | 1824 / 64479 | 1824 / 64479 | 1824 / 64479 | 1824 / 64479 |
| S6, one function written once, `let bigmap = mapS (\i -> ...)` before `\case`, used in 9 of 10 alternatives | 1798 / 7767 | 1798 / 7767 | 1798 / 7767 | 1536 / 17543 | 1958 / 11183 | 1958 / 11183 | 1958 / 11183 |
| S7, the same used in 2 of 10 | 1798 / 6711 | 1798 / 6711 | 1536 / 7895 | 1536 / 7895 | 1958 / 7327 | 1958 / 7327 | 1958 / 7327 |

Where the creation threshold succeeds, it reaches the argument form exactly, in allocation and in code: the copies it makes are the ones the source had before full laziness and CSE merged them. Every size limit has a cliff, though, and just above it nothing is gained: at size 793 (S1) or when the big function a small one is called from is just over the limit (S3, 773), all three policies keep the closures on every call, where the argument form allocates 11% and 16% less. S6 and S7 are the other side: the programmer wrote one copy, and duplication makes nine (S6: 2.3 times the code for 15% less allocation) or two. The inline threshold is the wrong yardstick: the basic `go` passes only because of its 10-point discount, and one more call (size 130) already fails, and so did the merged function of a real variation of the case, whose call to `ev` passes a dictionary (size 110). The budget bounds the code added at each case to one unfolding creation threshold, but gives up exactly when many alternatives use the value (S4, S5), as in a large interpreter. The creation threshold takes every win the argument form has, at up to 2.3 times the code (S5, S6). In S2, a policy that duplicates only the small function pays its code and keeps the big one's allocation. The two fixes that keep the source's copies apart instead of merging and re-creating them, float-in before CSE and CSE that doesn't merge lambdas, reach the argument form in every row, in allocation and in code, with no size limit; but in S6 and S7 they allocate 9% more than guard, as the argument form does, and the table of fixes above lists their other losses.

### Nested cases

The size checks above are made at each case separately, so in nested cases they compound. In N, one local function (unfolding size 253 or 661) is used at every leaf of d levels of three-way cases, two alternatives of each using it (a binding that every alternative uses is never pushed): the budget and the creation threshold both copy it to every leaf, 256 copies at depth 8, up to six times guard's code and, in one run, 3.5 and 3.2 seconds of compile time instead of 2.0. Letting the copies share one budget bounds that: a binding starts with one unfolding creation threshold, a case spends (n − 1) × size of it, and each of the n copies gets an equal part of what is left, so all copies of a binding add at most the threshold per float-in pass, whatever the nesting.

Any limit that stops partway down, though, can allocate more than not duplicating at all. In M, the late CSE merges the leaves' loops (`go`, from `mapS g`) into one that calls `g`, and that is `g`'s only use, so the simplifier after float-in would inline `g` into it, as it does in guard. Float-in instead copies the loop to the leaves and `g` only as far as the size limit allows, where each copy of `g` keeps several uses, is not inlined, and costs one more closure per call: 13% more than guard with the shared budget in M at size 253, 6% with the plain budget at size 661. Running the simplifier between the late CSE and float-in inlines `g` into the merged loop first; with that pass the shared budget allocates no more than guard in every row of both families, for 3% to 29% more code. The pass alone changes nothing in these programs. It is not free: compile-time allocation in `perf/compiler` rises by 0.92% on geometric mean and by up to 4.9% (T9961), or by 0.59% with a single iteration, which gives the same results in every program here; the testsuite otherwise changes only in two tests that count simplifier runs or print the inliner's trace (`rule2`, `inline-check`). Moving float-in after the final simplifier instead costs nothing and gives the same results here too, but leaves float-in's output unsimplified, which loses the case-of-known-constructor that T14152 checks for and weakens a demand signature in T22241. With or without the pass, the shared budget allocates exactly as the plain budget on the size family above and on the 41 sharing programs; the plain budget with the pass fixes M but not N's code. MB allocated / bytes of `.text`:

| program | guard | budget | creation threshold | shared budget | shared budget, simplifier after CSE |
|---|---|---|---|---|---|
| N, depth 4, size 661 | 160 / 8071 | 96 / 28927 | 96 / 28927 | 149 / 10783 | 139 / 9559 |
| N, depth 8, size 661 | 160 / 71215 | 96 / 425951 | 96 / 425951 | 149 / 74983 | 139 / 73759 |
| N, depth 8, size 253 | 160 / 70511 | 96 / 245727 | 96 / 245727 | 117 / 73775 | 139 / 72351 |
| M, 2 of 3, then 2 of 3, size 661 | 704 / 4911 | 661 / 9087 | 661 / 9087 | 736 / 7503 | 683 / 6311 |
| M, 2 of 3, then 3 of 4, size 253 | 464 / 4679 | 432 / 8079 | 432 / 8079 | 523 / 7311 | 443 / 5375 |
| M, 2 of 3, then 3 of 4, size 661 | 976 / 5383 | 1035 / 8719 | 944 / 12303 | 1035 / 8719 | 955 / 6783 |

### Examples from the related tickets

None of the examples in this ticket, #2988, #24655, #19230 and #15606, each made into a program with a driver, changes with the values-only prototype; duplicating thunks too, under the same budget, fixes the first example of this ticket and changes nothing else. MB allocated / mutator seconds, median of 7 runs:

| ticket | example | guard | values only | values and thunks | why the values-only prototype changes nothing |
|---|---|---|---|---|---|
| #24466 | `f z x`, a thunk `y = x+1` in two of three alternatives, the third hot | 472 / 0.063 | 472 / 0.066 | 280 / 0.050 | `y` is a thunk |
| #24466 | `foo1`, a thunk used by a join point and one alternative | 0.05 / 0.028 | 0.05 / 0.029 | 0.05 / 0.028 | every path uses `x`, so it is strict and evaluated eagerly; there is no thunk |
| #24466 | `foo2`, the same with `x` also in the scrutinee | 0.05 / 0.020 | 0.05 / 0.019 | 0.05 / 0.019 | as `foo1`; and a binding the scrutinee uses is never pushed |
| #2988 | the cascade `x1` to `x4`, `x4` used in both alternatives | 1280 / 0.130 | 1280 / 0.131 | 1280 / 0.129 | every alternative uses `x4` |
| #2988 | `x` in two of three alternatives, the third hot, `x` a local function | 208 / 0.022 | 208 / 0.022 | 208 / 0.022 | the simplifier inlines `x` into both alternatives and fuses each `map` into a loop: no closure is left |
| #2988 | the same with `x` a thunk | 64 / 0.038 | 64 / 0.037 | 64 / 0.038 | `postInlineUnconditionally` inlines it, since each alternative uses it once |
| #24655 | `(x,x)` returned at the end of a local loop | 16 / 0.007 | 16 / 0.007 | 16 / 0.007 | HEAD builds `(x,x)` in the loop's exit join point (the fix of #24655) |
| #24655 | an inlined function's lambda that could float out of `\p`, in two of three alternatives | 144 / 0.029 | 144 / 0.030 | 144 / 0.029 | fusion removes the lambda |
| #19230 | `e5'1` | 632 / 0.190 | 632 / 0.192 | 632 / 0.194 | an arity problem, which float-in can't reach |
| #15606 | `f x = let y = blah x in \z -> let v = h x y in v + z`, shared partial application (W3) | 6 / 0.003 | 6 / 0.003 | 6 / 0.003 | float-out decides it; nothing reaches a case with several alternatives |

A thunk can be duplicated into the alternatives for the same reason as a value: only one alternative runs, and a binding that the scrutinee or anything outside the case uses is not pushed, so it is evaluated at most as often as before. With thunks too, the size, nested and sharing programs above allocate the same and have the same code size as with values only, and the testsuite and `perf/compiler` results are those of the values-only prototype (every compile-time metric within 0.01%). The first example's driver: `f` is `NOINLINE` and ``main = print (foldl' (\acc k -> case f (k `mod` 10) k of (a, b) -> acc + a + b) 0 [1 .. 10000000 :: Int])``; the others are in the same style.

### Testsuite, nofib and horde-ad

With the budget and the creation-threshold policies alike, the testsuite passes (11802 expected passes, nothing unexpected) and none of the 105 `perf/compiler` allocation metrics moves by more than 0.015%; an earlier policy failed two Core-shape tests by duplicating `NOINLINE` bindings and a join point, and cost T15630 4% by duplicating join points, so both policies exclude those. On nofib (`-s Fast`, 114 benchmarks; four need packages not installed here), the inline-threshold, budget and creation-threshold policies change allocation by at most 0.12%, geometric mean 1.0000. In horde-ad, with each of those three, the defining-module `SPECIALISE` build allocates the same as importer specialisation on all 158 benchmarks of its three allocation-checked suites (geometric means 0.9998 to 1.0000, extremes 0.9970 and 1.0006), instead of up to 10.5% more, and the importer-specialised build is unchanged with the inline threshold and the creation threshold (extremes 0.9982 and 1.0004). With the shared budget and the pass, nofib changes allocation by at most 0.68% (geometric mean 1.0001), horde-ad allocates as importer specialisation does in both builds (extremes 0.9982 and 1.0005), and `minimalTest` and `CAFlessTest` fail the same 3 and 4 tests as with guard (printed-AST tests whose fresh variable numbers differ on HEAD). horde-ad is built from one tree throughout, with `-fno-worker-wrapper-cbv` on its interpreter module and inspection-testing disabled. Build times, 1949 to 2326 seconds with the duplicating compilers and 2226 to 2530 with guard, measured at different times, show no cost.

<details><summary>The prototype: a shared budget for values and thunks, and a one-iteration simplifier pass after the late CSE</summary>

```diff
diff --git a/compiler/GHC/Core/Opt/FloatIn.hs b/compiler/GHC/Core/Opt/FloatIn.hs
--- a/compiler/GHC/Core/Opt/FloatIn.hs
+++ b/compiler/GHC/Core/Opt/FloatIn.hs
@@ -23,13 +23,16 @@ import GHC.Platform
 
 import GHC.Core
 import GHC.Core.Opt.Arity( isOneShotBndr )
+import GHC.Core.Unfold ( ExprSize(..), sizeExpr, defaultUnfoldingOpts
+                       , unfoldingCreationThreshold )
 import GHC.Core.Make hiding ( wrapFloats )
 import GHC.Core.Utils
 import GHC.Core.FVs
 import GHC.Core.Type
 
 import GHC.Types.Basic      ( RecFlag(..), isRec )
-import GHC.Types.Id         ( idType, isJoinId, idJoinPointHood )
+import GHC.Types.InlinePragma ( isNoInlinePragma )
+import GHC.Types.Id         ( idType, isJoinId, idJoinPointHood, idInlinePragma )
 import GHC.Types.Tickish
 import GHC.Types.Var
 import GHC.Types.Var.Set
@@ -40,6 +43,7 @@ import GHC.Utils.Panic
 import GHC.Utils.Outputable
 
 import Data.List        ( mapAccumL )
+import Data.Maybe       ( fromMaybe, isJust )
 
 {-
 Top-level interface function, @floatInwards@.  Note that we do not
@@ -130,10 +134,11 @@ the closure for a is not built.
 type FreeVarSet  = DVarSet
 type BoundVarSet = DIdSet
 
-data FloatInBind = FB BoundVarSet FreeVarSet FloatBind
+data FloatInBind = FB BoundVarSet FreeVarSet FloatBind Int
         -- The FreeVarSet is the free variables of the binding.  In the case
         -- of recursive bindings, the set doesn't include the bound
-        -- variables.
+        -- variables.  The Int is the code that duplicating the binding
+        -- may still add; see Note [Duplicating floats].
 
 type FloatInBinds    = [FloatInBind] -- In normal dependency order
                                      --    (outermost binder first)
@@ -141,7 +146,7 @@ type RevFloatInBinds = [FloatInBind] -- In reverse dependency order
                                      --    (innermost binder first)
 
 instance Outputable FloatInBind where
-  ppr (FB bvs fvs _) = text "FB" <> braces (sep [ text "bndrs =" <+> ppr bvs
+  ppr (FB bvs fvs _ _) = text "FB" <> braces (sep [ text "bndrs =" <+> ppr bvs
                                                 , text "fvs =" <+> ppr fvs ])
 
 fiExpr :: Platform
@@ -530,7 +535,7 @@ fiExpr platform to_drop (_, AnnCase scrut case_bndr _ [AnnAlt con alt_bndrs rhs]
     fiExpr platform (case_float : rhs_binds) rhs
   where
     case_float = FB all_bndrs scrut_fvs
-                    (FloatCase scrut' case_bndr con alt_bndrs)
+                    (FloatCase scrut' case_bndr con alt_bndrs) dupBudget
     scrut'     = fiExpr platform scrut_binds scrut
     rhs_fvs    = freeVarsOf rhs    -- No need to delete alt_bndrs
     scrut_fvs  = freeVarsOf scrut  -- See Note [Shadowing and name capture]
@@ -586,7 +591,7 @@ fiBind platform to_drop (AnnNonRec id ann_rhs@(rhs_fvs, rhs)) body_fvs
   = ( shared_binds          -- Land these before
                             -- See Note [extra_fvs (1)] and Note [extra_fvs (2)]
     , FB (unitDVarSet id) rhs_fvs'         -- The new binding itself
-          (FloatLet (NonRec id rhs'))
+          (FloatLet (NonRec id rhs')) dupBudget
     , body_binds )                         -- Land these after
 
   where
@@ -614,7 +619,7 @@ fiBind platform to_drop (AnnNonRec id ann_rhs@(rhs_fvs, rhs)) body_fvs
 fiBind platform to_drop (AnnRec bindings) body_fvs
   = ( shared_binds
     , FB (mkDVarSet ids) rhs_fvs'
-         (FloatLet (Rec (fi_bind rhss_binds bindings)))
+         (FloatLet (Rec (fi_bind rhss_binds bindings))) dupBudget
     , body_binds )
   where
     (ids, rhss) = unzip bindings
@@ -745,7 +750,7 @@ We have to maintain the order on these drop-point-related lists.
 -}
 
 -- pprFIB :: RevFloatInBinds -> SDoc
--- pprFIB fibs = text "FIB:" <+> ppr [b | FB _ _ b <- fibs]
+-- pprFIB fibs = text "FIB:" <+> ppr [b | FB _ _ b _ <- fibs]
 
 sepBindsByDropPoint
     :: Platform
@@ -794,7 +799,7 @@ sepBindsByDropPoint platform is_case floaters here_fvs fork_fvs
     go [] here_box fork_boxes
         = (dropBoxFloats here_box, map dropBoxFloats fork_boxes)
 
-    go (bind_w_fvs@(FB bndrs bind_fvs bind) : binds) here_box fork_boxes
+    go (bind_w_fvs@(FB bndrs bind_fvs bind budget) : binds) here_box fork_boxes
         | drop_here = go binds (insert here_box) fork_boxes
         | otherwise = go binds here_box          new_fork_boxes
         where
@@ -816,19 +821,29 @@ sepBindsByDropPoint platform is_case floaters here_fvs fork_fvs
           cant_push
             | is_case   = (n_alts > 1 && n_used_alts == n_alts)
                              -- Used in all, muliple branches, don't push
-                          || (n_used_alts > 1 && not (floatIsDupable platform bind))
-                             -- floatIsDupable: see Note [Duplicating floats]
+                          || (n_used_alts > 1 && not (floatIsDupable platform bind
+                                                      || small_enough))
+                             -- floatIsDupable, small_enough:
+                             -- see Note [Duplicating floats]
 
             | otherwise = floatIsCase bind || n_used_alts > 1
                              -- floatIsCase: see Note [Floating primops]
 
+          -- Each copy shares what is left of the budget
+          -- See Note [Duplicating floats]
+          copy_cost    = (n_used_alts - 1) * fromMaybe 0 (floatCopySize bind)
+          small_enough = isJust (floatCopySize bind) && copy_cost <= budget
+          copy         | n_used_alts > 1, small_enough
+                       = FB bndrs bind_fvs bind ((budget - copy_cost) `div` n_used_alts)
+                       | otherwise = bind_w_fvs
+
           new_fork_boxes = zipWithEqual insert_maybe
                                         fork_boxes used_in_flags
 
           insert :: DropBox -> DropBox
           insert (fvs,drops) = (fvs `unionDVarSet` bind_fvs, bind_w_fvs:drops)
 
-          insert_maybe box True  = insert box
+          insert_maybe (fvs,drops) True = (fvs `unionDVarSet` bind_fvs, copy:drops)
           insert_maybe box False = box
 
 
@@ -845,18 +860,56 @@ situations like
 
 If the thing is used in all RHSs there is nothing gained,
 so we don't duplicate then.
+
+We also duplicate any let binding, a value or a thunk, if the code the
+copies add, (n-1) times its size for n alternatives, is within its
+budget: duplicating it into the alternatives that use it never
+duplicates work, since only one alternative runs and a binding that the
+scrutinee uses is not pushed, and it saves its allocation in the
+alternatives that don't use it.  The budget starts at the unfolding
+creation threshold and the copies share what is left of it, so nested
+cases cannot compound the duplication: in one float-in pass, all copies
+of a binding add at most the threshold.  (Not for join points, which
+are not allocated, nor for NOINLINE bindings.)  E.g. full laziness may
+float identical local functions out of three alternatives of
+     \x -> \t -> case t of { A ix -> ..go1.. ; B ix -> ..go2.. ; C -> 0 }
+when (\t) is still a separate lambda; if the function is later
+eta-expanded, CSE merges the copies, and without duplication the merged
+function is allocated on every call, also for C.
 -}
 
+dupBudget :: Int
+dupBudget = unfoldingCreationThreshold defaultUnfoldingOpts
+
+floatCopySize :: FloatBind -> Maybe Int
+-- The size of one copy, if the binding may be duplicated
+floatCopySize (FloatLet (NonRec b r))
+  | dup_ok b = Just (copySize r)
+floatCopySize (FloatLet (Rec prs))
+  | all (dup_ok . fst) prs
+  = Just (sum (map (copySize . snd) prs))
+floatCopySize _ = Nothing
+
+copySize :: CoreExpr -> Int
+copySize r = case sizeExpr defaultUnfoldingOpts dupBudget [] (snd (collectBinders r)) of
+                SizeIs { _es_size_is = s } -> s
+                TooBig                     -> dupBudget + 1
+
+-- A join point is not allocated, so duplicating it saves nothing; and a
+-- NOINLINE binding is one the programmer wants to have a single copy of.
+dup_ok :: Id -> Bool
+dup_ok b = not (isJoinId b) && not (isNoInlinePragma (idInlinePragma b))
+
 floatedBindsFVs :: RevFloatInBinds -> FreeVarSet
 floatedBindsFVs binds = mapUnionDVarSet fbFVs binds
 
 fbFVs :: FloatInBind -> DVarSet
-fbFVs (FB _ fvs _) = fvs
+fbFVs (FB _ fvs _ _) = fvs
 
 wrapFloats :: RevFloatInBinds -> CoreExpr -> CoreExpr
 -- Remember RevFloatInBinds is in *reverse* dependency order
 wrapFloats []               e = e
-wrapFloats (FB _ _ fl : bs) e = wrapFloats bs (wrapFloat fl e)
+wrapFloats (FB _ _ fl _ : bs) e = wrapFloats bs (wrapFloat fl e)
 
 floatIsDupable :: Platform -> FloatBind -> Bool
 floatIsDupable platform (FloatCase scrut _ _ _) = exprIsDupable platform scrut
diff --git a/compiler/GHC/Core/Opt/Pipeline.hs b/compiler/GHC/Core/Opt/Pipeline.hs
--- a/compiler/GHC/Core/Opt/Pipeline.hs
+++ b/compiler/GHC/Core/Opt/Pipeline.hs
@@ -283,6 +283,11 @@ getCoreToDo dflags hpt_rule_base extra_vars
                 -- succeed in commoning up things floated out by full laziness.
                 -- CSE used to rely on the no-shadowing invariant, but it doesn't any more
 
+        runWhen cse (simpl_phase FinalPhase "post-late-cse" 1),
+                -- One iteration: inline what CSE left used once (e.g. a function
+                -- only the merged copies called) before float-in duplicates the
+                -- merged copies.
+
         runWhen do_float_in CoreDoFloatInwards,
 
         simplify "final",  -- Final tidy-up
```

The values-only prototype also requires `exprIsHNF` of each right-hand side in `floatCopySize`. The budget policy keeps no budget in `FloatInBind` and checks `(n - 1) * size` against the threshold at each case; the creation-threshold policy checks `size` alone. The full simplifier, `simplify "post-late-cse"`, gives the same results for 0.92% more compile-time allocation instead of 0.59%.

</details>

<details><summary>The programs written to break the fixes</summary>

Each is a `Main` module compiled with `-O`; `expensive k = sum [1 .. 2000 + k `mod` 7]` and the other helpers are `NOINLINE`.

W3, #15606's own example, with a shared partial application (the float of `h x y` out of `\z` keeps `f` at arity 1):

```haskell
f :: Int -> Int -> Int
f x = let y = blah x in \z -> let v = h x y in v + z  -- h x y = expensive (x + y)
main = print (sum [let g = f k in sum (map g [1 .. 1000]) | k <- [1 .. 200]])
```

W8, a cheap guard:

```haskell
f :: Int -> Int -> Int
f x | x > 0 = \y -> expensive x + y
f _ = id
main = print (sum [let g = f k in sum (map g [1 .. 1000]) | k <- [1 .. 200]])
```

W13, a local function and a constant call to it:

```haskell
f :: Int -> Int -> Int
f x | x > 0 = \y -> let { go :: Int -> Int; go 0 = x; go m = go (m - 1) + 1 } in go 1000 + go (y `mod` 3) + y
f _ = id
main = print (sum [let g = f k in sum (map g [1 .. 1000]) | k <- [1 .. 200]])
```

L5, a loop-invariant function in a branch of a loop:

```haskell
f :: Int -> Int -> Int
f x n = loop 0 0
  where
    loop :: Int -> Int -> Int
    loop acc i
      | i == n = acc
      | otherwise = let { go :: Int -> Int; go 0 = x; go m = go (m - 1) + 1 } in loop (acc + go 1000 + go (i `mod` 7)) (i + 1)
main = print (sum [f k 1000 | k <- [1 .. 200]])
```

The size family shares this preamble and ending, with `ev :: Int -> Int -> Int` and `check :: Int -> Bool` both `NOINLINE`:

```haskell
mapS :: (a -> b) -> [a] -> [b]
{-# INLINE mapS #-}
mapS f l =
  let go [] = []
      go (x : xs) = let y = f x; rest = go xs in y `seq` rest `seq` (y : rest)
  in go l
data E = Lit Int | Add E E | C0 E [Int] | C1 E [Int] | C2 E [Int] | C3 E [Int] | C4 E [Int] | C5 E [Int]
eval :: Int -> E -> Int
eval k | check k = \case
  Lit n -> n
  Add a b -> eval k a + eval k b
  -- the alternatives below
eval _ = const 0
mk :: Int -> E
mk 0 = Lit 0
mk n = Add (mk (n - 1)) (if even n then Lit n else C0 (Lit 1) [1, 2])  -- C1 in S4
main :: IO ()
main = print (sum [eval k (mk 20) | k <- [1 .. 200000]])
```

S1 at size 130; each further level of `ev k (... + j)` adds about 50 to the size:

```haskell
  C0 a ix -> eval k a + sum (mapS (\i -> ev k (ev k i + 0)) ix)
  C1 a ix -> eval k a + sum (mapS (\i -> ev k (ev k i + 0)) ix)
  C2 a ix -> eval k a + sum (mapS (\i -> ev k (ev k i + 0)) ix)
  C3 a ix -> eval k a + length ix
  C4 a ix -> eval k a + length ix
  C5 a ix -> eval k a + length ix
```

S2, a small and a big function side by side (C1 and C2 the same as C0, C3 to C5 as in S1):

```haskell
  C0 a ix -> eval k a + sum (mapS (ev k) ix) + sum (mapS (\i -> ev k (ev k (ev k (ev k (ev k (ev k (ev k (ev k (ev k (ev k (ev k (ev k (ev k i + 0) + 1) + 2) + 3) + 4) + 5) + 6) + 7) + 8) + 9) + 10) + 11)) ix)
```

S3, the big function calling the small one:

```haskell
  C0 a ix -> eval k a + sum (mapS (\i -> ev k (ev k (ev k (ev k (ev k (ev k (ev k (ev k (ev k (ev k (ev k (ev k (ev k i + 0) + 1) + 2) + 3) + 4) + 5) + 6) + 7) + 8) + 9) + 10) + 11) + sum (mapS (ev k) [i, i])) ix)
```

S4, constructors `C0` to `C20`; `C0 a ix -> eval k a + length ix`, and for each of `C1` to `C20`:

```haskell
  C1 a ix -> eval k a + sum (mapS (ev k) ix)
```

S5, constructors `C0` to `C9` and ten `NOINLINE` functions `evj k i = k + i + j`; alternative `Cj` sums `mapS (evm k) ix` over every `m` except `j`:

```haskell
  C0 a ix -> eval k a + sum (mapS (ev1 k) ix) + sum (mapS (ev2 k) ix) + ... + sum (mapS (ev9 k) ix)
```

S6, constructors `C0` to `C9`, one copy written by the programmer (S7 the same, with only `C0` and `C1` using `bigmap`):

```haskell
eval k | check k = let bigmap = mapS (\i -> ev k (ev k (ev k (ev k (ev k (ev k (ev k (ev k (ev k (ev k (ev k i + 0) + 1) + 2) + 3) + 4) + 5) + 6) + 7) + 8) + 9)) in \case
  Lit n -> n
  Add a b -> eval k a + eval k b
  C0 a ix -> eval k a + sum (bigmap ix)  -- and C1 to C8 the same
  C9 a ix -> eval k a + length ix
```

N and M share the size family's preamble and ending, with `data E = Lit Int | Add E E | C0 E [Int] | C1 E [Int]`, `C1 a ix -> eval k a + length ix` and a `NOINLINE` selector ``sel k = k `mod` 3`` (in M, `sel3` and ``sel4 k = k `mod` 4``). N at depth 2 and size 253; each further level replaces every leaf by another such case:

```haskell
  C0 a ix -> eval k a + (let g = \i -> ev k (ev k (ev k (ev k (ev k i + 0) + 1) + 2) + 3) in (case sel (k - 0) of { 0 -> (case sel (k - 1) of { 0 -> sum (mapS g ix) + 0; 1 -> sum (mapS g ix) + 1; _ -> 0 }); 1 -> (case sel (k - 1) of { 0 -> sum (mapS g ix) + 2; 1 -> sum (mapS g ix) + 3; _ -> 1 }); _ -> 0 }))
```

M with 2 of 3, then 3 of 4, at size 253; size 661 has twelve levels of `ev k (... + j)`:

```haskell
  C0 a ix -> eval k a + (let g = \i -> ev k (ev k (ev k (ev k (ev k i + 0) + 1) + 2) + 3) in (case sel3 k of { 0 -> (case sel4 (k - 1) of { 0 -> sum (mapS g ix) + 0; 1 -> sum (mapS g ix) + 1; 2 -> sum (mapS g ix) + 2; _ -> 4 }); 1 -> (case sel4 (k - 1) of { 0 -> sum (mapS g ix) + 100; 1 -> sum (mapS g ix) + 101; 2 -> sum (mapS g ix) + 102; _ -> 104 }); _ -> 7 }))
```

D, I and P3, where (SW2) for let-bound values allocates 33%, 7% and 5% more, because the local function can't leave the branch:

```haskell
f :: Int -> Int -> Int  -- D
f x n = loop 0 0
  where
    loop :: Int -> Int -> Int
    loop acc i
      | i == n = acc
      | otherwise = let { go :: Int -> Int; go 0 = x; go m = go (m - 1) + 1 } in loop (acc + go (i `mod` 3) * go (i `mod` 5)) (i + 1)
main = print (sum [f k 1000 | k <- [1 .. 2000]])

f :: Int -> [Int] -> [Int]  -- I
f x = map (\y -> if even y then (let { go :: Int -> Int; go 0 = x; go m = go (m - 1) + 1 } in go (y `mod` 3) * go (y `mod` 5)) else y)
main = print (sum (concat [f k [1 .. 1000] | k <- [1 .. 2000]]))

eval :: Int -> E -> Int  -- P3, E as in the case above
eval x | check x = \case
  Lit n -> n
  Add a b -> eval x a + eval x b
  I1 a ix -> eval x a + sum (map (\i -> let { go :: Int -> Int; go 0 = x; go m = go (m - 1) + 1 } in go i) ix)
  I2 a ix -> eval x a * sum (map (\i -> let { go :: Int -> Int; go 0 = x; go m = go (m - 1) + 1 } in go (i + 1)) ix)
  I3 a ix -> eval x a - sum (map (\i -> let { go :: Int -> Int; go 0 = x; go m = go (m - 1) + 1 } in go (i + 2)) ix)
eval _ = const 0
main = print (sum [sum (map (eval k) [mk 5, mk 6, mk 7, mk 8]) | k <- [1 .. 50000]])
```

The other programs, each identical with every float-in variant and with guard: local functions under many-shot lambdas, in fused and unfused loops (`map`, list comprehensions, `foldl`, `zipWith`, explicit recursion), in IO loops, passed to higher-order functions, under shared partial applications, nested two and three deep, used in one branch only, called with constants (once, twice, in nested loops), heavy inner loops whose last iteration the simplifier peels into a constant call; a cheap case with a shared partial application, with work or with a local function under the lambda; #15606's example with its let-bound expression a constructor; a let-bound value and a constructor holding expensive work under a lambda with a shared partial application; user-written sharing between the lambdas; a value depending on the loop variable used in two of three alternatives, and a loop-invariant value bound outside a tail-recursive loop, used in two of three alternatives. The size family above is generated from the case, with the local functions made bigger by nested calls to `ev`.

</details>
