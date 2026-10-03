# Appendix B to the GHC !12121 comment: the prototypes and patches

Appendix to the comment drafted in [`docs/ghc-issue-floatin-duplicate-values-comment.md`](ghc-issue-floatin-duplicate-values-comment.md) for GHC [!12121](https://gitlab.haskell.org/ghc/ghc/-/merge_requests/12121); it is not posted with the comment, which links here.  Every compiler change the comment measures, as a unified diff against GHC HEAD `9f48a5b908` (10.1.20260925), each applying to that commit on its own, unless its section says it is against another variant here, on top of which it then applies.  The name in parentheses after each heading is the compiler's name in the scripts and raw results of [appendix C](ghc-issue-floatin-duplicate-values-appendix-c-scripts-and-results.md).

Contents: [the fixes behind "guard"](#the-fixes-behind-guard), [the prototype](#the-prototype-headthunk1-sharethunk1), [its variants](#variants-of-the-prototype), [the size policies](#the-size-policies), [the float-out restrictions](#the-float-out-restrictions), [the CSE and pipeline alternatives](#the-cse-and-pipeline-alternatives), [!12121 rebased onto HEAD](#12121-rebased-onto-head-headmr-mr12121), [the instrument](#the-instrument-dvdbg2).

## The fixes behind "guard"

The fixes proposed in GHC [#27873](https://gitlab.haskell.org/ghc/ghc/-/work_items/27873) and GHC [#27880](https://gitlab.haskell.org/ghc/ghc/-/work_items/27880) (`GHC.Core.Opt.Specialise`) and GHC [#27874](https://gitlab.haskell.org/ghc/ghc/-/work_items/27874) (`GHC.Core.Utils`), as applied for every compiler named `guard` or built on it (the horde-ad builds and the columns the comment marks as measured on guard).  Compilers named `head*` are built without them.

```diff
diff --git a/compiler/GHC/Core/Opt/Specialise.hs b/compiler/GHC/Core/Opt/Specialise.hs
index 9fb0571d..404e0294 100644
--- a/compiler/GHC/Core/Opt/Specialise.hs
+++ b/compiler/GHC/Core/Opt/Specialise.hs
@@ -34,6 +34,7 @@ import GHC.Core.Utils     ( exprIsTrivial, exprIsTopLevelBindable
                           , stripTicksTop, mkInScopeSetBndrs )
 import GHC.Core.FVs
 import GHC.Core.TyCo.FVs
+import GHC.Core.TyCo.Compare ( eqType )
 import GHC.Core.Opt.Arity( collectBindersPushingCo )
 import GHC.Core.Opt.Monad
 import GHC.Core.Opt.Simplify.Env ( SimplPhase(..), isActive )
@@ -793,7 +794,8 @@ specImports top_env (MkUD { ud_binds = dict_binds, ud_calls = calls })
 -- | Specialise a set of calls to imported bindings
 spec_imports :: SpecEnv          -- Passed in so that all top-level Ids are in scope
                                  ---In-scope set includes the FloatedDictBinds
-             -> [Id]             -- Stack of imported functions being specialised
+             -> [(Id, [[SpecArg]])]  -- Stack of imported functions being specialised,
+                                     -- with the call keys they were specialised at
                                  -- See Note [specImport call stack]
              -> FloatedDictBinds -- Dict bindings, used /only/ for filterCalls
                                  -- See Note [Avoiding loops in specImports]
@@ -826,7 +828,7 @@ spec_imports env callers dict_binds calls
 
 spec_import :: SpecEnv               -- Passed in so that all top-level Ids are in scope
                                      ---In-scope set includes the FloatedDictBinds
-            -> [Id]                  -- Stack of imported functions being specialised
+            -> [(Id, [[SpecArg]])]   -- Stack of imported functions being specialised
                                      -- See Note [specImport call stack]
             -> FloatedDictBinds      -- Dict bindings, used /only/ for filterCalls
                                      -- See Note [Avoiding loops in specImports]
@@ -835,15 +837,6 @@ spec_import :: SpecEnv               -- Passed in so that all top-level Ids are
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
@@ -886,7 +879,7 @@ spec_import env callers dict_binds cis@(CIS fn _)
 --           , text "new_calls" <+> ppr new_calls ])
 
        ; (env, rules2, spec_binds2)
-            <- spec_imports new_env (fn:callers)
+            <- spec_imports new_env ((fn, map ci_key good_calls) : callers)
                                     (dict_binds `thenFDBs` dict_binds1)
                                     new_calls
 
@@ -899,15 +892,49 @@ spec_import env callers dict_binds cis@(CIS fn _)
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
@@ -1162,6 +1189,14 @@ And if the call is to the same type, one specialisation is enough.
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
@@ -1803,11 +1838,21 @@ alreadyCovered env bndrs fn args is_active rules
         | isAutoRule rule -> -- Discard identical rules
                              -- We know that (fn args) is an instance of RULE
                              -- Check if RULE is an instance of (fn args)
-                             ruleLhsIsMoreSpecific in_scope bndrs args rule
+                             rule_is_instance rule
         | otherwise       -> True  -- User rules dominate
   where
     in_scope = substInScopeSet (se_subst env)
 
+    -- Match (fn args) as the template against the LHS of the RULE.
+    -- The other direction, ruleLhsIsMoreSpecific, is what lookupRule
+    -- has already established, so it would make any more general
+    -- auto-rule cover a more specific call; see (SC2).
+    rule_is_instance (Rule { ru_bndrs = rule_bndrs, ru_args = rule_args })
+      = isJust (matchExprs (ISE (in_scope `extendInScopeSetList` rule_bndrs)
+                                noUnfoldingFun)
+                           bndrs args rule_args)
+    rule_is_instance BuiltinRule{} = False
+
 -- Convenience function for invoking lookupRule from Specialise
 -- The SpecEnv's InScopeSet should include all the Vars in the [CoreExpr]
 specLookupRule :: HasDebugCallStack
diff --git a/compiler/GHC/Core/Utils.hs b/compiler/GHC/Core/Utils.hs
index 918cd1a3..19facdf6 100644
--- a/compiler/GHC/Core/Utils.hs
+++ b/compiler/GHC/Core/Utils.hs
@@ -79,7 +79,7 @@ import GHC.Core.FVs( exprFreeVars, bindFreeVars )
 import GHC.Core.DataCon
 import GHC.Core.Type as Type
 import GHC.Core.Predicate( isEqPred )
-import GHC.Core.Predicate( isUnaryClass )
+import GHC.Core.Predicate( isUnaryClass, isDictId )
 import GHC.Core.FamInstEnv
 import GHC.Core.TyCo.Compare( eqType, eqTypeX, eqTypeIgnoringMultiplicity )
 import GHC.Core.Coercion
@@ -3348,6 +3348,9 @@ mkStrictFieldSeqs args rhs =
         -- Argument representing strict field.
         | isMarkedStrict arg_cbv
         , wantCbvForId arg_id
+        -- No eval on a dictionary: it would become a case that takes the
+        -- dictionary apart. See (DNB1) in Note [Do not unbox class dictionaries]
+        , not (isDictId arg_id)
         -- Make sure to remove unfoldings here to avoid the simplifier dropping those for OtherCon[] unfoldings.
         = Case (Var $! zapIdUnfolding arg_id) arg_id case_ty ([Alt DEFAULT [] rhs])
         -- Normal argument
```

## The prototype (headthunk1, sharethunk1)

A budget shared by the copies of a binding, for values and thunks, and one simplifier iteration between the late CSE and float-in: the diff at the end of the comment.  The measured FloatIn.hs differed from this one only in comments and in the names of three helpers (`floatValueSize`, `valueSize` and `small_value` for `floatCopySize`, `copySize` and `small_enough`); the renamed one was compiled and gives the same result on the program checked (R1).

```diff
diff --git a/compiler/GHC/Core/Opt/FloatIn.hs b/compiler/GHC/Core/Opt/FloatIn.hs
--- a/compiler/GHC/Core/Opt/FloatIn.hs
+++ b/compiler/GHC/Core/Opt/FloatIn.hs
@@ -23,13 +23,16 @@
 
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
@@ -40,6 +43,7 @@
 import GHC.Utils.Outputable
 
 import Data.List        ( mapAccumL )
+import Data.Maybe       ( fromMaybe, isJust )
 
 {-
 Top-level interface function, @floatInwards@.  Note that we do not
@@ -130,10 +134,11 @@
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
@@ -141,7 +146,7 @@
                                      --    (innermost binder first)
 
 instance Outputable FloatInBind where
-  ppr (FB bvs fvs _) = text "FB" <> braces (sep [ text "bndrs =" <+> ppr bvs
+  ppr (FB bvs fvs _ _) = text "FB" <> braces (sep [ text "bndrs =" <+> ppr bvs
                                                 , text "fvs =" <+> ppr fvs ])
 
 fiExpr :: Platform
@@ -530,7 +535,7 @@
     fiExpr platform (case_float : rhs_binds) rhs
   where
     case_float = FB all_bndrs scrut_fvs
-                    (FloatCase scrut' case_bndr con alt_bndrs)
+                    (FloatCase scrut' case_bndr con alt_bndrs) dupBudget
     scrut'     = fiExpr platform scrut_binds scrut
     rhs_fvs    = freeVarsOf rhs    -- No need to delete alt_bndrs
     scrut_fvs  = freeVarsOf scrut  -- See Note [Shadowing and name capture]
@@ -586,7 +591,7 @@
   = ( shared_binds          -- Land these before
                             -- See Note [extra_fvs (1)] and Note [extra_fvs (2)]
     , FB (unitDVarSet id) rhs_fvs'         -- The new binding itself
-          (FloatLet (NonRec id rhs'))
+          (FloatLet (NonRec id rhs')) dupBudget
     , body_binds )                         -- Land these after
 
   where
@@ -614,7 +619,7 @@
 fiBind platform to_drop (AnnRec bindings) body_fvs
   = ( shared_binds
     , FB (mkDVarSet ids) rhs_fvs'
-         (FloatLet (Rec (fi_bind rhss_binds bindings)))
+         (FloatLet (Rec (fi_bind rhss_binds bindings))) dupBudget
     , body_binds )
   where
     (ids, rhss) = unzip bindings
@@ -745,7 +750,7 @@
 -}
 
 -- pprFIB :: RevFloatInBinds -> SDoc
--- pprFIB fibs = text "FIB:" <+> ppr [b | FB _ _ b <- fibs]
+-- pprFIB fibs = text "FIB:" <+> ppr [b | FB _ _ b _ <- fibs]
 
 sepBindsByDropPoint
     :: Platform
@@ -794,7 +799,7 @@
     go [] here_box fork_boxes
         = (dropBoxFloats here_box, map dropBoxFloats fork_boxes)
 
-    go (bind_w_fvs@(FB bndrs bind_fvs bind) : binds) here_box fork_boxes
+    go (bind_w_fvs@(FB bndrs bind_fvs bind budget) : binds) here_box fork_boxes
         | drop_here = go binds (insert here_box) fork_boxes
         | otherwise = go binds here_box          new_fork_boxes
         where
@@ -816,19 +821,29 @@
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
 
 
@@ -845,18 +860,56 @@
 
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
@@ -283,6 +283,11 @@
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

## Variants of the prototype

### Values only (headshare1, sharesimp1; dupshare without the pass)

The prototype's FloatIn.hs against the values-only one: the values-only version also requires `exprIsHNF` of each right-hand side.  The compilers named `dupshare` have the values-only FloatIn.hs and no simplifier pass.

```diff
diff --git a/compiler/GHC/Core/Opt/FloatIn.hs b/compiler/GHC/Core/Opt/FloatIn.hs
--- a/compiler/GHC/Core/Opt/FloatIn.hs
+++ b/compiler/GHC/Core/Opt/FloatIn.hs
@@ -822,8 +822,8 @@
             | is_case   = (n_alts > 1 && n_used_alts == n_alts)
                              -- Used in all, muliple branches, don't push
                           || (n_used_alts > 1 && not (floatIsDupable platform bind
-                                                      || small_enough))
-                             -- floatIsDupable, small_enough:
+                                                      || small_value))
+                             -- floatIsDupable, small_value:
                              -- see Note [Duplicating floats]
 
             | otherwise = floatIsCase bind || n_used_alts > 1
@@ -831,11 +831,11 @@
 
           -- Each copy shares what is left of the budget
           -- See Note [Duplicating floats]
-          copy_cost    = (n_used_alts - 1) * fromMaybe 0 (floatCopySize bind)
-          small_enough = isJust (floatCopySize bind) && copy_cost <= budget
-          copy         | n_used_alts > 1, small_enough
-                       = FB bndrs bind_fvs bind ((budget - copy_cost) `div` n_used_alts)
-                       | otherwise = bind_w_fvs
+          copy_cost   = (n_used_alts - 1) * fromMaybe 0 (floatValueSize bind)
+          small_value = isJust (floatValueSize bind) && copy_cost <= budget
+          copy        | n_used_alts > 1, small_value
+                      = FB bndrs bind_fvs bind ((budget - copy_cost) `div` n_used_alts)
+                      | otherwise = bind_w_fvs
 
           new_fork_boxes = zipWithEqual insert_maybe
                                         fork_boxes used_in_flags
@@ -861,17 +861,17 @@
 If the thing is used in all RHSs there is nothing gained,
 so we don't duplicate then.
 
-We also duplicate any let binding, a value or a thunk, if the code the
-copies add, (n-1) times its size for n alternatives, is within its
-budget: duplicating it into the alternatives that use it never
-duplicates work, since only one alternative runs and a binding that the
-scrutinee uses is not pushed, and it saves its allocation in the
-alternatives that don't use it.  The budget starts at the unfolding
-creation threshold and the copies share what is left of it, so nested
-cases cannot compound the duplication: in one float-in pass, all copies
-of a binding add at most the threshold.  (Not for join points, which
-are not allocated, nor for NOINLINE bindings.)  E.g. full laziness may
-float identical local functions out of three alternatives of
+We also duplicate a value binding (a function, partial application or
+constructor application) if the code the copies add, (n-1) times its
+size for n alternatives, is within its budget: duplicating it into the
+alternatives that use it never duplicates work, since only one
+alternative runs, and it saves its allocation in the alternatives that
+don't use it.  The budget starts at the unfolding creation threshold and
+the copies share what is left of it, so nested cases cannot compound the
+duplication: in one float-in pass, all copies of a binding add at most the
+threshold.  (Not for join points, which are not allocated, nor for NOINLINE
+bindings.)  E.g. full laziness may float identical local functions
+out of three alternatives of
      \x -> \t -> case t of { A ix -> ..go1.. ; B ix -> ..go2.. ; C -> 0 }
 when (\t) is still a separate lambda; if the function is later
 eta-expanded, CSE merges the copies, and without duplication the merged
@@ -881,17 +881,17 @@
 dupBudget :: Int
 dupBudget = unfoldingCreationThreshold defaultUnfoldingOpts
 
-floatCopySize :: FloatBind -> Maybe Int
--- The size of one copy, if the binding may be duplicated
-floatCopySize (FloatLet (NonRec b r))
-  | dup_ok b = Just (copySize r)
-floatCopySize (FloatLet (Rec prs))
-  | all (dup_ok . fst) prs
-  = Just (sum (map (copySize . snd) prs))
-floatCopySize _ = Nothing
+floatValueSize :: FloatBind -> Maybe Int
+-- The size of one copy, if the binding has values only and may be duplicated
+floatValueSize (FloatLet (NonRec b r))
+  | dup_ok b, exprIsHNF r = Just (valueSize r)
+floatValueSize (FloatLet (Rec prs))
+  | all (dup_ok . fst) prs, all (exprIsHNF . snd) prs
+  = Just (sum (map (valueSize . snd) prs))
+floatValueSize _ = Nothing
 
-copySize :: CoreExpr -> Int
-copySize r = case sizeExpr defaultUnfoldingOpts dupBudget [] (snd (collectBinders r)) of
+valueSize :: CoreExpr -> Int
+valueSize r = case sizeExpr defaultUnfoldingOpts dupBudget [] (snd (collectBinders r)) of
                 SizeIs { _es_size_is = s } -> s
                 TooBig                     -> dupBudget + 1
 
```

### Also pushing bindings that every alternative uses (headthunkall1, sharethunkall1)

Against the prototype's FloatIn.hs: the first disjunct of `cant_push` goes.

```diff
diff --git a/compiler/GHC/Core/Opt/FloatIn.hs b/compiler/GHC/Core/Opt/FloatIn.hs
--- a/compiler/GHC/Core/Opt/FloatIn.hs
+++ b/compiler/GHC/Core/Opt/FloatIn.hs
@@ -819,10 +819,8 @@
           n_used_alts = count id used_in_flags -- returns number of Trues in list.
 
           cant_push
-            | is_case   = (n_alts > 1 && n_used_alts == n_alts)
-                             -- Used in all, muliple branches, don't push
-                          || (n_used_alts > 1 && not (floatIsDupable platform bind
-                                                      || small_enough))
+            | is_case   = n_used_alts > 1 && not (floatIsDupable platform bind
+                                                    || small_enough)
                              -- floatIsDupable, small_enough:
                              -- see Note [Duplicating floats]
 
```

### The full simplifier pass (sharesimp)

Against the prototype's Pipeline.hs: `simplify` instead of one iteration.

```diff
diff --git a/compiler/GHC/Core/Opt/Pipeline.hs b/compiler/GHC/Core/Opt/Pipeline.hs
--- a/compiler/GHC/Core/Opt/Pipeline.hs
+++ b/compiler/GHC/Core/Opt/Pipeline.hs
@@ -283,10 +283,9 @@
                 -- succeed in commoning up things floated out by full laziness.
                 -- CSE used to rely on the no-shadowing invariant, but it doesn't any more
 
-        runWhen cse (simpl_phase FinalPhase "post-late-cse" 1),
-                -- One iteration: inline what CSE left used once (e.g. a function
-                -- only the merged copies called) before float-in duplicates the
-                -- merged copies.
+        runWhen cse (simplify "post-late-cse"),
+                -- Inline what CSE left used once (e.g. a function only the merged
+                -- copies called) before float-in duplicates the merged copies.
 
         runWhen do_float_in CoreDoFloatInwards,
 
```

### Float-in after the final simplifier instead (sharelate, guardlate; rejected)

Against HEAD: no extra pass, the late float-in moved after `simplify "final"`.  It fails T14152 and weakens a demand signature in T22241.

```diff
diff --git a/compiler/GHC/Core/Opt/Pipeline.hs b/compiler/GHC/Core/Opt/Pipeline.hs
--- a/compiler/GHC/Core/Opt/Pipeline.hs
+++ b/compiler/GHC/Core/Opt/Pipeline.hs
@@ -283,10 +283,12 @@
                 -- succeed in commoning up things floated out by full laziness.
                 -- CSE used to rely on the no-shadowing invariant, but it doesn't any more
 
-        runWhen do_float_in CoreDoFloatInwards,
-
         simplify "final",  -- Final tidy-up
 
+        runWhen do_float_in CoreDoFloatInwards,
+                -- After "final", which inlines what CSE left used once (e.g. a
+                -- function only the merged copies called) into its use.
+
         maybe_rule_check FinalPhase,
 
         --------  After this we have -O2 passes -----------------
```

## The size policies

Earlier policies, all on guard and without the simplifier pass.  The inline threshold (dupvalue) uses `couldBeSmallEnoughToInline`; the budget per case (dupbudget) checks `(n - 1) * size` against `unfoldingCreationThreshold`; the creation threshold (dupcreate) checks `size` alone.  The exclusion of join points and `NOINLINE` bindings (`dup_ok`) was added to all three sources after dupvalue's testsuite run, so every dupvalue measurement was made with a compiler built without it, which is why it failed T18903 and T26709 and cost T15630 4%; the dupvalue source without `dup_ok` is the instrument's source at the end of this appendix with its trace removed.

### dupvalue

```diff
diff --git a/compiler/GHC/Core/Opt/FloatIn.hs b/compiler/GHC/Core/Opt/FloatIn.hs
--- a/compiler/GHC/Core/Opt/FloatIn.hs
+++ b/compiler/GHC/Core/Opt/FloatIn.hs
@@ -23,13 +23,16 @@
 
 import GHC.Core
 import GHC.Core.Opt.Arity( isOneShotBndr )
+import GHC.Core.Opt.Simplify.Inline ( couldBeSmallEnoughToInline )
+import GHC.Core.Unfold ( defaultUnfoldingOpts, unfoldingUseThreshold )
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
@@ -816,8 +819,10 @@
           cant_push
             | is_case   = (n_alts > 1 && n_used_alts == n_alts)
                              -- Used in all, muliple branches, don't push
-                          || (n_used_alts > 1 && not (floatIsDupable platform bind))
-                             -- floatIsDupable: see Note [Duplicating floats]
+                          || (n_used_alts > 1 && not (floatIsDupable platform bind
+                                                      || floatIsSmallValue bind))
+                             -- floatIsDupable, floatIsSmallValue:
+                             -- see Note [Duplicating floats]
 
             | otherwise = floatIsCase bind || n_used_alts > 1
                              -- floatIsCase: see Note [Floating primops]
@@ -845,8 +850,35 @@
 
 If the thing is used in all RHSs there is nothing gained,
 so we don't duplicate then.
+
+We also duplicate a value binding (a function, partial application or
+constructor application) that is small enough to inline: duplicating it
+into the alternatives that use it never duplicates work, since only one
+alternative runs, and it saves its allocation in the alternatives that
+don't use it.  (Not for join points, which are not allocated, nor for
+NOINLINE bindings.)  E.g. full laziness may float identical local functions
+out of three alternatives of
+     \x -> \t -> case t of { A ix -> ..go1.. ; B ix -> ..go2.. ; C -> 0 }
+when (\t) is still a separate lambda; if the function is later
+eta-expanded, CSE merges the copies, and without duplication the merged
+function is allocated on every call, also for C.
 -}
 
+floatIsSmallValue :: FloatBind -> Bool
+floatIsSmallValue (FloatLet (NonRec b r)) = dup_ok b && small_value r
+floatIsSmallValue (FloatLet (Rec prs))    = all (\(b, r) -> dup_ok b && small_value r) prs
+floatIsSmallValue _                       = False
+
+small_value :: CoreExpr -> Bool
+small_value r = exprIsHNF r
+                && couldBeSmallEnoughToInline defaultUnfoldingOpts
+                     (unfoldingUseThreshold defaultUnfoldingOpts) r
+
+-- A join point is not allocated, so duplicating it saves nothing; and a
+-- NOINLINE binding is one the programmer wants to have a single copy of.
+dup_ok :: Id -> Bool
+dup_ok b = not (isJoinId b) && not (isNoInlinePragma (idInlinePragma b))
+
 floatedBindsFVs :: RevFloatInBinds -> FreeVarSet
 floatedBindsFVs binds = mapUnionDVarSet fbFVs binds
 
```

### dupbudget

```diff
diff --git a/compiler/GHC/Core/Opt/FloatIn.hs b/compiler/GHC/Core/Opt/FloatIn.hs
--- a/compiler/GHC/Core/Opt/FloatIn.hs
+++ b/compiler/GHC/Core/Opt/FloatIn.hs
@@ -23,13 +23,16 @@
 
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
@@ -816,8 +819,10 @@
           cant_push
             | is_case   = (n_alts > 1 && n_used_alts == n_alts)
                              -- Used in all, muliple branches, don't push
-                          || (n_used_alts > 1 && not (floatIsDupable platform bind))
-                             -- floatIsDupable: see Note [Duplicating floats]
+                          || (n_used_alts > 1 && not (floatIsDupable platform bind
+                                                      || floatIsSmallValue n_used_alts bind))
+                             -- floatIsDupable, floatIsSmallValue:
+                             -- see Note [Duplicating floats]
 
             | otherwise = floatIsCase bind || n_used_alts > 1
                              -- floatIsCase: see Note [Floating primops]
@@ -845,8 +850,42 @@
 
 If the thing is used in all RHSs there is nothing gained,
 so we don't duplicate then.
+
+We also duplicate a value binding (a function, partial application or
+constructor application) if the code the copies add, (n-1) times its
+size for n alternatives, is within the unfolding creation threshold:
+duplicating it into the alternatives that use it never duplicates work,
+since only one alternative runs, and it saves its allocation in the
+alternatives that don't use it.  (Not for join points, which are not allocated, nor for
+NOINLINE bindings.)  E.g. full laziness may float identical local functions
+out of three alternatives of
+     \x -> \t -> case t of { A ix -> ..go1.. ; B ix -> ..go2.. ; C -> 0 }
+when (\t) is still a separate lambda; if the function is later
+eta-expanded, CSE merges the copies, and without duplication the merged
+function is allocated on every call, also for C.
 -}
 
+floatIsSmallValue :: Int -> FloatBind -> Bool
+-- The binding has values only, and duplicating it n times adds at most
+-- one unfolding creation threshold of code.
+floatIsSmallValue n (FloatLet (NonRec b r)) = dup_ok b && small_values n [r]
+floatIsSmallValue n (FloatLet (Rec prs))    = all (dup_ok . fst) prs && small_values n (map snd prs)
+floatIsSmallValue _ _                       = False
+
+small_values :: Int -> [CoreExpr] -> Bool
+small_values n rs
+  = all exprIsHNF rs && (n - 1) * sum (map size rs) <= budget
+  where
+    budget = unfoldingCreationThreshold defaultUnfoldingOpts
+    size r = case sizeExpr defaultUnfoldingOpts budget [] (snd (collectBinders r)) of
+               SizeIs { _es_size_is = s } -> s
+               TooBig                     -> budget + 1
+
+-- A join point is not allocated, so duplicating it saves nothing; and a
+-- NOINLINE binding is one the programmer wants to have a single copy of.
+dup_ok :: Id -> Bool
+dup_ok b = not (isJoinId b) && not (isNoInlinePragma (idInlinePragma b))
+
 floatedBindsFVs :: RevFloatInBinds -> FreeVarSet
 floatedBindsFVs binds = mapUnionDVarSet fbFVs binds
 
```

### dupcreate, against dupbudget

```diff
diff --git a/compiler/GHC/Core/Opt/FloatIn.hs b/compiler/GHC/Core/Opt/FloatIn.hs
--- a/compiler/GHC/Core/Opt/FloatIn.hs
+++ b/compiler/GHC/Core/Opt/FloatIn.hs
@@ -866,15 +866,15 @@
 -}
 
 floatIsSmallValue :: Int -> FloatBind -> Bool
--- The binding has values only, and duplicating it n times adds at most
--- one unfolding creation threshold of code.
+-- The binding has values only, each of them within the unfolding creation
+-- threshold.
 floatIsSmallValue n (FloatLet (NonRec b r)) = dup_ok b && small_values n [r]
 floatIsSmallValue n (FloatLet (Rec prs))    = all (dup_ok . fst) prs && small_values n (map snd prs)
 floatIsSmallValue _ _                       = False
 
 small_values :: Int -> [CoreExpr] -> Bool
-small_values n rs
-  = all exprIsHNF rs && (n - 1) * sum (map size rs) <= budget
+small_values _n rs
+  = all exprIsHNF rs && sum (map size rs) <= budget
   where
     budget = unfoldingCreationThreshold defaultUnfoldingOpts
     size r = case sizeExpr defaultUnfoldingOpts budget [] (snd (collectBinders r)) of
```

## The float-out restrictions

All on guard. spine: GHC #15606's rule in the first float-out pass only; spineall: the same in every pass, which is this diff with `| le_spine env, not (floatOverSat env)` replaced by `| le_spine env`; spine2: only values; spine3: spine2 plus partial applications of the enclosing recursive group; coldalt: (SW2) of `Note [Saving work]` extended to let-bound values; funtop1: let-bound functions float only to top level in the first pass.

### spine

```diff
diff --git a/compiler/GHC/Core/Opt/SetLevels.hs b/compiler/GHC/Core/Opt/SetLevels.hs
--- a/compiler/GHC/Core/Opt/SetLevels.hs
+++ b/compiler/GHC/Core/Opt/SetLevels.hs
@@ -316,6 +316,22 @@
 will almost certainly be optimised away anyway.
 -}
 
+{- Note [Spine lambdas in the first float-out pass]
+~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
+A lambda on the spine of a right-hand side, separated from the binding's
+own lambdas only by lets and cases, as \y in
+    f = \x -> case g x of K -> \y -> ...
+is often absorbed into f's arity by eta-expansion later.  Floating out of
+it only pays if a partial application (f x) is shared, which, as for
+adjacent lambdas (see "We don't split adjacent lambdas" below), is rare;
+and if f is later eta-expanded, the floated bindings are allocated on
+every call, including the calls that never needed them.  The first
+float-out pass runs before arity analysis, so in that pass such a lambda
+starts no new major level; the late pass, which has accurate arity
+information, floats out of it if it survives.  (floatOverSat is False
+only in the first pass.)
+-}
+
 lvlExpr :: LevelEnv             -- Context
         -> CoreExprWithFVs      -- Input expression
         -> LvlM LevelledExpr    -- Result expression
@@ -351,7 +367,8 @@
     let tickish' = substTickish (le_subst env) tickish
     return (Tick tickish' expr')
 
-lvlExpr env expr@(_, AnnApp _ _) = lvlApp env expr (collectAnnArgs expr)
+lvlExpr env expr@(_, AnnApp _ _)
+  = lvlApp (env { le_spine = False }) expr (collectAnnArgs expr)
 
 -- We don't split adjacent lambdas.  That is, given
 --      \x y -> (x+1,y)
@@ -361,12 +378,17 @@
 -- lambdas makes them more expensive.
 
 lvlExpr env expr@(_, AnnLam {})
-  = do { new_body <- lvlNonTailMFE new_env True body
+  = do { new_body <- lvlNonTailMFE (new_env { le_spine = True }) True body
        ; return (mkLams new_bndrs new_body) }
   where
     (bndrs, body)        = collectAnnBndrs expr
     (env1, bndrs1)       = substBndrsSL NonRecursive env bndrs
-    (new_env, new_bndrs) = lvlLamBndrs env1 (le_ctxt_lvl env) bndrs1
+    (new_env, new_bndrs)
+      -- See Note [Spine lambdas in the first float-out pass]
+      | le_spine env, not (floatOverSat env)
+      = lvlBndrs env1 (incMinorLvl (le_ctxt_lvl env)) bndrs1
+      | otherwise
+      = lvlLamBndrs env1 (le_ctxt_lvl env) bndrs1
         -- At one time we called a special version of collectBinders,
         -- which ignored coercions, because we don't want to split
         -- a lambda like this (\x -> coerce t (\s -> ...))
@@ -383,7 +405,7 @@
        ; return (Let bind' body') }
 
 lvlExpr env (_, AnnCase scrut case_bndr ty alts)
-  = do { scrut' <- lvlNonTailMFE env True scrut
+  = do { scrut' <- lvlNonTailMFE (env { le_spine = False }) True scrut
        ; lvlCase env (freeVarsOf scrut) scrut' case_bndr ty alts }
 
 lvlNonTailExpr :: LevelEnv             -- Context
@@ -1475,7 +1497,7 @@
                       = collectNAnnBndrs join_arity rhs
                       | otherwise
                       = collectAnnBndrs rhs
-    (env1, bndrs1)    = substBndrsSL NonRecursive env bndrs
+    (env1, bndrs1)    = substBndrsSL NonRecursive (env { le_spine = True }) bndrs
     all_bndrs         = abs_vars ++ bndrs1
     (body_env, bndrs') | JoinPoint {} <- mb_join_arity
                       = lvlJoinBndrs env1 dest_lvl rec all_bndrs
@@ -1701,6 +1723,11 @@
                                         -- (since we want to substitute a LevelledExpr for
                                         -- an Id via le_env) but we do use the Co/TyVar substs
        , le_env      :: IdEnv ([OutVar], LevelledExpr)  -- Domain is pre-cloned Ids
+       , le_spine    :: Bool
+           -- True <=> on the spine of a binding's right-hand side, after its
+           -- own lambdas: reached through let bodies, case alternatives,
+           -- casts, ticks and lambda bodies only.
+           -- See Note [Spine lambdas in the first float-out pass]
     }
 
 {- Note [le_subst and le_env]
@@ -1740,7 +1767,8 @@
        , le_ctxt_lvl  = tOP_LEVEL
        , le_lvl_env   = emptyVarEnv
        , le_subst     = mkEmptySubst in_scope_toplvl
-       , le_env       = emptyVarEnv }
+       , le_env       = emptyVarEnv
+       , le_spine     = False }
   where
     in_scope_toplvl = emptyInScopeSet `extendInScopeSetBndrs` binds
       -- The Simplifier (see Note [Glomming] in GHC.Core.Opt.OccurAnal) and
```

### spine2

```diff
diff --git a/compiler/GHC/Core/Opt/SetLevels.hs b/compiler/GHC/Core/Opt/SetLevels.hs
--- a/compiler/GHC/Core/Opt/SetLevels.hs
+++ b/compiler/GHC/Core/Opt/SetLevels.hs
@@ -316,6 +316,27 @@
 will almost certainly be optimised away anyway.
 -}
 
+{- Note [Spine lambdas in the first float-out pass]
+~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
+A lambda on the spine of a right-hand side, separated from the binding's
+own lambdas only by lets and cases, as \y in
+    f = \x -> case g x of K -> \y -> ...
+is often absorbed into f's arity by eta-expansion later.  Floating a
+let-bound value (a function, a partial application or a constructor
+application) out of such a lambda saves only its allocation, and only if
+a partial application (f x) is shared, which, as for adjacent lambdas
+(see "We don't split adjacent lambdas" below), is rare; and if f is
+later eta-expanded, the floated value is allocated on every call,
+including the calls that never needed it.  So in the first float-out
+pass, which runs before arity analysis, a let-bound value does not
+float out of the nearest enclosing spine lambda, unless it goes to the
+top level (le_spine_lvl, used in lvlBind).  Work (a thunk or a redex)
+still floats out of it, because for a shared partial application that
+saves work, possibly unboundedly much.  The late pass, which has
+accurate arity information, floats values out of the lambda if it
+survives.  (floatOverSat is False only in the first pass.)
+-}
+
 lvlExpr :: LevelEnv             -- Context
         -> CoreExprWithFVs      -- Input expression
         -> LvlM LevelledExpr    -- Result expression
@@ -351,7 +372,8 @@
     let tickish' = substTickish (le_subst env) tickish
     return (Tick tickish' expr')
 
-lvlExpr env expr@(_, AnnApp _ _) = lvlApp env expr (collectAnnArgs expr)
+lvlExpr env expr@(_, AnnApp _ _)
+  = lvlApp (env { le_spine = False }) expr (collectAnnArgs expr)
 
 -- We don't split adjacent lambdas.  That is, given
 --      \x y -> (x+1,y)
@@ -361,12 +383,18 @@
 -- lambdas makes them more expensive.
 
 lvlExpr env expr@(_, AnnLam {})
-  = do { new_body <- lvlNonTailMFE new_env True body
+  = do { new_body <- lvlNonTailMFE body_env True body
        ; return (mkLams new_bndrs new_body) }
   where
     (bndrs, body)        = collectAnnBndrs expr
     (env1, bndrs1)       = substBndrsSL NonRecursive env bndrs
     (new_env, new_bndrs) = lvlLamBndrs env1 (le_ctxt_lvl env) bndrs1
+    body_env
+      -- See Note [Spine lambdas in the first float-out pass]
+      | le_spine env, not (floatOverSat env)
+      = new_env { le_spine = True, le_spine_lvl = le_ctxt_lvl new_env }
+      | otherwise
+      = new_env { le_spine = True }
         -- At one time we called a special version of collectBinders,
         -- which ignored coercions, because we don't want to split
         -- a lambda like this (\x -> coerce t (\s -> ...))
@@ -383,7 +411,7 @@
        ; return (Let bind' body') }
 
 lvlExpr env (_, AnnCase scrut case_bndr ty alts)
-  = do { scrut' <- lvlNonTailMFE env True scrut
+  = do { scrut' <- lvlNonTailMFE (env { le_spine = False }) True scrut
        ; lvlCase env (freeVarsOf scrut) scrut' case_bndr ty alts }
 
 lvlNonTailExpr :: LevelEnv             -- Context
@@ -1312,7 +1340,8 @@
     rhs_fvs    = freeVarsOf rhs
     bind_fvs   = rhs_fvs `unionDVarSet` dBndrFreeVars bndr
     abs_vars   = abstractVars dest_lvl env bind_fvs
-    dest_lvl   = destLevel env bind_fvs ty_fvs (isFunction rhs) is_bot_lam
+    dest_lvl   = spineClamp env (not is_bot_lam && exprIsHNF deann_rhs) $
+                 destLevel env bind_fvs ty_fvs (isFunction rhs) is_bot_lam
 
     deann_rhs  = deAnnotate rhs
     mb_bot_str = exprBotStrictness_maybe deann_rhs
@@ -1404,7 +1433,8 @@
                 bndrs
 
     ty_fvs   = foldr (unionVarSet . tyCoVarsOfType . idType) emptyVarSet bndrs
-    dest_lvl = destLevel env bind_fvs ty_fvs is_fun is_bot
+    dest_lvl = spineClamp env (all (exprIsHNF . deAnnotate) rhss) $
+               destLevel env bind_fvs ty_fvs is_fun is_bot
     abs_vars = abstractVars dest_lvl env bind_fvs
 
     is_top_bindable = not (any (mightBeUnliftedType . idType) bndrs)
@@ -1439,6 +1469,18 @@
   = True     -- Yes!  Float me
 
 
+-- | A let-bound value does not float out of the nearest enclosing spine
+-- lambda, unless to the top level.
+-- See Note [Spine lambdas in the first float-out pass]
+spineClamp :: LevelEnv -> Bool -> Level -> Level
+spineClamp env is_value dest_lvl
+  | is_value
+  , not (isTopLvl dest_lvl)
+  , dest_lvl `ltMajLvl` le_spine_lvl env
+  = le_spine_lvl env
+  | otherwise
+  = dest_lvl
+
 profitableFloat :: LevelEnv -> Level -> Bool
 profitableFloat env dest_lvl
   =  (dest_lvl `ltMajLvl` le_ctxt_lvl env)  -- Escapes a value lambda
@@ -1475,7 +1517,10 @@
                       = collectNAnnBndrs join_arity rhs
                       | otherwise
                       = collectAnnBndrs rhs
-    (env1, bndrs1)    = substBndrsSL NonRecursive env bndrs
+    spine_lvl | dest_lvl `ltMajLvl` le_spine_lvl env = tOP_LEVEL
+              | otherwise                            = le_spine_lvl env
+    (env1, bndrs1)    = substBndrsSL NonRecursive
+                          (env { le_spine = True, le_spine_lvl = spine_lvl }) bndrs
     all_bndrs         = abs_vars ++ bndrs1
     (body_env, bndrs') | JoinPoint {} <- mb_join_arity
                       = lvlJoinBndrs env1 dest_lvl rec all_bndrs
@@ -1701,6 +1746,15 @@
                                         -- (since we want to substitute a LevelledExpr for
                                         -- an Id via le_env) but we do use the Co/TyVar substs
        , le_env      :: IdEnv ([OutVar], LevelledExpr)  -- Domain is pre-cloned Ids
+       , le_spine    :: Bool
+           -- True <=> on the spine of a binding's right-hand side, after its
+           -- own lambdas: reached through let bodies, case alternatives,
+           -- casts, ticks and lambda bodies only.
+           -- See Note [Spine lambdas in the first float-out pass]
+       , le_spine_lvl :: Level
+           -- The level of the nearest enclosing spine lambda (first pass
+           -- only); tOP_LEVEL if none.
+           -- See Note [Spine lambdas in the first float-out pass]
     }
 
 {- Note [le_subst and le_env]
@@ -1740,7 +1794,9 @@
        , le_ctxt_lvl  = tOP_LEVEL
        , le_lvl_env   = emptyVarEnv
        , le_subst     = mkEmptySubst in_scope_toplvl
-       , le_env       = emptyVarEnv }
+       , le_env       = emptyVarEnv
+       , le_spine     = False
+       , le_spine_lvl = tOP_LEVEL }
   where
     in_scope_toplvl = emptyInScopeSet `extendInScopeSetBndrs` binds
       -- The Simplifier (see Note [Glomming] in GHC.Core.Opt.OccurAnal) and
```

### spine3

```diff
diff --git a/compiler/GHC/Core/Opt/SetLevels.hs b/compiler/GHC/Core/Opt/SetLevels.hs
--- a/compiler/GHC/Core/Opt/SetLevels.hs
+++ b/compiler/GHC/Core/Opt/SetLevels.hs
@@ -88,7 +88,7 @@
 import GHC.Core
 import GHC.Core.Opt.Monad ( FloatOutSwitches(..) )
 import GHC.Core.Utils
-import GHC.Core.Opt.Arity   ( exprBotStrictness_maybe, isOneShotBndr )
+import GHC.Core.Opt.Arity   ( exprBotStrictness_maybe, isOneShotBndr, exprIsDeadEnd )
 import GHC.Core.FVs     -- all of it
 import GHC.Core.Subst
 import GHC.Core.TyCo.Subst( lookupTyVar )
@@ -281,7 +281,8 @@
        ; return (NonRec bndr' rhs') }
 
 lvlTopBind env (Rec pairs)
-  = do { prs' <- mapM (\(b,r) -> lvl_top env Recursive b r) pairs
+  = do { let env' = extendRecSpine env pairs
+       ; prs' <- mapM (\(b,r) -> lvl_top env' Recursive b r) pairs
        ; return (Rec prs') }
 
 lvl_top :: LevelEnv -> RecFlag -> Id -> CoreExpr
@@ -316,6 +317,35 @@
 will almost certainly be optimised away anyway.
 -}
 
+{- Note [Spine lambdas in the first float-out pass]
+~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
+A lambda on the spine of a right-hand side, separated from the binding's
+own lambdas only by lets and cases, as \y in
+    f = \x -> case g x of K -> \y -> ...
+is often absorbed into f's arity by eta-expansion later.  Floating a
+let-bound value (a function, a partial application or a constructor
+application) out of such a lambda saves only its allocation, and only if
+a partial application (f x) is shared, which, as for adjacent lambdas
+(see "We don't split adjacent lambdas" below), is rare; and if f is
+later eta-expanded, the floated value is allocated on every call,
+including the calls that never needed it.  So in the first float-out
+pass, which runs before arity analysis, a let-bound value does not
+float out of the nearest enclosing spine lambda, unless it goes to the
+top level (le_spine_lvl, used in lvlBind).  Work (a thunk or a redex)
+still floats out of it, because for a shared partial application that
+saves work, possibly unboundedly much -- with one exception: a call to
+the enclosing recursive group with fewer value arguments than the
+callee's spine arity (its own lambdas plus its spine lambdas, see
+spineArity) counts as a partial application, not as work
+(le_rec_spine, used in lvlMFE).  Floating such a call out of a spine
+lambda can save at most the work before the callee's spine lambda; if
+that work is cheap, f is later eta-expanded and the call becomes a
+partial application allocated on every call; if it is not, the spine
+lambda survives and the late pass floats the call.  The late pass, which has
+accurate arity information, floats values out of the lambda if it
+survives.  (floatOverSat is False only in the first pass.)
+-}
+
 lvlExpr :: LevelEnv             -- Context
         -> CoreExprWithFVs      -- Input expression
         -> LvlM LevelledExpr    -- Result expression
@@ -351,7 +381,8 @@
     let tickish' = substTickish (le_subst env) tickish
     return (Tick tickish' expr')
 
-lvlExpr env expr@(_, AnnApp _ _) = lvlApp env expr (collectAnnArgs expr)
+lvlExpr env expr@(_, AnnApp _ _)
+  = lvlApp (env { le_spine = False }) expr (collectAnnArgs expr)
 
 -- We don't split adjacent lambdas.  That is, given
 --      \x y -> (x+1,y)
@@ -361,12 +392,18 @@
 -- lambdas makes them more expensive.
 
 lvlExpr env expr@(_, AnnLam {})
-  = do { new_body <- lvlNonTailMFE new_env True body
+  = do { new_body <- lvlNonTailMFE body_env True body
        ; return (mkLams new_bndrs new_body) }
   where
     (bndrs, body)        = collectAnnBndrs expr
     (env1, bndrs1)       = substBndrsSL NonRecursive env bndrs
     (new_env, new_bndrs) = lvlLamBndrs env1 (le_ctxt_lvl env) bndrs1
+    body_env
+      -- See Note [Spine lambdas in the first float-out pass]
+      | le_spine env, not (floatOverSat env)
+      = new_env { le_spine = True, le_spine_lvl = le_ctxt_lvl new_env }
+      | otherwise
+      = new_env { le_spine = True }
         -- At one time we called a special version of collectBinders,
         -- which ignored coercions, because we don't want to split
         -- a lambda like this (\x -> coerce t (\s -> ...))
@@ -383,7 +420,7 @@
        ; return (Let bind' body') }
 
 lvlExpr env (_, AnnCase scrut case_bndr ty alts)
-  = do { scrut' <- lvlNonTailMFE env True scrut
+  = do { scrut' <- lvlNonTailMFE (env { le_spine = False }) True scrut
        ; lvlCase env (freeVarsOf scrut) scrut' case_bndr ty alts }
 
 lvlNonTailExpr :: LevelEnv             -- Context
@@ -696,7 +733,7 @@
     float_me = saves_work || saves_alloc
 
     -- See Note [Saving work]
-    is_hnf = exprIsHNF expr
+    is_hnf = exprIsHNF expr || isSpinePap env expr
     saves_work = escapes_value_lam        -- (a)
                  && not is_hnf            -- (b)
                  && not float_is_new_lam  -- (c)
@@ -1312,7 +1349,8 @@
     rhs_fvs    = freeVarsOf rhs
     bind_fvs   = rhs_fvs `unionDVarSet` dBndrFreeVars bndr
     abs_vars   = abstractVars dest_lvl env bind_fvs
-    dest_lvl   = destLevel env bind_fvs ty_fvs (isFunction rhs) is_bot_lam
+    dest_lvl   = spineClamp env (not is_bot_lam && exprIsHNF deann_rhs) $
+                 destLevel env bind_fvs ty_fvs (isFunction rhs) is_bot_lam
 
     deann_rhs  = deAnnotate rhs
     mb_bot_str = exprBotStrictness_maybe deann_rhs
@@ -1332,7 +1370,8 @@
   = -- No float
     do { let bind_lvl       = incMinorLvl (le_ctxt_lvl env)
              (env', bndrs') = substAndLvlBndrs Recursive env bind_lvl bndrs
-             lvl_rhs (b,r)  = lvlRhs env' Recursive is_bot (idJoinPointHood b) r
+             lvl_rhs (b,r)  = lvlRhs (extendRecSpine env' rec_prs) Recursive is_bot
+                                     (idJoinPointHood b) r
        ; rhss' <- mapM lvl_rhs pairs
        ; return (Rec (bndrs' `zip` rhss'), env') }
 
@@ -1391,7 +1430,8 @@
                       -- function in a Rec, and we don't much care what
                       -- happens to it.  False is simple!
 
-    do_rhs env (_,rhs) = lvlFloatRhs abs_vars dest_lvl env Recursive
+    rec_prs = [ (b, deAnnotate r) | (b, r) <- pairs ]
+    do_rhs env (_,rhs) = lvlFloatRhs abs_vars dest_lvl (extendRecSpine env rec_prs) Recursive
                                      is_bot NotJoinPoint
                                      rhs
 
@@ -1404,7 +1444,8 @@
                 bndrs
 
     ty_fvs   = foldr (unionVarSet . tyCoVarsOfType . idType) emptyVarSet bndrs
-    dest_lvl = destLevel env bind_fvs ty_fvs is_fun is_bot
+    dest_lvl = spineClamp env (all (exprIsHNF . deAnnotate) rhss) $
+               destLevel env bind_fvs ty_fvs is_fun is_bot
     abs_vars = abstractVars dest_lvl env bind_fvs
 
     is_top_bindable = not (any (mightBeUnliftedType . idType) bndrs)
@@ -1439,6 +1480,53 @@
   = True     -- Yes!  Float me
 
 
+-- | A let-bound value does not float out of the nearest enclosing spine
+-- lambda, unless to the top level.
+-- See Note [Spine lambdas in the first float-out pass]
+spineClamp :: LevelEnv -> Bool -> Level -> Level
+spineClamp env is_value dest_lvl
+  | is_value
+  , not (isTopLvl dest_lvl)
+  , dest_lvl `ltMajLvl` le_spine_lvl env
+  = le_spine_lvl env
+  | otherwise
+  = dest_lvl
+
+-- | A call to the enclosing recursive group with fewer value arguments
+-- than the callee's spine arity.
+-- See Note [Spine lambdas in the first float-out pass]
+isSpinePap :: LevelEnv -> CoreExpr -> Bool
+isSpinePap env e
+  | (Var f, args) <- collectArgs e
+  , Just n <- lookupVarEnv (le_rec_spine env) f
+  = valArgCount args < n
+  | otherwise
+  = False
+
+-- | The number of value lambdas on the spine of a right-hand side: its
+-- own lambdas and the lambdas reached from them through let bodies,
+-- case alternatives (the minimum over the alternatives that do not
+-- diverge), casts and ticks.
+spineArity :: CoreExpr -> Int
+spineArity (Lam b e) | isId b    = 1 + spineArity e
+                     | otherwise = spineArity e
+spineArity (Let _ e)             = spineArity e
+spineArity (Cast e _)            = spineArity e
+spineArity (Tick _ e)            = spineArity e
+spineArity (Case _ _ _ alts)
+  = case [ spineArity rhs | Alt _ _ rhs <- alts, not (exprIsDeadEnd rhs) ] of
+      []     -> 0
+      n : ns -> foldr min n ns
+spineArity _                     = 0
+
+-- | In the first pass, record the spine arities of a recursive group.
+extendRecSpine :: LevelEnv -> [(Id, CoreExpr)] -> LevelEnv
+extendRecSpine env prs
+  | floatOverSat env = env
+  | otherwise
+  = env { le_rec_spine = extendVarEnvList (le_rec_spine env)
+                           [ (b, spineArity r) | (b, r) <- prs ] }
+
 profitableFloat :: LevelEnv -> Level -> Bool
 profitableFloat env dest_lvl
   =  (dest_lvl `ltMajLvl` le_ctxt_lvl env)  -- Escapes a value lambda
@@ -1475,7 +1563,10 @@
                       = collectNAnnBndrs join_arity rhs
                       | otherwise
                       = collectAnnBndrs rhs
-    (env1, bndrs1)    = substBndrsSL NonRecursive env bndrs
+    spine_lvl | dest_lvl `ltMajLvl` le_spine_lvl env = tOP_LEVEL
+              | otherwise                            = le_spine_lvl env
+    (env1, bndrs1)    = substBndrsSL NonRecursive
+                          (env { le_spine = True, le_spine_lvl = spine_lvl }) bndrs
     all_bndrs         = abs_vars ++ bndrs1
     (body_env, bndrs') | JoinPoint {} <- mb_join_arity
                       = lvlJoinBndrs env1 dest_lvl rec all_bndrs
@@ -1701,6 +1792,19 @@
                                         -- (since we want to substitute a LevelledExpr for
                                         -- an Id via le_env) but we do use the Co/TyVar substs
        , le_env      :: IdEnv ([OutVar], LevelledExpr)  -- Domain is pre-cloned Ids
+       , le_spine    :: Bool
+           -- True <=> on the spine of a binding's right-hand side, after its
+           -- own lambdas: reached through let bodies, case alternatives,
+           -- casts, ticks and lambda bodies only.
+           -- See Note [Spine lambdas in the first float-out pass]
+       , le_rec_spine :: IdEnv Int
+           -- Spine arities of the enclosing recursive groups (first pass
+           -- only), keyed by pre-cloned binders.
+           -- See Note [Spine lambdas in the first float-out pass]
+       , le_spine_lvl :: Level
+           -- The level of the nearest enclosing spine lambda (first pass
+           -- only); tOP_LEVEL if none.
+           -- See Note [Spine lambdas in the first float-out pass]
     }
 
 {- Note [le_subst and le_env]
@@ -1740,7 +1844,10 @@
        , le_ctxt_lvl  = tOP_LEVEL
        , le_lvl_env   = emptyVarEnv
        , le_subst     = mkEmptySubst in_scope_toplvl
-       , le_env       = emptyVarEnv }
+       , le_env       = emptyVarEnv
+       , le_spine     = False
+       , le_spine_lvl = tOP_LEVEL
+       , le_rec_spine = emptyVarEnv }
   where
     in_scope_toplvl = emptyInScopeSet `extendInScopeSetBndrs` binds
       -- The Simplifier (see Note [Glomming] in GHC.Core.Opt.OccurAnal) and
```

### coldalt

```diff
diff --git a/compiler/GHC/Core/Opt/SetLevels.hs b/compiler/GHC/Core/Opt/SetLevels.hs
--- a/compiler/GHC/Core/Opt/SetLevels.hs
+++ b/compiler/GHC/Core/Opt/SetLevels.hs
@@ -88,7 +88,7 @@
 import GHC.Core
 import GHC.Core.Opt.Monad ( FloatOutSwitches(..) )
 import GHC.Core.Utils
-import GHC.Core.Opt.Arity   ( exprBotStrictness_maybe, isOneShotBndr )
+import GHC.Core.Opt.Arity   ( exprBotStrictness_maybe, isOneShotBndr, exprIsDeadEnd )
 import GHC.Core.FVs     -- all of it
 import GHC.Core.Subst
 import GHC.Core.TyCo.Subst( lookupTyVar )
@@ -462,7 +462,13 @@
 
   | otherwise     -- Stays put
   = do { let (alts_env1, [case_bndr']) = substAndLvlBndrs NonRecursive env incd_lvl [case_bndr]
-             alts_env = extendCaseBndrEnv alts_env1 case_bndr scrut'
+             alts_env2 = extendCaseBndrEnv alts_env1 case_bndr scrut'
+             -- See Note [Let-bound values in case alternatives]
+             alts_env | length [ () | AnnAlt _ _ rhs <- alts
+                                    , not (exprIsDeadEnd (deAnnotate rhs)) ] >= 2
+                      = alts_env2 { le_alt_lvl = incd_lvl }
+                      | otherwise
+                      = alts_env2
        ; alts' <- mapM (lvl_alt alts_env) alts
        ; return (Case scrut' case_bndr' ty' alts') }
   where
@@ -828,6 +834,25 @@
 
 Hence `isTopLvl dest_lvl` in `saves_alloc`.
 
+Note [Let-bound values in case alternatives]
+~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
+(SW2) of Note [Saving work] applies to let-bound values too: floating a
+let-bound HNF (a function, a partial application or a constructor
+application) out of an alternative of a case with several alternatives
+allocates it whichever alternative is taken.  E.g.
+    f = \x -> \t -> case t of
+                     A ix -> let go = ...x... in go ix
+                     B ix -> let go = ...x... in go ix
+                     C    -> 0
+Floating the go's out of \t saves their allocation only if a partial
+application (f x) is shared; if f is eta-expanded instead (even later,
+after arity analysis), they are allocated on every call of f, also for C;
+and CSE then merges the identical copies, so that float-in can no longer
+sink them back.  So a let-bound HNF does not float out of an alternative
+of a case with two or more non-bottoming alternatives, unless it goes to
+the top level (le_alt_lvl, used in lvlBind).  It may still float out of
+lambdas inside the alternative.  Work (a thunk or a redex) still floats.
+
 Note [Floating to the top]
 ~~~~~~~~~~~~~~~~~~~~~~~~~~
 Even though Note [Saving allocation] suggests that we should not, in
@@ -1312,7 +1337,8 @@
     rhs_fvs    = freeVarsOf rhs
     bind_fvs   = rhs_fvs `unionDVarSet` dBndrFreeVars bndr
     abs_vars   = abstractVars dest_lvl env bind_fvs
-    dest_lvl   = destLevel env bind_fvs ty_fvs (isFunction rhs) is_bot_lam
+    dest_lvl   = altClamp env (not is_bot_lam && exprIsHNF deann_rhs) $
+                 destLevel env bind_fvs ty_fvs (isFunction rhs) is_bot_lam
 
     deann_rhs  = deAnnotate rhs
     mb_bot_str = exprBotStrictness_maybe deann_rhs
@@ -1404,7 +1430,8 @@
                 bndrs
 
     ty_fvs   = foldr (unionVarSet . tyCoVarsOfType . idType) emptyVarSet bndrs
-    dest_lvl = destLevel env bind_fvs ty_fvs is_fun is_bot
+    dest_lvl = altClamp env (all (exprIsHNF . deAnnotate) rhss) $
+               destLevel env bind_fvs ty_fvs is_fun is_bot
     abs_vars = abstractVars dest_lvl env bind_fvs
 
     is_top_bindable = not (any (mightBeUnliftedType . idType) bndrs)
@@ -1439,6 +1466,17 @@
   = True     -- Yes!  Float me
 
 
+-- | A let-bound value does not float out of a case alternative, unless to
+-- the top level.  See Note [Let-bound values in case alternatives]
+altClamp :: LevelEnv -> Bool -> Level -> Level
+altClamp env is_value dest_lvl
+  | is_value
+  , not (isTopLvl dest_lvl)
+  , dest_lvl `ltLvl` le_alt_lvl env
+  = le_alt_lvl env
+  | otherwise
+  = dest_lvl
+
 profitableFloat :: LevelEnv -> Level -> Bool
 profitableFloat env dest_lvl
   =  (dest_lvl `ltMajLvl` le_ctxt_lvl env)  -- Escapes a value lambda
@@ -1475,7 +1513,9 @@
                       = collectNAnnBndrs join_arity rhs
                       | otherwise
                       = collectAnnBndrs rhs
-    (env1, bndrs1)    = substBndrsSL NonRecursive env bndrs
+    alt_lvl | dest_lvl `ltLvl` le_alt_lvl env = tOP_LEVEL
+            | otherwise                       = le_alt_lvl env
+    (env1, bndrs1)    = substBndrsSL NonRecursive (env { le_alt_lvl = alt_lvl }) bndrs
     all_bndrs         = abs_vars ++ bndrs1
     (body_env, bndrs') | JoinPoint {} <- mb_join_arity
                       = lvlJoinBndrs env1 dest_lvl rec all_bndrs
@@ -1701,6 +1741,10 @@
                                         -- (since we want to substitute a LevelledExpr for
                                         -- an Id via le_env) but we do use the Co/TyVar substs
        , le_env      :: IdEnv ([OutVar], LevelledExpr)  -- Domain is pre-cloned Ids
+       , le_alt_lvl  :: Level
+           -- The level of the innermost enclosing alternative of a case with
+           -- several alternatives; tOP_LEVEL if none.
+           -- See Note [Let-bound values in case alternatives]
     }
 
 {- Note [le_subst and le_env]
@@ -1740,7 +1784,8 @@
        , le_ctxt_lvl  = tOP_LEVEL
        , le_lvl_env   = emptyVarEnv
        , le_subst     = mkEmptySubst in_scope_toplvl
-       , le_env       = emptyVarEnv }
+       , le_env       = emptyVarEnv
+       , le_alt_lvl   = tOP_LEVEL }
   where
     in_scope_toplvl = emptyInScopeSet `extendInScopeSetBndrs` binds
       -- The Simplifier (see Note [Glomming] in GHC.Core.Opt.OccurAnal) and
```

### funtop1

```diff
diff --git a/compiler/GHC/Core/Opt/SetLevels.hs b/compiler/GHC/Core/Opt/SetLevels.hs
--- a/compiler/GHC/Core/Opt/SetLevels.hs
+++ b/compiler/GHC/Core/Opt/SetLevels.hs
@@ -1282,7 +1282,7 @@
   |  isTyVar bndr  -- Don't float TyVar binders (simplifier gets rid of them pronto)
   || isCoVar bndr  -- Don't float CoVars: difficult to fix up CoVar occurrences
                    --                     (see extendPolyLvlEnv)
-  || not (wantToFloat env NonRecursive dest_lvl is_join is_top_bindable)
+  || not (wantToFloat env NonRecursive dest_lvl is_join is_top_bindable (isFunction rhs))
   = -- No float
     do { rhs' <- lvlRhs env NonRecursive is_bot_lam mb_join_arity rhs
        ; let  bind_lvl        = incMinorLvl (le_ctxt_lvl env)
@@ -1328,7 +1328,7 @@
     is_join       = isJoinPoint mb_join_arity
 
 lvlBind env (AnnRec pairs)
-  |  not (wantToFloat env Recursive dest_lvl is_join is_top_bindable)
+  |  not (wantToFloat env Recursive dest_lvl is_join is_top_bindable is_fun)
   = -- No float
     do { let bind_lvl       = incMinorLvl (le_ctxt_lvl env)
              (env', bndrs') = substAndLvlBndrs Recursive env bind_lvl bndrs
@@ -1417,12 +1417,20 @@
             -> Level    -- This is how far it could float
             -> Bool     -- Join point
             -> Bool     -- True <=> top-level-bindadable
+            -> Bool     -- True <=> the RHS is a function (value lambda)
             -> Bool     -- True <=> Yes! Float me
 
-wantToFloat env is_rec dest_lvl is_join is_top_bindable
+wantToFloat env is_rec dest_lvl is_join is_top_bindable is_fun
   | not (profitableFloat env dest_lvl)
   = False
 
+  -- Floating a function saves only the allocation of its closure, and only
+  -- if the lambdas it escapes are applied more than once.  The first pass
+  -- runs before arity analysis, so leave such floats to the late pass, as
+  -- for over-saturated applications (floatOverSat is False only early).
+  | is_fun, not (isTopLvl dest_lvl), not (floatOverSat env)
+  = False
+
   | floatTopLvlOnly env && not (isTopLvl dest_lvl)
   = False
 
```

## The CSE and pipeline alternatives

Their sources were edited in place and not kept, so only their description survives. fibcse: one more `runWhen do_float_in CoreDoFloatInwards` in `GHC.Core.Opt.Pipeline`, just before the late `runWhen cse CoreCSE`. cselam: `GHC.Core.Opt.CSE` doesn't common up the right-hand sides of local recursive let-bound lambdas.  Both on guard.

## !12121 rebased onto HEAD (headmr, mr12121)

!12121 as of its source branch `wip/T24466` at `f4d80f08e3` (updated 2026-08-10), applied to HEAD with two hunks resolved by hand: in `floatIsDupable` the merge request's equations replace HEAD's but keep HEAD's `FloatTick` equation, and in `postInlineUnconditionally` the `where` block, whose bindings had moved in HEAD, keeps only `is_demanded` and `uf_opts` inside the commented-out part. headmr is this on HEAD, mr12121 on guard, and headmrFI the same without the `GHC.Core.Opt.Simplify.Utils` part.

```diff
diff --git a/compiler/GHC/Core/Opt/FloatIn.hs b/compiler/GHC/Core/Opt/FloatIn.hs
--- a/compiler/GHC/Core/Opt/FloatIn.hs
+++ b/compiler/GHC/Core/Opt/FloatIn.hs
@@ -22,14 +22,19 @@
 import GHC.Platform
 
 import GHC.Core
+import GHC.Core.Unfold( ExprSize(..), sizeExpr,
+                        UnfoldingOpts(..), defaultUnfoldingOpts )
 import GHC.Core.Opt.Arity( isOneShotBndr )
+import GHC.Core.Opt.OccurAnal( occurAnalyseExpr )
+-- import GHC.Core.Opt.Simplify.Inline( smallEnoughToInline )
 import GHC.Core.Make hiding ( wrapFloats )
 import GHC.Core.Utils
 import GHC.Core.FVs
 import GHC.Core.Type
 
-import GHC.Types.Basic      ( RecFlag(..), isRec )
-import GHC.Types.Id         ( idType, isJoinId, idJoinPointHood )
+import GHC.Types.Basic      ( RecFlag(..), isRec, isOneOcc )
+import GHC.Types.Id         ( idType, isJoinId, idJoinPointHood, idDemandInfo, idOccInfo )
+import GHC.Types.Demand     ( isStrUsedDmd )
 import GHC.Types.Tickish
 import GHC.Types.Var
 import GHC.Types.Var.Set
@@ -50,10 +55,11 @@
 floatInwards platform binds = map (fi_top_bind platform) binds
   where
     fi_top_bind platform (NonRec binder rhs)
-      = NonRec binder (fiExpr platform [] (freeVars rhs))
+      = NonRec binder (fiExpr platform [] (preprocess rhs))
     fi_top_bind platform (Rec pairs)
-      = Rec [ (b, fiExpr platform [] (freeVars rhs)) | (b, rhs) <- pairs ]
+      = Rec [ (b, fiExpr platform [] (preprocess rhs)) | (b, rhs) <- pairs ]
 
+    preprocess rhs = freeVars (occurAnalyseExpr rhs)
 
 {-
 ************************************************************************
@@ -553,9 +559,14 @@
              all_alt_bndrs [scrut_fvs, all_alt_fvs]
              -- all_alt_bndrs: see Note [Shadowing and name capture]
 
-        -- Float into the alts with the is_case flag set
+    -- Float into the alts with the is_case flag set
+    -- Efficiency short-cut for the common case of a single alternative,
+    --   e.g.  case e of I# x -> blah
+    -- In that case just float in unconditionally.
     (drop_here2, alts_drops_s)
-       = sepBindsByDropPoint platform True alts_drops emptyDVarSet alts_fvs
+       = case alts of
+            [_] -> ([], [alts_drops])
+            _   -> sepBindsByDropPoint platform True alts_drops emptyDVarSet alts_fvs
 
     scrut_fvs = freeVarsOf scrut
 
@@ -680,7 +691,9 @@
       -- See Note [noFloatInto considerations] wrinkle 2
 
   | otherwise  -- See Note [noFloatInto considerations] wrinkle 2
-  = exprIsTrivial deann_expr || exprIsHNF deann_expr
+  = exprIsTrivial deann_expr -- || exprIsHNF deann_expr
+      -- let x = e in Just (Just (x+1))
+      -- here we want to float in!
   where
     deann_expr = deAnnotate' expr
 
@@ -785,8 +798,6 @@
   | otherwise
   = go floaters (initDropBox here_fvs) (map initDropBox fork_fvs)
   where
-    n_alts = length fork_fvs
-
     go :: RevFloatInBinds -> DropBox -> [DropBox]
        -> (RevFloatInBinds, [RevFloatInBinds])
         -- The *first* one in the pair is the drop_here set
@@ -795,10 +806,49 @@
         = (dropBoxFloats here_box, map dropBoxFloats fork_boxes)
 
     go (bind_w_fvs@(FB bndrs bind_fvs bind) : binds) here_box fork_boxes
-        | drop_here = go binds (insert here_box) fork_boxes
-        | otherwise = go binds here_box          new_fork_boxes
+        | push_it_in = go binds here_box          new_fork_boxes
+        | otherwise  = go binds (insert here_box) fork_boxes
         where
+          push_it_in = not used_here && can_push && (n_used_alts == 1 || some_benefit)
           -- "here" means the group of bindings dropped at the top of the fork
+          -- Otherwise always float in if there is just one arm; or if there is
+          -- some benefit to doing so
+
+          -- can_push: see Note [Floating primops]
+          can_push | is_case   = True
+                   | otherwise = not (floatIsCase bind)
+
+          -- some_benefit is used only if (n_used_alts > 1) and (not used_here)
+          -- So some duplication is going to occur
+          -- We want to push even if the thing is used in all branches. e.g.
+          --    let x = Just y in
+          --    case z of
+          --       True  -> case p of { True  -> x; False -> Nothing }
+          --       False -> case p of { False -> x; True  -> Nothing }
+          -- Here `x` is used in the both branches of the outer `case`,
+          -- but we still really want to push it in
+          some_benefit = small_enough &&
+                         no_work_duplication &&
+                         not strict_thunk
+
+          small_enough = floatIsDupable platform bind
+
+          -- no_work_duplication includes no duplication of /allocation/
+          -- For case-expressions this is true by construction (is_case)
+          -- But in all other situations we need to be careful e.g.
+          --     let x = Just y in f x x
+          -- Don't duplicate the (x = Just y) into the two arguments!
+          --
+          -- But if occurence analysis says "used once", we /can/ float in.  e.g.
+          --     let x = Just y in
+          --     join $j z = ...x...
+          --     in case v of { A -> $j 1; B -> $j 2; C -> x }
+          -- Here we can float into the RHS of the join point and the arms of the case
+          -- See Note [Occurrence analysis for join points] in GHC.Core.Opt.OccurAnal
+          no_work_duplication = is_case || case bind of
+                                  FloatCase {}          -> True   -- Always a primop
+                                  FloatLet (NonRec b _) -> isOneOcc (idOccInfo b)
+                                  FloatLet (Rec {})     -> False  -- One will be a loop breaker
 
           used_here     = bndrs `usedInDropBox` here_box
           used_in_flags = case fork_boxes of
@@ -809,18 +859,16 @@
                -- Short-cut for the singleton case;
                -- used for lambdas and singleton cases
 
-          drop_here = used_here || cant_push
-
           n_used_alts = count id used_in_flags -- returns number of Trues in list.
 
-          cant_push
-            | is_case   = (n_alts > 1 && n_used_alts == n_alts)
-                             -- Used in all, muliple branches, don't push
-                          || (n_used_alts > 1 && not (floatIsDupable platform bind))
-                             -- floatIsDupable: see Note [Duplicating floats]
-
-            | otherwise = floatIsCase bind || n_used_alts > 1
-                             -- floatIsCase: see Note [Floating primops]
+          -- A demanded thunk like  let x = factorial y in ... could be pushed, but
+          -- it'll turn into a case-expression so it doesn't allocate directly.
+          -- So I am experimenting with making it stay put.
+          strict_thunk = case bind of
+                           FloatCase{}           -> False
+                           FloatLet (Rec {})     -> False
+                           FloatLet (NonRec b r) -> isStrUsedDmd (idDemandInfo b)
+                                                    && not (exprIsHNF r)
 
           new_fork_boxes = zipWithEqual insert_maybe
                                         fork_boxes used_in_flags
@@ -832,19 +880,19 @@
           insert_maybe box False = box
 
 
-{- Note [Duplicating floats]
-~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-For case expressions we duplicate the binding if it is reasonably
-small, and if it is not used in all the RHSs This is good for
-situations like
+{- Note [Duplicating floats into case alternatives]
+~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
+For case expressions (is_case = True) it is safe to float the bining into all
+RHSs, without duplicating work.  But it might duplicate code.  So we refrain if
+* It is used in all alternatives
+* It is used in multiple alternatives, and is not small (floatIsDupable)
+
+This is good for situations like
      let x = I# y in
      case e of
        C -> error x
        D -> error x
        E -> ...not mentioning x...
-
-If the thing is used in all RHSs there is nothing gained,
-so we don't duplicate then.
 -}
 
 floatedBindsFVs :: RevFloatInBinds -> FreeVarSet
@@ -859,10 +907,26 @@
 wrapFloats (FB _ _ fl : bs) e = wrapFloats bs (wrapFloat fl e)
 
 floatIsDupable :: Platform -> FloatBind -> Bool
-floatIsDupable platform (FloatCase scrut _ _ _) = exprIsDupable platform scrut
-floatIsDupable platform (FloatLet (Rec prs))    = all (exprIsDupable platform . snd) prs
-floatIsDupable platform (FloatLet (NonRec _ r)) = exprIsDupable platform r
-floatIsDupable _        (FloatTick t)           = pprPanic "floatIsDupable" (ppr t)
+floatIsDupable _ (FloatCase scrut _ _ _) = small_enough_e scrut
+floatIsDupable _ (FloatLet bind)         = bindIsDupable bind
+floatIsDupable _ (FloatTick t)           = pprPanic "floatIsDupable" (ppr t)
+
+bindIsDupable :: CoreBind -> Bool
+bindIsDupable bind
+  | isJoinBind bind        = False  -- No point in duplicating join points
+bindIsDupable (Rec prs)    = all small_enough_b prs
+bindIsDupable (NonRec b r) = small_enough_b (b,r)
+
+small_enough_b :: (Id,CoreExpr) -> Bool
+small_enough_b (_,rhs) = small_enough_e rhs
+
+small_enough_e :: CoreExpr -> Bool
+small_enough_e e
+  = case sizeExpr opts (unfoldingUseThreshold opts) [] e of
+      TooBig    -> False
+      SizeIs {} -> True
+  where
+    opts = defaultUnfoldingOpts
   -- FloatTick: whether it is safe to float a tick inwards should reallly depend
   -- on the kind of tick.  But in fact FloatIn never floats ticks at all, so
   -- this case can't happen.  Hence the panic, which is at least simple.
diff --git a/compiler/GHC/Core/Opt/Pipeline.hs b/compiler/GHC/Core/Opt/Pipeline.hs
--- a/compiler/GHC/Core/Opt/Pipeline.hs
+++ b/compiler/GHC/Core/Opt/Pipeline.hs
@@ -313,8 +313,11 @@
         -- off one layer of a recursive function (concretely, I saw this
         -- in wheel-sieve1), and I'm guessing that SpecConstr can too
         -- And CSE is a very cheap pass. So it seems worth doing here.
-        runWhen ((liberate_case || spec_constr) && cse) $ CoreDoPasses
-           [ CoreCSE, simplify "post-final-cse" ],
+        -- Also SpecConstr yields new FloatIn possibilities
+        runWhen (liberate_case || spec_constr) $ CoreDoPasses
+           [ runWhen cse CoreCSE
+           , runWhen do_float_in CoreDoFloatInwards
+           , runWhen (cse || do_float_in) $ simplify "post-O2" ],
 
         ---------  End of -O2 passes --------------
 
diff --git a/compiler/GHC/Core/Opt/Simplify/Utils.hs b/compiler/GHC/Core/Opt/Simplify/Utils.hs
--- a/compiler/GHC/Core/Opt/Simplify/Utils.hs
+++ b/compiler/GHC/Core/Opt/Simplify/Utils.hs
@@ -49,7 +49,7 @@
 import GHC.Core
 import GHC.Types.Literal ( isLitRubbish )
 import GHC.Core.Opt.Simplify.Env
-import GHC.Core.Opt.Simplify.Inline( smallEnoughToInline )
+-- import GHC.Core.Opt.Simplify.Inline( smallEnoughToInline )
 import GHC.Core.Opt.Stats ( Tick(..) )
 import qualified GHC.Core.Subst
 import GHC.Core.Ppr
@@ -1821,6 +1821,10 @@
                                         --     in GHC.Core.Opt.Simplify.Iteration
   | otherwise
   = case occ_info of
+      OneOcc { occ_in_lam = in_lam, occ_n_br = n_br }
+        | n_br == 1, NotInsideLam <- in_lam  -- One syntactic occurrence
+        -> True                              -- See Note [Post-inline for single-use things]
+{-
       OneOcc { occ_in_lam = in_lam, occ_int_cxt = int_cxt, occ_n_br = n_br }
         -- See Note [Inline small things to avoid creating a thunk]
 
@@ -1843,7 +1847,7 @@
         -> work_ok in_lam int_cxt && (n_br == 1 || smallEnoughToInline uf_opts unfolding)
               -- Multiple syntactic occurences; but lazy, and small enough to dup
               -- ToDo: consider discount on smallEnoughToInline if int_cxt is true
-
+-}
       IAmDead -> True   -- This happens; for example, the case_bndr during case of
                         -- known constructor:  case (a,b) of x { (p,q) -> ... }
                         -- Here x isn't mentioned in the RHS, so we don't want to
@@ -1852,6 +1856,12 @@
       _ -> False
 
   where
+    occ_info    = idOccInfo old_bndr
+    unfolding   = idUnfolding bndr
+    phase       = sePhase env
+    active      = isActive phase (idInlineActivation bndr)
+        -- See Note [pre/postInlineUnconditionally in gentle mode]
+{-
     work_ok NotInsideLam _              = True
     work_ok IsInsideLam  IsInteresting  = isCheapUnfolding unfolding
     work_ok IsInsideLam  NotInteresting = False
@@ -1869,11 +1879,8 @@
 
 --    is_unlifted = isUnliftedType (idType bndr)
     is_demanded = isStrUsedDmd (idDemandInfo bndr)
-    occ_info    = idOccInfo old_bndr
-    unfolding   = idUnfolding bndr
     uf_opts     = seUnfoldingOpts env
-    active      = isActive (sePhase env) $ idInlineActivation bndr
-        -- See Note [pre/postInlineUnconditionally in gentle mode]
+-}
 
 {- Note [Inline small things to avoid creating a thunk]
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```

## The instrument (dvdbg2)

The inline-threshold policy as measured, without `dup_ok`, with a `pprTrace` of each binding float-in considers duplicating, its use counts and its size; used to read the sizes of the floated functions.

```diff
diff --git a/compiler/GHC/Core/Opt/FloatIn.hs b/compiler/GHC/Core/Opt/FloatIn.hs
--- a/compiler/GHC/Core/Opt/FloatIn.hs
+++ b/compiler/GHC/Core/Opt/FloatIn.hs
@@ -23,6 +23,8 @@
 
 import GHC.Core
 import GHC.Core.Opt.Arity( isOneShotBndr )
+import GHC.Core.Opt.Simplify.Inline ( couldBeSmallEnoughToInline )
+import GHC.Core.Unfold ( defaultUnfoldingOpts, unfoldingUseThreshold, sizeExpr )
 import GHC.Core.Make hiding ( wrapFloats )
 import GHC.Core.Utils
 import GHC.Core.FVs
@@ -36,6 +38,7 @@
 
 import GHC.Utils.Misc
 import GHC.Utils.Panic
+import GHC.Utils.Trace ( pprTrace )
 
 import GHC.Utils.Outputable
 
@@ -809,15 +812,23 @@
                -- Short-cut for the singleton case;
                -- used for lambdas and singleton cases
 
-          drop_here = used_here || cant_push
+          drop_here = used_here || cant_push_dbg
+          cant_push_dbg
+            | is_case, n_used_alts > 1
+            = pprTrace "dupvalue" (ppr (dVarSetElems bndrs) <+> ppr n_used_alts <+> ppr n_alts
+                                   <+> ppr (floatIsSmallValue bind) <+> ppr used_here
+                                   <+> ppr cant_push <+> dbg_bind bind) cant_push
+            | otherwise = cant_push
 
           n_used_alts = count id used_in_flags -- returns number of Trues in list.
 
           cant_push
             | is_case   = (n_alts > 1 && n_used_alts == n_alts)
                              -- Used in all, muliple branches, don't push
-                          || (n_used_alts > 1 && not (floatIsDupable platform bind))
-                             -- floatIsDupable: see Note [Duplicating floats]
+                          || (n_used_alts > 1 && not (floatIsDupable platform bind
+                                                      || floatIsSmallValue bind))
+                             -- floatIsDupable, floatIsSmallValue:
+                             -- see Note [Duplicating floats]
 
             | otherwise = floatIsCase bind || n_used_alts > 1
                              -- floatIsCase: see Note [Floating primops]
@@ -845,8 +856,36 @@
 
 If the thing is used in all RHSs there is nothing gained,
 so we don't duplicate then.
+
+We also duplicate a value binding (a function, partial application or
+constructor application) that is small enough to inline: duplicating it
+into the alternatives that use it never duplicates work, since only one
+alternative runs, and it saves its allocation in the alternatives that
+don't use it.  E.g. full laziness may float identical local functions
+out of three alternatives of
+     \x -> \t -> case t of { A ix -> ..go1.. ; B ix -> ..go2.. ; C -> 0 }
+when (\t) is still a separate lambda; if the function is later
+eta-expanded, CSE merges the copies, and without duplication the merged
+function is allocated on every call, also for C.
 -}
 
+dbg_bind :: FloatBind -> SDoc
+dbg_bind (FloatLet (Rec prs)) = vcat [ text "HNF" <+> ppr (exprIsHNF r) <+> text "small" <+> ppr (small_value r)
+                                       <+> text "size" <+> ppr (sizeExpr defaultUnfoldingOpts 1000 [] (snd (collectBinders r)))
+                                       $$ ppr r | (_, r) <- prs ]
+dbg_bind (FloatLet (NonRec _ r)) = text "NonRec HNF" <+> ppr (exprIsHNF r) <+> text "size" <+> ppr (sizeExpr defaultUnfoldingOpts 1000 [] (snd (collectBinders r))) $$ ppr r
+dbg_bind _ = text "other"
+
+floatIsSmallValue :: FloatBind -> Bool
+floatIsSmallValue (FloatLet (NonRec _ r)) = small_value r
+floatIsSmallValue (FloatLet (Rec prs))    = all (small_value . snd) prs
+floatIsSmallValue _                       = False
+
+small_value :: CoreExpr -> Bool
+small_value r = exprIsHNF r
+                && couldBeSmallEnoughToInline defaultUnfoldingOpts
+                     (unfoldingUseThreshold defaultUnfoldingOpts) r
+
 floatedBindsFVs :: RevFloatInBinds -> FreeVarSet
 floatedBindsFVs binds = mapUnionDVarSet fbFVs binds
 
```
