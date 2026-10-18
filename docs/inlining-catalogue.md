# GHC HEAD's inlining rules and exceptions: a catalogue with repros

Made 2026-10-15--2026-10-18 from our record of inlining observations. The catalogue gives, from GHC's source and from that record, whether GHC inlines a visible unfolding at a call (section 1), how eta-expansion and saturation change where a binding is inlined (section 2), how INLINE, INLINABLE and no pragma change the code (section 3), and which unfolding a call gets, the stable one, made from the right-hand side as written, or the vanilla one, made from the optimised right-hand side, and when either is the better (section 4), each with a minimal repro where one was found. Section 5 lists the rules read but given no entry; section 6 lists the places in inlining where GHC's text and code disagree or its behaviour may be unintended; and an appendix states how inlining meets specialisation, without repros. Each entry states one of GHC's rules: the rule set is so granular that every rule reads almost as a singular exception, or perhaps only looks singular to us because the rules are so arcane; where an entry gives an exception, it is an exception to a rule the entry states, as we guess it.

The compiler is GHC HEAD alone (Mikolaj, 2026-10-15): 10.1.20260918 at `~/r/horde-ad/ghc/_build/stage1/bin/ghc`, built from the working tree of `~/r/horde-ad/ghc`, branch `wip/T27737`: master e2d5702699 plus commits 0f0d5c45c8 ("Don't push `case` inside `let` in Gentle simplification"), 9111295d4d and 6913545fd3, and uncommitted patches to [compiler/GHC/Core/Map/Expr.hs][g1] (the proposed fix of GHC [#27892](https://gitlab.haskell.org/ghc/ghc/-/work_items/27892)), [Core/Opt/Simplify/Iteration.hs][g2] (of GHC [#27885](https://gitlab.haskell.org/ghc/ghc/-/work_items/27885)), [Core/Opt/Specialise.hs][g3] (of GHC [#27873](https://gitlab.haskell.org/ghc/ghc/-/work_items/27873) and GHC [#27880](https://gitlab.haskell.org/ghc/ghc/-/work_items/27880)) and [Core/Utils.hs][g4] (of GHC [#27874](https://gitlab.haskell.org/ghc/ghc/-/work_items/27874)), each compiled into the binary after its last edit. The working tree also patches the RTS header rts/include/rts/prof/LDV.h, defining `PROF_HEADER_CREATE` as nothing in a build without profiling. Source citations link to lines of commit 6913545fd3, published on GitLab as `wip/T27737`, with the function or Note name beside each, the name being what survives a line moving; a line only the uncommitted patches carry is named as the patch's, unlinked, with its line number in the working tree. An entry names the patch where one bears on it.

## Contents

- [How to read an entry](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#how-to-read-an-entry)
- [The decision whether to inline an occurrence, in brief](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#the-decision-whether-to-inline-an-occurrence-in-brief)
- [1. Whether a visible unfolding is inlined at a call](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#1-whether-a-visible-unfolding-is-inlined-at-a-call)
  - [A01. At an exactly saturated, boring call with trivial arguments, an INLINE body must be tiny](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a01-an-inline-function-at-an-exactly-saturated-call-with-trivial-arguments-in-a-boring-context-is-inlined-only-if-its-body-is-tiny-judged-after-its-template-is-simplified)
  - [A02. A pragma-free body no bigger than its call is inlined at every call giving it a value argument](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a02-a-binding-without-a-pragma-whose-body-is-no-bigger-than-its-call-is-inlined-at-every-call-giving-it-a-value-argument-partial-calls-included-which-inline-can-undo)
  - [A03. Without INLINE, a body bigger than its call needs an interesting argument or context](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a03-a-function-without-inline-and-bigger-than-its-call-is-inlined-only-where-some-argument-or-the-context-is-interesting-however-small-it-is)
  - [A04. Without INLINE, a body bigger than its call must fit `-funfolding-use-threshold` after discount](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a04-without-inline-a-body-bigger-than-its-call-is-inlined-only-if-its-size-less-the-calls-discounts-is-at-most--funfolding-use-threshold-90-by-default)
  - [A05. INLINE has no size limit; else a body past the creation threshold needs `inline` or one use](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a05-inline-is-taken-whatever-the-bodys-size-without-it-a-body-past-the-creation-threshold-is-inlined-at-a-call-only-by-inline-a13-unless-the-call-is-its-only-occurrence-a16)
  - [A06. Without INLINE, only work-free unfoldings are inlined at calls; nullary INLINE ones at any use](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a06-without-inline-only-a-work-free-unfolding-is-inlined-at-a-call-a-binding-with-no-arguments-under-inline-is-inlined-at-every-use)
  - [A07. An argument earns its discount only as a value; a call or merely evaluated variable earns 10](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a07-an-argument-earns-its-discount-only-as-a-value-a-call-or-a-merely-evaluated-variable-earns-10-a-lambda-bound-variable-nothing)
  - [A08. The call's context is taken from its continuation, and some strict positions count as boring](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a08-the-calls-context-is-taken-from-its-continuation-and-some-strict-positions-count-as-boring)
  - [A09. Without INLINE, a body bigger than its call pays a penalty at calls deep in multi-way cases](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a09-without-inline-a-call-of-a-body-bigger-than-the-call-nested-in-more-than--funfolding-case-threshold-multi-way-cases-2-by-default-pays-a-size-penalty-growing-with-the-depth)
  - [A10. An unfolding is inactive outside its pragma's phases; NOINLINE's `[k]`, `[~k]` match INLINE's](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a10-a-phase-on-a-pragma-makes-the-unfolding-inactive-outside-its-phases-k-and-k-mean-the-same-for-noinline-as-for-inline)
  - [A11. A loop breaker is inlined only by `inline`; INLINE bindings are among the last picked as one](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a11-a-loop-breaker-is-inlined-only-by-inline-a13-inline-or-not-in-its-module-or-an-importer-in-a-recursive-group-inline-bindings-are-among-the-last-chosen)
  - [A12. Rules are tried first, on unsimplified arguments; one needing them simplified loses to inlining](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a12-at-a-call-rules-are-tried-before-inlining-on-the-arguments-as-written-a-rule-that-needs-the-arguments-simplified-loses-to-an-active-unfolding)
  - [A13. `inline f` substitutes `f`'s unfolding whatever its guidance; once `f` is split, the wrapper's](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a13-inline-f-substitutes-fs-unfolding-as-it-is-when-the-rule-fires-whatever-its-guidance-a-loop-breakers-too-if-f-has-one-and-built-in-rules-are-on-once-workerwrapper-has-split-f-that-is-the-wrapper-alone)
  - [A14. `noinline f` only leaves `f` unapplied, so a nullary INLINE binding is inlined through it](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a14-noinline-f-blocks-inlining-only-because-f-is-then-applied-to-no-value-argument-an-inline-binding-with-no-arguments-is-inlined-through-it)
  - [A15. A dictionary function is inlined only if its class is unary; else a rule selects its methods](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a15-a-dictionary-function-is-inlined-only-if-its-class-is-unary-its-methods-otherwise-selected-by-a-rule)
  - [A16. A binding used once outside a lambda is pre-inlined unless INLINE, in a stable unfolding, etc.](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a16-a-binding-that-occurs-once-outside-a-lambda-or-applied-inside-one-when-its-right-hand-side-is-trivial-or-a-lambda-is-substituted-before-it-is-simplified-whatever-its-size-with-exceptions-chief-among-them-inline-and-an-occurrence-inside-a-stable-unfolding)
  - [A17. A small local let used at most once per branch is copied there, into a lambda only if work-free](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a17-after-simplifying-a-local-let-a-small-right-hand-side-used-at-most-once-in-each-branch-is-copied-into-the-branches-using-it-but-into-a-lambda-only-when-work-free-and-in-an-interesting-position-and-never-at-top-level)
  - [A18. A19 apart, join points are inlined only for discounted values or more evaluated free variables](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a18-apart-from-a19s-cases-a-join-point-is-inlined-at-a-jump-only-where-an-argument-the-body-scrutinises-or-applies-is-a-value-or-a-free-variable-is-more-evaluated-there-interesting-arguments-are-not-enough)
  - [A19. A join point is inlined unconditionally only if trivial, a jump or a closed application](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a19-a-join-point-is-inlined-unconditionally-only-if-its-body-is-trivial-a-jump-or-an-application-without-free-variables)
  - [A20. An exit join point without a stable unfolding is never inlined back into its loop](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a20-an-exit-join-point-without-a-stable-unfolding-is-never-inlined-back-into-its-loop)
  - [A21. A lone scrutinee with an expandable unfolding is not inlined; the case is resolved through it](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a21-a-variable-scrutinised-alone-with-an-expandable-unfolding-is-not-inlined-the-case-is-resolved-through-the-unfolding-instead)
  - [A22. CONLIKE lets a rule match through a variable bound to a call, without inlining the variable](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a22-conlike-lets-a-rule-match-through-a-variable-bound-to-a-call-without-inlining-the-variable)
  - [A23. A top-level function known to diverge is not inlined, unless it is no bigger than its call](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a23-a-top-level-function-known-to-diverge-is-not-inlined-unless-it-is-no-bigger-than-its-call)
  - [A24. NOINLINE keeps a function's body out of callers, not its wrapper; OPAQUE also blocks the split](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a24-noinline-keeps-a-functions-body-out-of-its-callers-but-not-its-workerwrapper-wrapper-which-is-inlined-in-the-final-phase-opaque-keeps-the-call-itself-unsplit)
  - [A25. Constructor wrappers are inlined only in the final phase, unpacking ones not at boring calls](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a25-a-data-constructors-wrapper-is-inlined-only-in-the-final-phase-and-one-that-unpacks-a-field-not-in-a-boring-context)
  - [A26. A worker/wrapper wrapper is inlined only at interesting calls, not before phase 2 and its rules](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a26-a-workerwrapper-wrapper-gets-an-always-inline-stable-unfolding-active-from-phase-2-or-later-after-the-functions-rules-and-is-inlined-only-where-an-argument-or-the-context-is-interesting)
  - [A27. In an interface unfolding, a function imported through an hs-boot file is wrapped in `noinline`](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a27-in-an-unfolding-written-to-an-interface-a-function-imported-through-an-hs-boot-file-is-wrapped-in-noinline)
  - [A28. A derived Generic instance's `from` and `to` get INLINE [1] when the type is small](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a28-a-derived-generic-instances-from-and-to-get-inline-1-when-the-type-is-small)
  - [A29. INLINE copies a `typeRep` dispatch into callers, where only the matching branch keeps a body](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a29-inline-on-a-dispatcher-over-typerep-copies-the-case-into-every-caller-where-the-comparisons-stay-but-become-constants-and-only-the-matching-branch-keeps-a-body)
  - [A30. A default recursing via a method-level dictionary is no loop breaker: INLINE inlines it forever](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a30-a-default-method-recursing-through-its-own-method-level-dictionary-is-no-loop-breaker-under-inline-an-importer-at-known-dictionaries-inlines-it-without-end-under-inlinable-it-specialises-it)
  - [A31. `-g`'s source notes stop exitification, and floated literals stay apart under them](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a31--g-wraps-expressions-in-source-notes-at-which-exitification-stops-and-under-which-floated-literals-stay-apart)
  - [A32. `-funfolding-use-threshold=0` stops size-judged inlining but not INLINE or wrapper inlining](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a32--funfolding-use-threshold0-leaves-inline-and-wrapper-unfoldings-inlining-but-stops-the-size-judged-ones-so-what-they-would-have-brought-into-the-client-bases-eqint-and-friends-among-it-stays-in-the-librarys-compiled-code)
  - [A33. INLINE copies each `HasCallStack` call a function makes into each caller as a static stack node](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a33-inline-on-a-hascallstack-function-copies-each-hascallstack-call-it-makes-into-every-caller-as-a-static-call-stack-node-cse-merges-the-inlined-copies-that-hold-no-stack-unless-each-shares-a-recursive-group-with-what-floats-out-of-it)
  - [A34. With an `error` check, a wrapper forces an argument first; a body inlined whole checks first](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#a34-a-check-that-fails-with-error-makes-its-function-strict-in-what-only-the-other-branch-uses-called-through-a-workerwrapper-split-the-function-forces-that-first-and-inlined-whole-it-checks-first-so-inlining-changes-which-error-a-caller-gets)
- [2. Eta-expansion and saturation](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#2-eta-expansion-and-saturation)
  - [E01. An INLINE function is inlined only when given every value argument its left-hand side names](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#e01-an-inline-function-is-inlined-only-at-a-call-giving-every-value-argument-its-left-hand-side-names)
  - [E02. A point-free INLINE binding counts only dictionaries, so it is inlined where passed unapplied](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#e02-a-point-free-inline-definition-counts-only-its-dictionaries-so-it-is-inlined-where-it-is-passed-unapplied)
  - [E03. An over-saturated INLINE call is inlined anywhere: a pragma-free alias grows or is eta-reduced](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#e03-an-over-saturated-inline-call-is-inlined-whatever-its-context-so-a-pragma-free-alias-of-an-inline-function-whose-left-hand-side-names-fewer-arguments-grows-to-its-body-and-one-whose-left-hand-side-names-as-many-is-eta-reduced-to-it-e04)
  - [E04. Eta-reducing `\x y -> f x y` to `f` needs `f`'s arity or the context to cover the lambdas](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#e04-eta-reduction-turns-x-y---f-x-y-into-f-only-when-f-is-a-variable-whose-arity-or-the-calling-context-covers-the-lambdas-it-reaches-inline-unfoldings-but-leaves-their-count)
  - [E05. `f = g a` is not eta-expanded, so an INLINE `g` is inlined at `f`'s callers, not into `f`](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#e05-a-partial-application-on-a-right-hand-side-is-not-eta-expanded-so-the-inline-function-it-names-is-inlined-at-its-callers-rather-than-in-the-definition)
  - [E06. Stable unfoldings are eta-expanded: INLINE ones keep their count, INLINABLE ones get a new one](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#e06-a-stable-unfoldings-template-is-eta-expanded-to-the-bindings-arity-an-inline-one-keeps-its-count-but-gains-the-callees-body-an-inlinable-one-gets-a-new-count)
  - [E07. A lambda that is not a right-hand side is eta-expanded only if it already has a value lambda](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#e07-a-lambda-that-is-not-a-right-hand-side-is-eta-expanded-only-if-it-already-has-a-value-lambda-so-z---f-a-z-can-saturate-an-inline-f-where-f-a-cannot)
  - [E08. Without a pragma, a lambda behind work counts only if the work is cheap or the lambda one-shot](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#e08-a-lambda-behind-work-joins-a-pragma-free-bindings-count-only-if-the-work-is-cheap-or-the-lambda-one-shot-oneshot-the-state-hack)
  - [E09. Lambdas in every branch of a `case` on an argument join the count, unless `-fpedantic-bottoms`](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#e09-lambdas-under-a-case-on-an-argument-join-the-count-unless--fpedantic-bottoms-a-branch-that-is-neither-a-lambda-nor-bottom-stops-them)
  - [E10. A CallStack before a lambda counts as cheap, and so, under `-fdicts-cheap`, does a dictionary](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#e10-a-callstack-bound-before-a-lambda-counts-as-cheap-so-hascallstack-does-not-cut-the-count--fdicts-cheap-does-the-same-for-a-let-bound-dictionary-not-already-cheap)
  - [E11. A local or unexported function's lambdas become one-shot if every call applies it to that many](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#e11-a-local-functions-lambdas-or-an-unexported-top-level-functions-become-one-shot-and-join-its-count-when-every-call-applies-it-to-that-many-arguments)
  - [E12. A partial application used in several branches of an inlined function is saturated at each use](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#e12-a-partial-application-passed-to-an-inlined-higher-order-function-that-uses-it-in-more-than-one-branch-is-copied-to-its-uses-and-saturated-there-a-lambda-that-saturates-the-same-call-grows-first-stays-bound-and-is-called)
  - [E13. Worker/wrapper splits a function only at lambdas its right-hand side shows](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#e13-workerwrapper-splits-a-function-only-at-lambdas-its-right-hand-side-shows)
  - [E14. A join point reached only from an exit join point counts as one: unless stable, no unfolding](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#e14-a-join-point-jumped-to-only-from-inside-a-loops-exit-join-point-is-taken-for-an-exit-join-point-and-without-a-stable-unfolding-gets-none-so-it-is-not-inlined-at-its-jumps-saturating-a-call-can-give-a-caller-such-a-join-point-taking-a-vector-boxed-which-bangs-on-unrelated-bindings-can-undo)
  - [E15. The first float-out lifts local functions out of a lambda that Call Arity later removes](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#e15-the-first-float-out-lifts-local-functions-out-of-a-lambda-that-call-aritys-eta-expansion-later-removes-cse-then-merges-the-copies-and-float-in-leaves-the-merged-one-above-the-case)
  - [E16. A SPECIALISE copy and an importer's specialisation meet the first float-out in different forms](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#e16-a-defining-modules-specialise-copy-and-an-importers-specialisation-of-one-inlinable-function-meet-the-first-float-out-in-different-forms-behind-a-guard-that-is-not-cheap-the-copy-keeps-its-arity-short-and-floats-its-self-call-as-work-and-where-the-defining-module-raises-the-arity-only-the-importers-template-is-eta-expanded)
  - [E17. Inlined, an entry point's loop-invariant work floats out of the loop; out of line, it is redone](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#e17-inlining-an-entry-point-puts-its-loop-invariant-work-into-the-caller-where-full-laziness-floats-it-out-of-the-callers-loop-called-out-of-line-the-work-is-redone-every-iteration)
  - [E18. A strict constructor under a lazy one is a thunk in STG if its fields are not known tagged](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#e18-a-strict-field-constructor-built-from-fields-the-tag-inference-does-not-prove-evaluated-becomes-under-a-lazy-constructor-a-thunk-of-its-fields-as-when-they-come-from-a-worker-returning-through-a-nullary-join-point)
  - [E19. Under Call Arity, a pointful wrapper makes a specialisation run its checks at every call](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#e19-call-arity-gives-an-unexported-specialisation-the-arity-of-its-one-callers-call-so-a-wrapper-naming-its-arguments-moves-an-inlinable-bodys-checks-inside-the-lambdas-where-a-client-runs-them-at-every-call-instead-of-floating-them-to-constants)
  - [E20. A left section's `let` blocks copying an argument unless an INLINE template saturates its call](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#e20-a-function-argument-holding-a-haskell2010-left-sections-let-is-too-big-to-copy-into-an-inlined-functions-branches-so-whether-an-inline-function-saturates-that-call-in-its-own-template-decides-whether-the-argument-is-copied-first-kept-bound-it-leaves-a-closure-at-the-calls-too-deep-to-inline)
- [3. How INLINE, INLINABLE and no pragma change the code](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#3-how-inline-inlinable-and-no-pragma-change-the-code)
  - [O01. An INLINE specialisation passed a lazy accumulator is inlined after worker/wrapper, loops boxed](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#o01-an-inline-specialisation-passed-a-variable-as-a-loops-lazy-accumulator-is-inlined-only-after-workerwrapper-and-the-loops-it-brings-stay-boxed)
  - [O02. An inlined loop that may evaluate a lifted element reloads outer live values per return point](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#o02-a-loop-that-may-evaluate-a-lifted-element-inlined-into-a-larger-function-reloads-that-functions-live-values-at-every-return-point-so-the-same-loop-core-compiles-to-different-code-inlined-and-out-of-line-and-the-instructions-move-either-way)
  - [O03. A loop moved from an INLINE body into an INLINABLE function arrives unboxed when inlined late](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#o03-a-loop-moved-out-of-an-inline-body-into-an-inlinable-function-arrives-unboxed-when-inlined-late-its-specialisation-is-inlined-from-its-optimised-right-hand-side)
  - [O04. INLINE on a callee in a rare branch makes its caller too big to inline, both exported or reused](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#o04-inline-on-a-function-called-from-a-rarely-taken-branch-makes-its-caller-too-big-to-inline-where-both-are-exported-or-used-more-than-once-the-branch-gains-every-other-call-loses)
  - [O05. INLINE added to a polymorphic list function gives each caller a copy at its own type](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#o05-inline-added-to-a-polymorphic-list-function-with-no-other-pragma-gives-each-caller-a-copy-at-its-own-type-and-makes-a-caller-permuting-two-lists-one-worker-a-few-instructions-a-call-fewer-at-no-byte-on-a-small-fold-over-boxed-elements-inline-costs-a-few-a-call)
  - [O06. An equality-cast dictionary is not specialised on; the fix is INLINE on a non-recursive callee](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#o06-a-dictionary-cast-by-an-equality-given-is-not-specialised-on-so-under-inlinable-the-callee-runs-overloaded-and-inline-on-a-non-recursive-callee-is-the-way-round-it)
  - [O07. List fusion needs producer and consumer inlined into one expression, or the list is built](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#o07-list-fusion-needs-the-producer-and-the-consumer-inlined-into-one-expression-a-producer-specialised-under-inlinable-a-consumer-called-out-of-line-or-a-bang-on-the-consumers-list-builds-the-list)
  - [O08. Specialisations key on types and dictionaries; properties of values reach only inlined copies](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#o08-a-specialisation-keys-on-types-and-dictionaries-never-on-a-value-argument-a-property-of-the-arguments-at-a-call-such-as-a-known-function-or-two-arguments-that-are-one-array-reaches-only-an-inlined-copy)
  - [O09. Unsimplified at float-out, an INLINABLE specialisation's loop becomes a closure](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#o09-a-clients-specialisation-of-an-inlinable-function-meets-float-out-before-the-simplifier-and-a-loop-that-would-be-a-join-point-floats-out-as-a-closure)
  - [O10. An INLINE body under big INLINABLE callers is copied once per caller and type, not per call](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#o10-an-inline-body-whose-callers-are-all-inlinable-and-too-big-to-inline-is-copied-once-per-caller-and-type-into-their-specialisations-not-at-every-call-site)
  - [O11. INLINABLE splits a function small only when optimised; with a run-time dictionary it is called](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#o11-a-function-whose-right-hand-side-is-small-only-once-optimised-is-split-by-workerwrapper-under-inlinable-its-unfolding-the-source-form-and-called-out-of-line-where-its-dictionary-comes-at-run-time-under-inline-or-without-a-pragma-its-body-is-inlined-as-natts-is)
  - [O12. A sum returned out of line in different constructors is built on the heap; a product is not](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#o12-a-sum-returned-in-different-constructors-by-a-function-called-out-of-line-is-built-on-the-heap-where-a-product-is-returned-unboxed-only-inlining-lets-the-caller-take-it-apart-unbuilt)
  - [O13. A check in an INLINE body is computed at every call once its loops fuse into the caller](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#o13-a-check-written-into-an-inline-body-is-computed-at-every-call-once-its-loops-fuse-into-the-caller-and-once-as-a-floated-constant-where-they-stay-a-call-orthotopes-ispermutation)
  - [O14. An INLINE method making two or more method calls a rank deeper costs ticks exponential in rank](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#o14-an-inline-method-that-unfolds-two-or-more-calls-of-its-classs-methods-at-the-next-rank-of-a-type-level-list-costs-simplifier-ticks-growing-exponentially-with-the-rank-against-a-limit-fixed-by-the-programs-size)
  - [O15. A strict constructor applied in part leaves its field lazy, floated from a client as a constant](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#o15-a-strict-constructor-applied-in-part-leaves-its-field-a-lazy-argument-which-float-out-lifts-from-a-client-as-a-constant-applied-in-full-its-field-is-evaluated-by-a-case-that-stays-at-each-call)
  - [O16. A sum a case binds whole becomes a join point's argument, so each inlined branch builds it](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#o16-a-value-a-case-binds-whole-becomes-a-join-points-argument-under-case-of-case-so-each-branch-of-an-inlined-function-returning-a-sum-builds-its-constructor-to-jump-there-under-inline-or-inlinable-on-the-caller-and-at--o2)
  - [O17. An INLINE function grouped with a recursive INLINABLE one is inlined into it and its unfolding](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#o17-an-inline-function-in-a-recursive-group-with-a-self-recursive-inlinable-one-is-inlined-into-it-and-its-unfolding-so-a-clients-specialisation-of-the-loop-breaker-resolves-the-class-methods-the-inline-body-calls)
  - [O18. Inlined right after a `memcpy`, a sum loop loads values spilled across the call at every step](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#o18-inline-on-a-forcing-chain-puts-the-copy-and-the-summing-into-one-function-where-the-sum-loops-address-and-bound-spilled-across-the-copys-memcpy-call-with-nothing-reading-them-before-the-loop-stay-in-their-stack-slots-and-are-loaded-at-every-element-the-loops-core-unchanged-as-in-orthotopes-storable-sum)
  - [O19. A loop eta-expanded only after its call became a scrutinee is a heap closure, not a join point](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#o19-a-local-recursive-function-eta-expanded-only-after-its-call-became-a-case-scrutinee-is-no-join-point-so-a-loop-inlined-into-a-non-tail-position-can-become-a-heap-closure-allocated-each-call-as-sumts-odometer-walk-does-where-suma-is-inlined)
  - [O20. A scrutinised call out of line is no tail call; inlined, an exit box adds a heap check per step](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#o20-a-function-inlined-where-its-result-is-scrutinised-jumps-from-every-exit-to-the-continuation-a-top-level-function-after-floatout-out-of-line-it-is-a-non-tail-call-a-few-instructions-a-call-more-inlined-a-boxed-result-built-at-the-loop-exit-puts-a-heap-check-in-every-iteration)
  - [O21. A worker returning through a nullary join point makes its wrapper's strict constructor a thunk](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#o21-a-worker-that-returns-through-a-nullary-join-point-gets-no-tag-signature-so-its-cpr-wrapper-rebuilds-a-strict-field-constructor-as-a-thunk-an-inlinable-function-inlined-call-site-by-call-site-can-make-that-join-point-where-under-inline-it-is-inlined-once-as-genericforce-does)
  - [O22. Made INLINABLE, an INLINE chain's link returns a vector boxed, builds static strides per call](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#o22-one-pragma-of-an-inline-chain-made-inlinable-a-wrapper-or-a-helper-whose-result-is-built-in-a-join-point-from-a-vector-its-branches-choose-returns-that-vector-boxed-out-of-line-a-strides-list-of-a-static-shape-is-computed-at-every-call-instead-of-once-and-a-method-whose-unfolding-is-one-call-inlines-as-before)
  - [O23. A specialised worker/wrapper wrapper is inlined only at interesting calls, so a bang decides it](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#o23-a-specialised-workerwrapper-wrapper-is-inlined-only-where-an-argument-or-the-context-is-interesting-so-a-bang-that-evaluates-an-argument-can-decide-it-as-for-the-call-of-sreshape-in-reshapes-row)
  - [O24. A bang's case before a strict constructor's fields can change the code, as can uniques' order](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#o24-strict-constructor-wrappers-are-inlined-only-in-the-final-phase-so-a-bang-that-puts-a-case-at-the-head-of-a-methods-unfolding-can-move-that-evaluation-ahead-of-the-wrappers-strict-fields-as-under-orthotopes-badshape-guard-and-the-code-generated-after-it-changes-equal-core-can-compile-to-different-code-too-by-the-order-of-uniques)
  - [O25. INLINABLE for INLINE on point-free wrappers: boxed ones run out of line, Storable ones box once](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#o25-inlinable-in-place-of-inline-on-a-point-free-wrapper-trades-two-unrelated-effects-by-kind-the-boxed-wrapper-not-overloaded-is-called-out-of-line-through-its-cast-worker-and-the-storable-one-specialised-in-the-client-escapes-a-re-boxing-its-inlined-copy-pays)
  - [O26. A one-method dictionary is pre-inlined at one applied call in a lambda, out of line at several](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#o26-a-dictionary-of-a-single-method-class-a-function-is-inlined-unconditionally-where-its-one-call-sits-in-a-lambda-and-applies-it-to-a-value-and-stays-out-of-line-split-by-workerwrapper-while-several-rows-call-it-in-orthotopes-build-the-one-call-left-stays-a-call-not-reproduced-small)
  - [O27. INLINE lets the first float-out lift vector's size tests to top-level `Bool`s dearer than them](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#o27-inlined-in-the-gentle-run-an-inline-wrappers-body-brings-vectors-size-tests-into-a-client-before-the-first-float-out-which-lifts-them-to-top-level-bools-that-cost-more-to-enter-than-the-tests-a-specialisation-of-the-same-body-meets-that-float-out-with-the-tests-still-in-a-call-and-later-tests-a-case-bound-size)
  - [O28. A function argument used twice is copied while small: with an INLINABLE callee, not INLINE](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#o28-a-function-argument-that-an-inline-function-applies-at-two-places-is-copied-into-both-only-while-small-with-its-own-callee-inlinable-it-is-copied-a-local-closure-over-the-callers-values-and-with-the-callee-inline-it-grows-first-and-stays-bound-a-top-level-worker-as-the-function-orthotopes-rerank-applies-to-each-subarray-does-under-scalars-storable-wrappers)
  - [O29. A row's body that inlining makes a `case` is recomputed at every call](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#o29-a-rows-body-that-inlining-turns-into-a-case-stays-under-the-rows-lambda-which-setlevels-levels-as-a-strict-context-so-a-result-independent-of-the-lambdas-argument-is-built-at-every-call-where-a-constructor-application-around-an-out-of-line-call-floats-to-a-constant)
  - [O30. An element-polymorphic copy is keyed on the vector alone; a pragma-free wrapper runs overloaded](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#o30-a-copy-specialised-in-a-module-polymorphic-in-the-element-is-keyed-on-the-vector-type-alone-its-element-and-the-elements-evidence-parameters-without-a-pragma-on-the-wrapper-a-client-calls-the-wrappers-worker-has-no-unfolding-and-runs-with-the-elements-dictionary)
- [4. Which unfolding a call gets: stable or vanilla](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#4-which-unfolding-a-call-gets-stable-or-vanilla)
  - [U01. Without a pragma, the unfolding is the optimised right-hand side, its guidance the importer's](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#u01-a-binding-without-a-pragma-carries-an-unfolding-made-from-its-optimised-right-hand-side-and-its-importer-computes-that-unfoldings-guidance)
  - [U02. A binding CSE rewrites to an earlier binder loses its INLINE or INLINABLE unfolding](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#u02-cse-replacing-a-bindings-whole-right-hand-side-by-an-earlier-binding-drops-its-inline-or-inlinable-unfolding)
  - [U03. INLINE's stable unfolding keeps the right-hand side as written while the binding is optimised](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#u03-inline-gives-a-stable-unfolding-of-the-right-hand-side-as-written-inlined-at-saturated-calls-with-something-to-gain-while-the-right-hand-side-is-optimised-on-its-own)
  - [U04. INLINABLE gives a stable unfolding as written, which an importer inlines by that form's size](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#u04-inlinable-gives-a-stable-unfolding-of-the-right-hand-side-as-written-and-an-importer-inlines-it-by-the-size-of-that-form-not-of-the-optimised-right-hand-side)
  - [U05. The interface carries every stable unfolding, a vanilla one only when GHC might inline it](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#u05-which-unfoldings-the-interface-carries-every-stable-one-a-vanilla-one-only-when-ghc-might-inline-it-and-more-or-fewer-under-the-exposure-flags)
  - [U06. An importer recomputes imported guidance by its own thresholds, always-inline unfoldings apart](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#u06-an-importer-recomputes-the-guidance-of-every-imported-unfolding-not-marked-always-inline-with-its-own-thresholds-so--funfolding-creation-threshold-also-decides-which-imported-functions-it-inlines)
  - [U07. Worker/wrapper gives a small function an always-inline unfolding, not refreshed afterwards](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#u07-workerwrapper-does-not-split-a-small-function-but-gives-it-an-always-inline-stable-unfolding-which-from-then-on-is-not-refreshed-from-the-right-hand-side)
  - [U08. Worker/wrapper moves an INLINABLE unfolding to the worker, so importers can still specialise it](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#u08-workerwrapper-splits-an-inlinable-function-and-moves-its-stable-unfolding-to-the-worker-so-importers-can-still-specialise-it)
  - [U09. INLINE stops worker/wrapper, even on a self-recursive loop breaker not inlined](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#u09-inline-stops-workerwrapper-even-on-a-self-recursive-function-that-as-its-own-loop-breaker-is-not-inlined)
  - [U10. Each simplifier pass simplifies stable unfoldings, with only what is active in all their phases](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#u10-a-stable-unfolding-is-simplified-at-every-simplifier-pass-but-only-with-the-inlinings-and-rules-active-throughout-its-own-activation-and-without-eta-expansion)
  - [U11. A default method's compulsory unfolding gives every instance taking it the whole body, any size](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#u11-a-classs-default-method-gets-a-compulsory-unfolding-so-every-instance-taking-the-default-gets-its-whole-body-as-lazy-as-written-whatever-its-size-and-at-any-optimisation-level-and-with-it-the-defaults-inline-or-inlinable)
  - [U12. A specialised copy keeps an INLINE unfolding but no INLINABLE one; a SPECIALISE copy, neither](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#u12-a-specialised-copy-keeps-the-inline-unfolding-of-what-it-specialises-and-drops-an-inlinable-one-a-specialise-pragmas-copy-made-by-the-desugarer-gets-no-stable-unfolding-at-all-so-it-loses-the-inline-unfolding)
  - [U13. An optimised unfolding carries what later passes did, exit join points included](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#u13-an-optimised-unfolding-carries-what-the-defining-modules-later-passes-did-at-the-abstract-types-such-as-an-exit-join-point-which-no-client-inlines-an-inlinable-unfolding-taken-before-optimisation-carries-none-of-it)
  - [U14. Without a stable unfolding, a join point gets none at birth, nor ever as an exit join point](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#u14-a-join-point-without-a-stable-unfolding-gets-none-at-birth-nor-ever-if-it-is-taken-for-an-exit-join-point-so-it-is-not-inlined-even-where-inlining-would-restore-a-tail-call)
  - [U15. A bang on an INLINE function's argument stays in every caller's copy and changes their Core](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#u15-a-bang-on-an-inline-functions-argument-stays-in-the-unfolding-inlined-at-every-caller-though-the-arguments-demand-already-makes-it-strict-and-changes-the-callers-core)
  - [U16. A demand signature combines the stable unfolding's demands with the right-hand side's](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#u16-a-bindings-demand-signature-combines-the-demands-of-its-stable-unfolding-with-those-of-its-right-hand-side-so-an-argument-the-right-hand-side-no-longer-uses-stays-used-and-a-boxed-use-in-the-unfolding-keeps-it-boxed)
  - [U17. Cast worker/wrapper moves a stable unfolding to the cast worker, leaving a trivial vanilla one](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#u17-cast-workerwrapper-moves-a-stable-unfolding-to-the-cast-worker-leaving-the-binding-a-trivial-vanilla-unfolding-a-coercion-of-the-worker)
  - [U18. At commit 6913545fd3, CSE merges equal `let`-holding bindings only while no third differs](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#u18-at-commit-6913545fd3-cse-merges-two-identical-bindings-holding-a-non-recursive-let-only-while-no-third-such-binding-differs-from-them-so-inlined-copies-that-float-out-alike-stay-separate-the-trees-patch-merges-them)
  - [U19. A join point given a built value hides its construction from CPR; the value is returned boxed](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#u19-a-join-point-that-receives-an-already-built-value-hides-how-it-was-built-from-cpr-analysis-so-a-worker-returns-the-nested-constructor-boxed)
  - [U20. A worker returning a result's fields unboxed makes callers keeping the result rebuild its boxes](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#u20-a-worker-that-returns-a-results-fields-unboxed-makes-every-caller-that-keeps-the-result-rebuild-its-boxes-a-box-the-worker-needed-itself-included)
  - [U21. Worker/wrapper unboxes a given equality but not the argument whose type it fixes](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#u21-workerwrapper-unboxes-a-given-equality-but-not-the-argument-whose-type-it-fixes-so-a-worker-over-a--int-takes-and-returns-a-boxed)
- [5. Rules read but given no entry](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#5-rules-read-but-given-no-entry)
  - [R01. Rule left-hand sides and GHCi expressions get no inlining](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#r01-rule-left-hand-sides-and-ghci-expressions-get-no-inlining)
  - [R02. No flag bypasses `tryUnfolding`'s tests: `unfoldingVeryAggressive` is set by nothing on HEAD](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#r02-no-flag-bypasses-tryunfoldings-tests-unfoldingveryaggressive-which-they-check-is-set-by-nothing-on-head)
  - [R03. Inlining decisions do not depend on `-funfolding-keeness-factor`, though it is accepted](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#r03-inlining-decisions-do-not-depend-on--funfolding-keeness-factor-though-it-is-accepted)
  - [R04. The `inline depth` that `-dinline-check` prints decides no inlining](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#r04-the-inline-depth-that--dinline-check-prints-decides-no-inlining)
  - [R05. CorePrep's eta-expansion of arguments comes after all inlining](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#r05-corepreps-eta-expansion-of-arguments-comes-after-all-inlining)
  - [R06. Recursive bindings' arities and trimmed arities change no inlining beyond E08's](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#r06-recursive-bindings-arities-and-trimmed-arities-change-no-inlining-beyond-e08s)
  - [R07. Ordinary source gives each INLINE unfolding a count; the count-free form serves only a fallback](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#r07-ordinary-source-gives-every-inline-unfolding-a-saturation-count-mkinlineunfoldingnoarity-serves-only-a-fallback)
  - [R08. After specialisation, a local dictionary binder's unfolding is remade from its specialised form](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#r08-after-specialisation-a-local-dictionary-binders-unfolding-is-remade-from-its-specialised-right-hand-side)
- [6. Inlining, not specialisation: GHC's text against its code, and behaviour that may be unintended](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#6-inlining-not-specialisation-ghcs-text-against-its-code-and-behaviour-that-may-be-unintended)
- [Appendix. How inlining meets specialisation](https://github.com/Mikolaj/horde-ad/blob/drop-recursive-inline/docs/inlining-catalogue.md#appendix-how-inlining-meets-specialisation)

## How to read an entry

Each entry gives the rule, with its source; what of our record it explains (**Seen**); its repros' modules and the dump lines that show the rule at work; and whether the observation reproduces small. An observation that did not reproduce small is an entry too, saying what was tried. Entries cite one another by ID, a letter and two digits: A for the call-site decision, E for eta and saturation, O for our record's observations, U for which unfolding a call gets, and R for a rule read but given no entry (section 5). A check's ID standing alone (P, I3, S1, A3 and the like) cites that check of `docs/perf-checklist.md`, and orthotope's commits are named by subject and its scratch builds by the names the measurements used (C3, V2a and the like), with what each changes; "the tip" is "Condense the account of unorderedRouteT's sort and merge" of the date an entry gives, 2026-10-15 where it gives none.

Every repro is a directory under `~/r/horde-ad/dist-inlcat/cases/`, an uncommitted scratch directory on the machine the catalogue was made on; `~/r/horde-ad/dist-inlcat/README.md` gives a case's form; `bin/run-case cases/DIR` builds it with HEAD and keeps the dumps, `bin/check-case cases/DIR` checks the lines of the directory's `expect` file against those dumps (most of the dump lines the entry quotes, and condensed decision lines, checked part by part), and `bin/run-all` does both for every case; an entry names its directories as `~/r/horde-ad/dist-inlcat/cases/NAME`, and their files by name. The entries show the modules of the repros their main claims rest on, eliding only repeated lines and comments. An entry that reproduces small also gives whatever else its main claim needs, so that the claim reproduces without the directories, though a side remark, or a claim resting on a build of orthotope or horde-ad, may not: a variant's modules are compiled with `ghc --make -ddump-to-file -O -ddump-simpl -ddump-inlinings -dsuppress-all -dsuppress-uniques` and the flags the entry names for the variant, its own suppression flags in place of those two where the entry names them or says what the variant keeps; a repro importing vector adds `-package-db ~/.cabal/store/ghc-10.1.20260918-inplace/package.db -package-id vector-0.13.2.0-28fe1729931a9eb304d82b5130f8c94336e05847f89768a2a20a1eaeca32fd89`, vector 0.13.2.0 as built with HEAD; `run`, where the entry gives it, holds the arguments `Main` is linked and run with; and the entry shows each script the claim rests on or says what it does. U05's two guidance figures for A13's `hugeN` and its worker come from a scratch build, not from a case's dumps. On 2026-10-18 every `expect` line of every case passed. Where an entry gives instruction counts of a repro, they come from a script in its directory, `~/r/horde-ad/dist-inlcat/cases/NAME/measure.sh` unless the entry names another, run by hand: unless the entry says otherwise, it runs the variants' `Main` at an iteration count and at twice it, counting instructions with `perf stat -e instructions:u` and bytes allocated with `+RTS -s`, and divides the differences by the difference in iterations, or in elements where the entry gives figures an element; no `expect` line checks them. `-dinline-check NAME` decisions in a block are quoted whole, or with lines elided at `...`, or condensed as the entry says; dump lines may have their whitespace collapsed to fit one line.

## The decision whether to inline an occurrence, in brief

The order in which GHC HEAD's simplifier tests whether to inline an occurrence, each step with the entries that give it:

1. Before a let's right-hand side is simplified, a binding that occurs once, outside a lambda, or applied inside one when its right-hand side is trivial or a lambda, is substituted with no size or benefit test, unless, chiefly, it is INLINE or the occurrence is inside a stable unfolding (A16); after the right-hand side is simplified, a small or trivial local binding is substituted at its uses (A17), and an exit join point never is (A20).
2. At a call, rules are tried first, on the arguments as written (A12): a class method on a known dictionary is selected by a built-in rule (A15), `inline f` substitutes `f`'s unfolding whatever its guidance, which for a function split by worker/wrapper is the wrapper's (A13), and a specialisation rule wins over an INLINE unfolding (A12, U12); a rule matches through a variable bound to a CONLIKE call without inlining it (A22).
3. Then the call site gets no unfolding for a loop breaker (A11), an exit or newly made join point without a stable unfolding (A20, U14) or a dictionary function of a class that is not unary (A15); in a phase the pragma excludes, it gets an inactive one (A10, A24, A25, A26).
4. Otherwise the decision follows the unfolding's guidance. Under `UnfNever`, given to a body past the creation threshold or to a top-level bottoming function bigger than its call, the unfolding is never inlined (A05, A23). `UnfWhen`, given to an INLINE function (U03), a wrapper (A26), a small function (A02, U07) or a compulsory unfolding (U11), needs its count of arguments (E01, E02), or with `unsat_ok` at least one (A02, A26), and then either `boring_ok` (A01) or a benefit from an argument or the context (A03, A07, A08); a lone scrutinised variable with an expandable unfolding has none, its `case` resolved through that unfolding instead (A21), and over-saturation counts as one (E03). `UnfIfGoodArgs`, given to a pragma-free function (U01) or an INLINABLE one (U04), needs a work-free unfolding (A06), a benefit (A03), and its size, less the discounts and plus a depth penalty for a call deep in cases (A09), within the threshold (A04); a join point is decided differently (A18, A19).

Section 4 says which unfolding the call gets: a stable unfolding of the right-hand side as written under INLINE and INLINABLE (U03, U04), one of the optimised right-hand side otherwise (U01), exported under U05's rules, its guidance recomputed by the importer (U06); and section 2's eta and arity rules fix the count of arguments the unfolding needs.

## 1. Whether a visible unfolding is inlined at a call

The call-site decision and its exceptions, apart from saturation and eta (section 2) and from which unfolding the call gets (section 4); and some consequences of inlining and of flags beyond that decision (A29 and A31 to A34).

### A01. An INLINE function at an exactly saturated call with trivial arguments in a boring context is inlined only if its body is tiny, judged after its template is simplified

**Rule.** An INLINE pragma gives the binding `UnfWhen` guidance, and `tryUnfolding` inlines the binding at a call giving every argument its left-hand side names if `boring_ok || some_benefit` ([compiler/GHC/Core/Opt/Simplify/Inline.hs#L310][g5], the `UnfWhen` case, the test at [#L311][g6]). `some_benefit` holds when some argument is not `TrivArg` or, at a call with enough arguments, `interesting_call` holds, which, at a call not over-saturated, it never does in a boring context (`calc_some_benefit`, [#L394][g7]; `interesting_call`, `_other -> False`, [#L418][g8]); so at a call whose arguments are variables with no unfolding and whose result is returned or stored as it is (`BoringCtxt`), as in a lazy argument of a function with no rules and no argument discount (`lazyArgContext`, [compiler/GHC/Core/Opt/Simplify/Utils.hs#L977][g9]), `boring_ok` decides. `mkInlineUnfoldingWithArity` sets it, for a count above 0, from `inlineBoringOk` ([compiler/GHC/Core/Unfold/Make.hs#L157][g10], [#L169][g11]; Note [INLINE pragmas and boring contexts] at [#L317][g12]; `inlineBoringOk`, [compiler/GHC/Core/Unfold.hs#L293][g13]), which walks the template with a credit of one per value lambda ([#L305][g14]), spends one per trivially applied argument ([#L312][g15]), and returns `True` only if it ends at a variable with its credit not overspent ([#L328][g16]), at a data constructor applied to trivial arguments whatever the credit ([#L326][g17], wrinkle (IB2) of Note [inlineBoringOk] at [#L224][g18]), at a unary class's constructor ([#L327][g19], (IB6)) or at a trivial literal ([#L324][g20]), skipping casts, ticks, type arguments, an empty `case` and an `unsafeEqualityProof` `case` (Note [Inline unsafeCoerce]); any non-trivial argument, any other `case` or a `let` makes it return `False` ([#L331][g21]). So a body with a nested call or a `case` is not tiny, and such an INLINE function is not inlined in a boring context. The flag is refreshed each time the stable unfolding is simplified, as `boring_ok || inlineBoringOk expr'` of the simplified template (`simplStableUnfolding`, [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4926][g22]), so a template that becomes a bare call after gentle simplification (`wId` below, once `id` is inlined) becomes boring-ok, while one that stays non-trivial never does. A count of 0 is boring-ok regardless (E02). Where the call is not inlined and is the whole body of a pragma-free function, that function is then eta-reduced to the INLINE one (E04), as `uArg = wArg` below and `fmap` to `mapA` in E03.

**Seen.** `docs/perf-checklist.md` I1's Read: "in a boring context --- its arguments variables GHC has no information on and its result returned or stored as it is, where GHC by design inlines only a tiny INLINE body", at `padT`'s `toVectorListT sh t`; and orthotope's `fmap`, whose exactly saturated call of Shaped `mapA` was not inlined, `mapA`'s body not being boring-ok (E03).

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A01-inline-boring-context`, variant `base`, `-dinline-check inl`): three INLINE functions, one with a `case` body and two tiny, each called as a lazy constructor argument with variable arguments; the first also called with a constructor argument and under a `case`.

```haskell
module M (lazyArgNot, lazyArgFlip, lazyArgCon, valueArgNot, caseNot) where

{-# INLINE inlNot #-}
inlNot :: Bool -> Bool
inlNot b = case b of { True -> False; False -> True }

{-# INLINE inlFlip #-}
inlFlip :: (Int -> Int -> Int) -> Int -> Int -> Int
inlFlip f x y = f y x

{-# INLINE inlCon #-}
inlCon :: Int -> Int -> (Int, Int, Int)
inlCon x y = (y, x, y)

lazyArgNot :: Bool -> Maybe Bool
lazyArgNot b = Just (inlNot b)

lazyArgFlip :: (Int -> Int -> Int) -> Int -> Int -> Maybe Int
lazyArgFlip f x y = Just (inlFlip f x y)

lazyArgCon :: Int -> Int -> Maybe (Int, Int, Int)
lazyArgCon x y = Just (inlCon x y)

valueArgNot :: Maybe Bool
valueArgNot = Just (inlNot True)

caseNot :: Bool -> Int
caseNot b = case inlNot b of { True -> 1; False -> 2 }
```

The decisions:

```
Considering inlining: inlNot
  arg infos [TrivArg]
  interesting continuation BoringCtxt
  some_benefit False
  is exp: True
  is work-free: True
  guidance ALWAYS_IF(arity=1,unsat_ok=False,boring_ok=False)
  case depth = 0
  inline depth = 1
  ANSWER = NO
Considering inlining: inlNot
  arg infos [ValueArg]
  interesting continuation BoringCtxt
  some_benefit True
  ...
  ANSWER = YES
Considering inlining: inlNot
  arg infos [TrivArg]
  interesting continuation CaseCtxt
  some_benefit True
  ...
  ANSWER = YES
Considering inlining: inlFlip
  arg infos [TrivArg, TrivArg, TrivArg]
  interesting continuation BoringCtxt
  some_benefit False
  is exp: True
  is work-free: True
  guidance ALWAYS_IF(arity=3,unsat_ok=False,boring_ok=True)
  case depth = 0
  inline depth = 1
  ANSWER = YES
Considering inlining: inlCon
  arg infos [TrivArg, TrivArg]
  interesting continuation BoringCtxt
  some_benefit False
  ...
  ANSWER = YES
```

The Core:

```
lazyArgNot = \ b -> Just (inlNot b)
valueArgNot = Just False
lazyArgFlip = \ f x y -> Just (f y x)
lazyArgCon = \ x y -> Just (y, x, y)
```

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A01-inline-boring-ok`, variants `base`, `arg`, `con` and `id`, each checking one wrapper, by `-dinline-check wSwap`, `wArg`, `wCon` and `wId`, and `ds`, `-O -ddump-ds -dsuppress-uniques -dsuppress-module-prefixes`, dumping the desugarer's output): four INLINE wrappers, each called exactly saturated with variables as a function's whole body.

```haskell
module M where

data P = P Int Int

{-# NOINLINE g #-}
g :: Int -> Int -> Int
g x y = x * y + 1

{-# INLINE wSwap #-}
wSwap :: Int -> Int -> Int
wSwap x y = g y x                 -- a call with trivial arguments

{-# INLINE wArg #-}
wArg :: Int -> Int -> Int
wArg x y = g (x + 1) y            -- a call with a non-trivial argument

{-# INLINE wCon #-}
wCon :: Int -> Int -> P
wCon x y = P y x                  -- a constructor with trivial arguments

{-# INLINE wId #-}
wId :: Int -> Int -> Int
wId x y = id (g y y)              -- trivial only once id is inlined

uSwap, uArg, uId :: Int -> Int -> Int
uSwap a b = wSwap a b
uArg a b = wArg a b
uId a b = wId a b
uCon :: Int -> Int -> P
uCon a b = wCon a b
```

The decision at each call has `arg infos [TrivArg, TrivArg]`, `interesting continuation BoringCtxt` and `some_benefit False`; they differ in the guidance, each decision condensed to one line:

    wSwap  guidance ALWAYS_IF(arity=2,unsat_ok=False,boring_ok=True)   ANSWER = YES
    wArg   guidance ALWAYS_IF(arity=2,unsat_ok=False,boring_ok=False)  ANSWER = NO
    wCon   guidance ALWAYS_IF(arity=2,unsat_ok=False,boring_ok=True)   ANSWER = YES
    wId    guidance ALWAYS_IF(arity=2,unsat_ok=False,boring_ok=True)   ANSWER = YES

though the desugarer made `wId`'s unfolding with `Guidance=ALWAYS_IF(arity=2,unsat_ok=False,boring_ok=False) Tmpl= \ (x [Occ=Dead] :: Int) (y :: Int) -> id @Int (g y y)}]`. The Core:

    uSwap = \ a b -> g b a
    uCon = \ a b -> P b a
    uId = \ a b -> g b b
    uArg = wArg

**Reproduces small:** yes.

### A02. A binding without a pragma whose body is no bigger than its call is inlined at every call giving it a value argument, partial calls included, which INLINE can undo

**Rule.** For a binding with no INLINE pragma, `calcUnfoldingGuidance` measures the body under the lambdas with `sizeExpr` ([compiler/GHC/Core/Unfold.hs#L349][g23]); when `uncondInline` holds --- for a join point, A19's test; for another binding with value lambdas, a size at most `10 * (arity + 1)`, the size of the call it replaces, the arity being the unfolding's own count of value lambdas; for one without, only a trivial body ([#L502][g24]; Note [INLINE for small functions], [#L445][g25], points (1), (2) and (4)) --- the guidance is `UnfWhen` with `unsat_ok` and `boring_ok` both true ([#L353][g26]). `tryUnfolding` takes such an unfolding at any call with at least one value argument, in any context (`enough_args`, `(unsat_ok && n_val_args > 0)`, [compiler/GHC/Core/Opt/Simplify/Inline.hs#L318][g27]; point (3) of the Note), so `f` is inlined in `map (f a)`, giving a lambda in place of a partial application, while an occurrence with no value argument of a function with value lambdas is not inlined. A body of that size need not satisfy `inlineBoringOk`: a two-way `case` on the argument returning nullary constructors is within that size, as `inlNotP`'s `ALWAYS_IF` guidance below shows. An INLINE pragma replaces this guidance with `UnfWhen` whose `boring_ok` is `inlineBoringOk` of the body (A01), false for a `case` other than an empty one or an `unsafeEqualityProof` one, and whose `unsat_ok` is False (E01) (`mkInlineUnfoldingWithArity`, [compiler/GHC/Core/Unfold/Make.hs#L157][g10]); so adding INLINE to such a function stops its inlining in a boring context and at partial calls. A larger body without a pragma gets `UnfIfGoodArgs` and needs `some_benefit` (A03), whatever its adjusted size. Worker/wrapper keeps a function this small whole, with a stable unfolding (U07). The threshold grows with the unfolding's value lambdas, so it depends on the binding's arity after eta-expansion (E05, E08).

**Seen.** Not in our record. It is the other side of E01's observations: an INLINE wrapper is inlined at fewer partial calls than a small pragma-free one would be.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A02-tiny-body-unconditional`, variant `base`, `-dinline-check inl`): the same two-way `case` without a pragma and with INLINE, and a larger body without a pragma, each called as a lazy constructor argument with a variable argument. The callees are exported so that `preInlineUnconditionally` (A16) does not take them; the INLINE one has its own type so that CSE does not make it an alias of the other.

```haskell
module M (AB (..), boringP, boringI, boringB, inlNotP, inlNotI, inlNotB) where

data AB = A | B

inlNotP :: Bool -> Bool
inlNotP b = case b of { True -> False; False -> True }

{-# INLINE inlNotI #-}
inlNotI :: AB -> AB
inlNotI b = case b of { A -> B; B -> A }

inlNotB :: Int -> Maybe Int
inlNotB x = case x of { 0 -> Nothing; _ -> Just x }

boringP :: Bool -> Maybe Bool
boringP b = Just (inlNotP b)

boringI :: AB -> Maybe AB
boringI b = Just (inlNotI b)

boringB :: Int -> Maybe (Maybe Int)
boringB x = Just (inlNotB x)
```

The decisions:

```
Considering inlining: inlNotP
  arg infos [TrivArg]
  interesting continuation BoringCtxt
  some_benefit False
  is exp: True
  is work-free: True
  guidance ALWAYS_IF(arity=1,unsat_ok=True,boring_ok=True)
  case depth = 0
  inline depth = 1
  ANSWER = YES
Considering inlining: inlNotI
  arg infos [TrivArg]
  interesting continuation BoringCtxt
  some_benefit False
  is exp: True
  is work-free: True
  guidance ALWAYS_IF(arity=1,unsat_ok=False,boring_ok=False)
  case depth = 0
  inline depth = 1
  ANSWER = NO
Considering inlining: inlNotB
  arg infos [TrivArg]
  interesting continuation BoringCtxt
  some_benefit False
  is exp: True
  is work-free: True
  guidance IF_ARGS [20] 40 20
  case depth = 0
  inline depth = 1
  depth based penalty = 0
  adjusted size = 20
  ANSWER = NO
```

The Core:

```
boringP = \ b -> Just (case b of { False -> True; True -> False })
boringI = \ b -> Just (inlNotI b)
boringB = \ x -> Just (inlNotB x)
```

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A02-small-function-inlines-unsaturated`, variant `base`, `-dinline-check small`, which by prefix also reports `smallI`): one small body, without a pragma and with INLINE, applied in a client to one argument of two under `map` and to none under `zipWith`.

```haskell
module M where

{-# NOINLINE g #-}
g :: Int -> Int -> Int
g x y = x * y + 1

{-# NOINLINE g2 #-}
g2 :: Int -> Int -> Int
g2 x y = x * y + 2

small :: Int -> Int -> Int
small x y = g y x

{-# INLINE smallI #-}
smallI :: Int -> Int -> Int
smallI x y = g2 y x
```

```haskell
module C where
import M

one, oneI, none, noneI :: [Int] -> [Int]
one xs = map (small 1) xs
oneI xs = map (smallI 1) xs
none xs = zipWith small xs xs
noneI xs = zipWith smallI xs xs
```

The interface gives `small` `Unfolding: Core: StableSystem <2,TrueTrue>` and `smallI` `Unfolding: Core: StableUser <2,FalseTrue>`. At the calls under `map` and `zipWith`, each decision condensed to one line:

    Considering inlining: small   arg infos [ValueArg]  RuleArgCtxt  guidance ALWAYS_IF(arity=2,unsat_ok=True,boring_ok=True)   ANSWER = YES
    Considering inlining: smallI  arg infos [ValueArg]  RuleArgCtxt  guidance ALWAYS_IF(arity=2,unsat_ok=False,boring_ok=True)  ANSWER = NO
    Considering inlining: small   arg infos []          RuleArgCtxt  guidance ALWAYS_IF(arity=2,unsat_ok=True,boring_ok=True)   ANSWER = NO
    Considering inlining: smallI  arg infos []          RuleArgCtxt  guidance ALWAYS_IF(arity=2,unsat_ok=False,boring_ok=True)  ANSWER = NO

and the Core:

    one1 = \ y -> case y of { I# ww -> case $wg ww 1# of ww2 { __DEFAULT -> I# ww2 } }
    oneI1 = smallI oneI2

Under `zipWith` both are inlined once fusion has applied them to two arguments, `: ipv2 ipv3 -> : (g ipv2 ipv) (none_go ipv1 ipv3)` and `: ipv2 ipv3 -> : (g2 ipv2 ipv) (noneI_go ipv1 ipv3)`.

**Reproduces small:** yes.

### A03. A function without INLINE and bigger than its call is inlined only where some argument or the context is interesting, however small it is

**Rule.** A binding with `UnfIfGoodArgs` guidance (no pragma or INLINABLE, and not tiny, A02) is inlined at a call, a join point excepted (A18), only when all three hold: its unfolding is work-free (A06), `some_benefit`, and the adjusted size is at most the use threshold (A04). `some_benefit` at a call with enough arguments is: some argument is not `TrivArg` (A07), or the call context is interesting. Which contexts are interesting depends on the guidance: `CaseCtxt` (except a lone variable with an expandable unfolding, A21) and `ValAppCtxt` (unreachable on this tree, A08) always; `RuleArgCtxt` and `DiscArgCtxt` when the unfolding takes an argument; `RhsCtxt NonRecursive` only for `UnfWhen` guidance with an argument (INLINE, a worker/wrapper or constructor wrapper, A02's tiny bodies); `BoringCtxt` and `RhsCtxt Recursive` never. So a pragma-free function small enough to inline is still left as a call on the right-hand side of a let, or in a strict argument position that yields `RhsCtxt` (A08), where the same body under INLINE is inlined. An over-saturated call always has a benefit; an under-saturated one has one only if an argument is interesting (section 2). Source: [compiler/GHC/Core/Opt/Simplify/Inline.hs#L320][g28] (`tryUnfolding`, the `UnfIfGoodArgs` case), [#L392][g29] (`calc_some_benefit`, `interesting_call`), [#L433][g30] (Note [RHS of lets]).

**Seen.** Not in our record.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A03-some-benefit`, variant `base`, `-dinline-check inl`): the same body without a pragma (`inlB`) and with INLINE (`inlI`, its literal changed so that CSE keeps the two apart), each called as a lazy constructor argument, on a let's right-hand side and under a `case`; `inlB` also with a literal argument.

```haskell
module M (inlB, inlI, boringB, boringI, letB, letI, caseB, caseI, valueB) where

inlB :: Int -> Maybe Int
inlB x = case x of { 0 -> Nothing; _ -> Just x }

{-# INLINE inlI #-}
inlI :: Int -> Maybe Int
inlI x = case x of { 1 -> Nothing; _ -> Just x }

boringB, boringI :: Int -> Maybe (Maybe Int)
boringB x = Just (inlB x)
boringI x = Just (inlI x)

letB, letI :: Int -> (Maybe Int, Maybe Int)
letB x = let y = inlB x in (y, y)
letI x = let y = inlI x in (y, y)

caseB, caseI :: Int -> Int
caseB x = case inlB x of { Nothing -> 0; Just _ -> 1 }
caseI x = case inlI x of { Nothing -> 0; Just _ -> 1 }

valueB :: Maybe (Maybe Int)
valueB = Just (inlB 5)
```

The decisions, whitespace collapsed:

```
Considering inlining: inlB arg infos [TrivArg] interesting continuation BoringCtxt some_benefit False is exp: True is work-free: True guidance IF_ARGS [20] 40 20 case depth = 0 inline depth = 1 depth based penalty = 0 adjusted size = 20 ANSWER = NO
Considering inlining: inlB arg infos [TrivArg] interesting continuation RhsCtxt(NonRecursive) some_benefit False is exp: True is work-free: True guidance IF_ARGS [20] 40 20 case depth = 0 inline depth = 1 depth based penalty = 0 adjusted size = 0 ANSWER = NO
Considering inlining: inlB arg infos [ValueArg] interesting continuation BoringCtxt some_benefit True is exp: True is work-free: True guidance IF_ARGS [20] 40 20 case depth = 0 inline depth = 1 depth based penalty = 0 adjusted size = 0 ANSWER = YES
Considering inlining: inlB arg infos [TrivArg] interesting continuation CaseCtxt some_benefit True is exp: True is work-free: True guidance IF_ARGS [20] 40 20 case depth = 0 inline depth = 1 depth based penalty = 0 adjusted size = 0 ANSWER = YES
Considering inlining: inlI arg infos [TrivArg] interesting continuation BoringCtxt some_benefit False is exp: True is work-free: True guidance ALWAYS_IF(arity=1,unsat_ok=False,boring_ok=False) case depth = 0 inline depth = 1 ANSWER = NO
Considering inlining: inlI arg infos [TrivArg] interesting continuation RhsCtxt(NonRecursive) some_benefit True is exp: True is work-free: True guidance ALWAYS_IF(arity=1,unsat_ok=False,boring_ok=False) case depth = 0 inline depth = 1 ANSWER = YES
```

The Core:

```
boringB = \ x -> Just (inlB x)
letB = \ x -> let { y = inlB x } in (y, y)
valueB = Just valueB1
boringI = \ x -> Just (inlI x)
letI = \ x -> let { y = case x of wild { I# ds -> ...
```

**Reproduces small:** yes.

### A04. Without INLINE, a body bigger than its call is inlined only if its size less the call's discounts is at most `-funfolding-use-threshold`, 90 by default

**Rule.** For `UnfIfGoodArgs` guidance, printed `IF_ARGS [d1 .. dn] size res`, `tryUnfolding` computes `adjusted size = size + depth penalty - discount` and requires it to be at most `-funfolding-use-threshold` (default 90). The discount is 10 for the call, 10 for each value argument, an amount for each argument set by its summary --- 0 for `TrivArg`, 10 for `NonTrivArg`, the argument's own `di` for `ValueArg` --- and the result discount `res` in `CaseCtxt` and `ValAppCtxt` (unreachable on this tree, A08) or when over-saturated, at most 40 of it in the other contexts, and none in `BoringCtxt`. So an argument discount is earned only by a value (a constructor application, a lambda, a partial application, a variable bound to one: A07), and a result discount only by a context that consumes the result. `sizeExpr` sets the argument discounts: an argument scrutinised by a `case` gets 20 plus the size of the alternatives other than the largest; an argument applied to a value gets `-funfolding-fun-discount` (60), the largest one counting where it is applied several times; a dictionary argument given to a class method gets `-funfolding-dict-discount` (30), plus 60 when the method is applied further, summed over the calls, so an overloaded pragma-free function is inlined at a call with a known dictionary well past the size it would otherwise be allowed (A15's `inlOver` gets 180 for two methods each applied). The depth penalty is A09's. Source: [compiler/GHC/Core/Opt/Simplify/Inline.hs#L337][g31] (`adjusted_size`, `small_enough`), [#L709][g32] (`computeDiscount`); [compiler/GHC/Core/Unfold.hs#L603][g33] (`sizeExpr`, the case on an argument), [#L780][g34] (`classOpSize`), [#L829][g35] (`funSize`), [#L373][g36] (`mk_discount`, Note [Function and non-function discounts]), [#L94][g37] (`defaultUnfoldingOpts`).

**Seen.** GHC [#27893](https://gitlab.haskell.org/ghc/ghc/-/work_items/27893) (`docs/ghc-issue-exit-join-point-boxed-loop.md` in horde-ad), its Summary: HEAD inlines orthotope's `$wcopyStrided`, the six calls in it of a method of its known dictionary discounting it by 540, its adjusted size -123.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A04-size-and-discounts`, variants `base` and `thr110`, both `-dinline-check inl` and `-fno-worker-wrapper`, the latter so that `inlSz` keeps its own guidance rather than a wrapper's, A26; `thr110` adds `-funfolding-use-threshold=110`): a five-way `case` on the first argument, called with that argument a variable, an addition and a literal, in a lazy argument and under a `case`.

```haskell
module M (inlSz, trivK, nonTrivK, valueK, valueKCase) where

inlSz :: Int -> Int -> Int
inlSz k y = case k of
  0 -> y + 1
  1 -> y * 2
  2 -> y - 3
  3 -> y * y
  _ -> y

trivK, nonTrivK :: Int -> Int -> Maybe Int
trivK k y = Just (inlSz k y)
nonTrivK k y = Just (inlSz (k + 1) y)

valueK :: Int -> Maybe Int
valueK y = Just (inlSz 2 y)

valueKCase :: Int -> Bool
valueKCase y = case inlSz 2 y of { 0 -> True; _ -> False }
```

The decisions in `base`, whitespace collapsed; the four adjusted sizes are 153 less 30, 50, 40 and 80:

```
Considering inlining: inlSz arg infos [TrivArg, TrivArg] interesting continuation BoringCtxt some_benefit False is exp: True is work-free: True guidance IF_ARGS [20 60] 153 30 case depth = 0 inline depth = 1 depth based penalty = 0 adjusted size = 123 ANSWER = NO
Considering inlining: inlSz arg infos [ValueArg, TrivArg] interesting continuation BoringCtxt some_benefit True is exp: True is work-free: True guidance IF_ARGS [20 60] 153 30 case depth = 0 inline depth = 1 depth based penalty = 0 adjusted size = 103 ANSWER = NO
Considering inlining: inlSz arg infos [NonTrivArg, TrivArg] interesting continuation BoringCtxt some_benefit True is exp: True is work-free: True guidance IF_ARGS [20 60] 153 30 case depth = 0 inline depth = 1 depth based penalty = 0 adjusted size = 113 ANSWER = NO
Considering inlining: inlSz arg infos [ValueArg, TrivArg] interesting continuation CaseCtxt some_benefit True is exp: True is work-free: True guidance IF_ARGS [20 60] 153 30 case depth = 0 inline depth = 1 depth based penalty = 0 adjusted size = 73 ANSWER = YES
```

In `thr110` the call at 103 is taken and the one at 113 is not:

```
Considering inlining: inlSz arg infos [ValueArg, TrivArg] interesting continuation BoringCtxt some_benefit True ... adjusted size = 103 ANSWER = YES
Considering inlining: inlSz arg infos [NonTrivArg, TrivArg] interesting continuation BoringCtxt some_benefit True ... adjusted size = 113 ANSWER = NO
```

The Core of `valueK`, in `base` and in `thr110`:

```
valueK = \ y -> Just (inlSz valueK1 y)
valueK = \ y -> Just (case y of { I# x -> I# (-# x 3#) })
```

**Reproduces small:** yes.

### A05. INLINE is taken whatever the body's size; without it, a body past the creation threshold is inlined at a call only by `inline` (A13), unless the call is its only occurrence (A16)

**Rule.** An INLINE pragma gives `UnfWhen` guidance, which records no size, and `tryUnfolding` takes an `UnfWhen` unfolding at a call with enough arguments and a benefit (A01) without measuring it. Without a pragma, `calcUnfoldingGuidance` runs `sizeExpr` with `-funfolding-creation-threshold` (default 750) as its limit; past it the size is `TooBig` and the guidance `UnfNever`, for which `tryUnfolding` returns `Nothing` at every call, whatever the arguments and context. Below it, the use threshold of A04 applies. So a function past the creation threshold is inlined once it carries INLINE, which a library function one cannot annotate gets only through a copy of its definition, carrying the pragma, in a module of one's own. The `inline` function takes even an `UnfNever` unfolding (A13). Source: [compiler/GHC/Core/Opt/Simplify/Inline.hs#L308][g38] (`tryUnfolding`, `UnfNever`) and [#L310][g5] (`UnfWhen`); [compiler/GHC/Core/Unfold.hs#L349][g23] (`calcUnfoldingGuidance`, `TooBig -> UnfNever`), [#L1076][g39] (`mkSizeIs`, which subtracts the result discount before comparing with the limit); [compiler/GHC/Core/Unfold/Make.hs#L157][g10] (`mkInlineUnfoldingWithArity`).

**Seen.** Orthotope's benchmark: the step of `zipWith`'s `foldr2/left`, declined as too big, would be taken under an explicit INLINE on a local loop of the library's own.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A05-inline-ignores-size`, variant `base`, `-dinline-check inl`, and `-fno-worker-wrapper` so that the pragma-free functions keep their own guidance, A26): a body too big for the use threshold and one past the creation threshold, each without a pragma and with INLINE, each called with a literal for the scrutinised argument under a `case`.

```haskell
module M (inlBig, inlBigI, inlHuge, inlHugeI, useBig, useBigI, useHuge, useHugeI) where

inlBig :: Int -> Int -> Int
inlBig k y = case k of
  0 -> y + 1
  1 -> y * 2
  2 -> y - 3
  3 -> y * y
  4 -> y `div` 5
  _ -> y

{-# INLINE inlBigI #-}
inlBigI :: Int -> Int -> Int
inlBigI k y = case k of
  0 -> y + 1
  1 -> y * 2
  2 -> y - 3
  3 -> y * y
  4 -> y `div` 5
  _ -> y - 1

inlHuge :: Int -> Int -> Int
inlHuge k y = case k of
  1 -> y * 8 + 1
  2 -> y * 9 + 2
  -- ... forty alternatives, n -> y * (n + 7) + n
  40 -> y * 47 + 40
  _ -> y

{-# INLINE inlHugeI #-}
inlHugeI :: Int -> Int -> Int
inlHugeI k y = case k of
  1 -> y * 8 + 1
  -- ... the same forty alternatives
  40 -> y * 47 + 40
  _ -> y - 1

useBig, useBigI, useHuge, useHugeI :: Int -> Bool
useBig y = case inlBig 3 y of { 0 -> True; _ -> False }
useBigI y = case inlBigI 3 y of { 0 -> True; _ -> False }
useHuge y = case inlHuge 3 y of { 0 -> True; _ -> False }
useHugeI y = case inlHugeI 3 y of { 0 -> True; _ -> False }
```

The decisions, whitespace collapsed (`inlBig`'s last one, its size having shrunk over the simplifier's iterations):

```
Considering inlining: inlHuge UnfNever
Considering inlining: inlHugeI arg infos [ValueArg, TrivArg] interesting continuation BoringCtxt some_benefit True is exp: True is work-free: True guidance ALWAYS_IF(arity=2,unsat_ok=False,boring_ok=False) case depth = 0 inline depth = 1 ANSWER = YES
Considering inlining: inlBigI arg infos [ValueArg, TrivArg] interesting continuation BoringCtxt some_benefit True is exp: True is work-free: True guidance ALWAYS_IF(arity=2,unsat_ok=False,boring_ok=False) case depth = 0 inline depth = 1 ANSWER = YES
Considering inlining: inlBig arg infos [ValueArg, TrivArg] interesting continuation CaseCtxt some_benefit True is exp: True is work-free: True guidance IF_ARGS [20 80] 187 40 case depth = 0 inline depth = 1 depth based penalty = 0 adjusted size = 97 ANSWER = NO
```

The Core, heads of the four:

```
useBig = \ y -> case inlBig useBig1 y of { I# ds -> ...
useHuge = \ y -> case inlHuge useBig1 y of { I# ds -> ...
useBigI = \ y -> case y of { I# x -> case *# x x of { ...
useHugeI = \ y -> case y of { I# x -> case *# x 10# of { ...
```

**Reproduces small:** yes.

### A06. Without INLINE only a work-free unfolding is inlined at a call; a binding with no arguments under INLINE is inlined at every use

**Rule.** `tryUnfolding` takes an `UnfIfGoodArgs` unfolding, a join point's excepted (A18), only if it is work-free (`exprIsWorkFree`, cached in the unfolding): a lambda, a constructor application, a variable, or similar. A thunk such as `x = f 3` is not, so at a call site it is never inlined however small and however interesting the context, a `case` on it included; only pre- and post-inlining (A16, A17) and the `inline` function (A13) inline it. The `UnfWhen` case does not consult work-freeness. An INLINE pragma on a binding with no arguments gives `UnfWhen` with arity 0 and `boring_ok` true, so it is inlined at every occurrence, the work of its body duplicated at each, as Note [Honour INLINE on 0-ary bindings] intends; full laziness may then float a copy back out as a new top-level binding, which recomputes what the original binding computes. Source: [compiler/GHC/Core/Opt/Simplify/Inline.hs#L323][g40] (`is_wf, some_benefit, small_enough`); [compiler/GHC/Core/Unfold/Make.hs#L372][g41] (`is_work_free = exprIsWorkFree expr`), [#L169][g11] (`boring_ok | arity == 0 = True`), [#L267][g42] (Note [Honour INLINE on 0-ary bindings]); [compiler/GHC/Core/Utils.hs#L1937][g43] (`exprIsWorkFree`).

**Seen.** Not in our record.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A06-work-free-and-zero-arity`, variant `base`, `-dinline-check inl`): the same thunk without a pragma and with INLINE, each scrutinised and passed lazily.

```haskell
module M (expensive, inlCaf, inlCafI, useCaf, useCafI) where

{-# NOINLINE expensive #-}
expensive :: Int -> Int
expensive n = sum [1 .. n]

inlCaf :: Int
inlCaf = expensive 100

{-# INLINE inlCafI #-}
inlCafI :: Int
inlCafI = expensive 200

useCaf, useCafI :: Int -> (Int, Maybe Int)
useCaf y = (case inlCaf of { 0 -> y; _ -> 1 }, Just inlCaf)
useCafI y = (case inlCafI of { 0 -> y; _ -> 1 }, Just inlCafI)
```

The decisions, whitespace collapsed:

```
Considering inlining: inlCaf arg infos [] interesting continuation CaseCtxt some_benefit True is exp: False is work-free: False guidance IF_ARGS [] 30 0 case depth = 0 inline depth = 1 depth based penalty = 0 adjusted size = 20 ANSWER = NO
Considering inlining: inlCafI arg infos [] interesting continuation BoringCtxt some_benefit False is exp: False is work-free: False guidance ALWAYS_IF(arity=0,unsat_ok=False,boring_ok=True) case depth = 0 inline depth = 1 ANSWER = YES
```

The Core: `useCaf` refers to `inlCaf`; `useCafI` refers to a second binding computing `expensive 200` again.

```
useCaf1 = Just inlCaf
  (case inlCaf of { I# ds -> ...
inlCafI = case $wexpensive 200# of ww { __DEFAULT -> I# ww }
useCafI2 = case $wexpensive 200# of ww { __DEFAULT -> I# ww }
useCafI1 = Just useCafI2
```

**Reproduces small:** yes.

### A07. An argument earns its discount only as a value: a call or a merely evaluated variable earns 10, a lambda-bound variable nothing

**Rule.** `interestingArg` summarises each value argument of a call, before the arguments are simplified: `ValueArg` for a literal, a lambda, a partial application (a variable of arity greater than its arguments), a variable whose unfolding is a constructor application or CONLIKE (a dictionary function included), and a variable known not to be some constructors (`OtherCon [c ..]`, as in the default branch of a `case` on it); `NonTrivArg` for a saturated or unknown call, an applied lambda, a `case`, a `let` whose body is not a value, a variable known only to be evaluated (`OtherCon []`, as after `seq`), a variable with an expandable unfolding, and a rubbish literal; `TrivArg` for a type, a coercion, and a variable with no unfolding (a lambda-bound one) or with one neither CONLIKE nor expandable (a let-bound thunk). A04 gives what each earns: `ValueArg` the callee's discount for that argument, `NonTrivArg` 10, `TrivArg` nothing; and any summary other than `TrivArg` makes `some_benefit` (A03). Source: [compiler/GHC/Core/Opt/Simplify/Utils.hs#L1146][g44] (`interestingArg`), [#L1072][g45] (Note [Interesting arguments], wrinkles (IA1) to (IA4)); [compiler/GHC/Core/Opt/Simplify/Utils.hs#L593][g46] (`contArgs`, which applies it to the call's arguments); [compiler/GHC/Core/Opt/Simplify/Inline.hs#L725][g47] (`mk_arg_discount`).

**Seen.** Not in our record.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A07-argument-summary`, variant `base`, `-dinline-check inl`, and `-fno-worker-wrapper` so that the callees keep their own guidance, A26): one callee per kind of argument, each called as a lazy constructor argument.

```haskell
module M where

inlCon, inlVar, inlCall, inlOther, inlEvald :: Maybe Int -> Int
inlCon m = case m of { Nothing -> 1; Just v -> v * 3 + 1 }
inlVar m = case m of { Nothing -> 2; Just v -> v * 3 + 2 }
inlCall m = case m of { Nothing -> 3; Just v -> v * 3 + 3 }
inlOther m = case m of { Nothing -> 4; Just v -> v * 3 + 4 }
inlEvald m = case m of { Nothing -> 5; Just v -> v * 3 + 5 }

inlPap, inlLam, inlFVar :: (Int -> Int) -> Int
inlPap f = f 1 + f 2
inlLam f = f 3 + f 4
inlFVar f = f 5 + f 6

{-# NOINLINE mk #-}
mk :: Int -> Maybe Int
mk x = Just x

{-# NOINLINE add #-}
add :: Int -> Int -> Int
add x y = x + y

kCon :: Maybe Int
kCon = Just 3

aCon :: Maybe Int
aCon = Just (inlCon kCon)                 -- a variable bound to a constructor

aVar :: Maybe Int -> Maybe Int
aVar m = Just (inlVar m)                  -- a lambda-bound variable

aCall :: Int -> Maybe Int
aCall x = Just (inlCall (mk x))           -- a saturated call

aOther :: Maybe Int -> Maybe Int
aOther m = case m of
  Nothing -> Nothing
  _ -> Just (inlOther m)                  -- known not to be Nothing

aEvald :: Maybe Int -> Maybe Int
aEvald m = m `seq` Just (inlEvald m)      -- known to be evaluated

aPap :: Int -> Maybe Int
aPap x = Just (inlPap (add x))            -- a partial application

aLam :: Int -> Maybe Int
aLam x = Just (inlLam (\y -> y * x))      -- a lambda

aFVar :: (Int -> Int) -> Maybe Int
aFVar f = Just (inlFVar f)                -- a lambda-bound function
```

The first decision for each callee, whitespace collapsed and shortened after `some_benefit`:

```
Considering inlining: inlCon arg infos [ValueArg] interesting continuation BoringCtxt some_benefit True ...
Considering inlining: inlVar arg infos [TrivArg] interesting continuation BoringCtxt some_benefit False is exp: True is work-free: True guidance IF_ARGS [40] 52 20 case depth = 0 inline depth = 1 depth based penalty = 0 adjusted size = 32 ANSWER = NO
Considering inlining: inlCall arg infos [NonTrivArg] interesting continuation BoringCtxt some_benefit True is exp: True is work-free: True guidance IF_ARGS [40] 52 20 case depth = 0 inline depth = 1 depth based penalty = 0 adjusted size = 22 ANSWER = YES
Considering inlining: inlOther arg infos [ValueArg] interesting continuation BoringCtxt some_benefit True ...
Considering inlining: inlEvald arg infos [NonTrivArg] interesting continuation BoringCtxt some_benefit True ...
Considering inlining: inlPap arg infos [ValueArg] interesting continuation BoringCtxt some_benefit True ...
Considering inlining: inlLam arg infos [ValueArg] interesting continuation BoringCtxt some_benefit True is exp: True is work-free: True guidance IF_ARGS [60] 91 10 case depth = 0 inline depth = 1 depth based penalty = 0 adjusted size = 11 ANSWER = YES
Considering inlining: inlFVar arg infos [TrivArg] interesting continuation BoringCtxt some_benefit False is exp: True is work-free: True guidance IF_ARGS [60] 91 10 case depth = 0 inline depth = 1 depth based penalty = 0 adjusted size = 71 ANSWER = NO
```

The two `TrivArg` calls stay:

```
aVar = \ m -> Just (inlVar m)
aFVar = \ f -> Just (inlFVar f)
```

**Reproduces small:** yes.

### A08. The call's context is taken from its continuation, and some strict positions count as boring

**Rule.** `interestingCallContext` maps what consumes the call's result to a `CallCtxt`, which A03 and A04 use. A `case` gives `CaseCtxt`, a `seq` with a dead case binder included, except that a `case` with a live case binder and a single alternative whose binders are all dead (a bang pattern on a let, `let !r = f x in ...r...`) gives `RhsCtxt NonRecursive`, as a strict let would (Note [Seq is boring]). An argument of a function with RULES, or inside such an argument, gives `RuleArgCtxt`; otherwise an argument in a position where the function has a nonzero argument discount gives `DiscArgCtxt`; otherwise a strict argument gives `RhsCtxt NonRecursive` and a lazy one `BoringCtxt`. The right-hand side of a non-recursive let gives `RhsCtxt NonRecursive`, of a recursive one `RhsCtxt Recursive`; a let whose binder demand analysis has found demanded is simplified at every iteration with a `StrictBind` continuation, which gives `BoringCtxt`, and stays a let (`completeBindX`, [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L1670][g48]); so that context decides a call where a demand analysis has run before the simplifier run that first considers the call, as when `-fstrictness-before=N` adds one before phase N's run (`maybe_strictness_before`, [compiler/GHC/Core/Opt/Pipeline.hs#L152][g49]). In the first, gentle simplifier run, case-of-case is off: a `case` scrutinee then gives `BoringCtxt` (Note [No case of case is boring]) and a strict argument is simplified as a lazy one, `BoringCtxt` too, so a call under a `case` is first refused and taken in a later run. `ValAppCtxt` is reached only through a tick: `contArgs` takes every value argument through casts and type arguments before the context is computed, so `(f x |> co) y` is a call of `f` with two arguments, and only a `TickIt` continuation could stand between the call and a further value argument; the two places that would build a `TickIt` for a tick are commented out in `simplTick` ([compiler/GHC/Core/Opt/Simplify/Iteration.hs#L1469][g50] and [#L1546][g51]), the others only rebuild or consume an existing one ([#L1620][g52], [#L1952][g53], [#L4155][g54]), and no module outside the two simplifier modules names it. So `ValAppCtxt` does not arise on this tree, with `-g` or without. A tick that is not soft-scoped, such as a scoped cost centre, instead keeps outside it everything of the continuation but its type arguments and casts, so that a call inside it gets a boring stop in place of its value arguments and context (`no_floating_past_tick`, [Iteration.hs#L1522][g55], and `splitCont`, [#L1556][g56]) and stays a call; a source note, being soft-scoped, takes the continuation inside it instead (`tickishHasSoftScope`, [compiler/GHC/Types/Tickish.hs#L294][g57]). Source: [compiler/GHC/Core/Opt/Simplify/Utils.hs#L1000][g58] (`interestingCallContext`), [#L977][g9] and [#L984][g59] (`lazyArgContext`, `strictArgContext`), [#L887][g60] (Note [Seq is boring]), [#L874][g61] (Note [No case of case is boring]), [#L1059][g62] (`contHasRules`), [#L593][g46] (`contArgs`), [#L474][g63] (`mkRhsStop`); [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L2524][g64] (`tryInlining`, the only caller), [#L2490][g65] (`rebuildCall`, strict arguments only with `seCaseCase`), [#L1285][g66] (`simplExprF1`, a case scrutinee with `mkBoringStop` when `seCaseCase` is off), [#L2004][g67] (`simplNonRecE`, `StrictBind` for a demanded let); [compiler/GHC/Driver/Config/Core/Opt/Simplify.hs#L79][g68] (`initGentleSimplMode`, `sm_case_case = False`); [compiler/GHC/Core/Opt/Pipeline.hs#L189][g69] (`core_todo`: the demand analyser, [#L261][g70], after the phase-0 simplifier run).

**Seen.** Not in our record.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A08-call-contexts`, variant `base`, `-dinline-check inl`): one INLINE callee, not tiny, per context; `N.strictNoUnf` is strict and NOINLINE, so the interface gives its strictness and no unfolding, hence no discount. The demanded let and the cost centre are the second repro's.

```haskell
module N (strictNoUnf) where

{-# NOINLINE strictNoUnf #-}
strictNoUnf :: Maybe Int -> Int
strictNoUnf m = case m of { Nothing -> 0; Just v -> v + 1 }
```

```haskell
{-# LANGUAGE BangPatterns #-}
module M where

import N (strictNoUnf)

{-# INLINE inlCase #-}
inlCase :: Int -> Maybe Int
inlCase x = case x of { 0 -> Nothing; _ -> Just (x + 0) }

-- inlSeqLive, inlSeqDead, inlStrict, inlDisc, inlRule, inlLet, inlLazy:
-- the same with the literals 1 to 7.

{-# INLINE inlRec #-}
inlRec :: Int -> Maybe Int -> Maybe Int
inlRec x r = case x of { 9 -> r; _ -> Just (x + 9) }

{-# NOINLINE discFun #-}
discFun :: Maybe Int -> Int
discFun m = case m of { Nothing -> 0; Just v -> v }

{-# NOINLINE ruleFun #-}
ruleFun :: Maybe Int -> Int
ruleFun _ = 0
{-# RULES "ruleFun/Just" forall v. ruleFun (Just v) = v #-}

ctxCase, ctxSeqDead, ctxStrict, ctxDisc, ctxRule :: Int -> Int
ctxCase x = case inlCase x of { Nothing -> 0; Just v -> v }
ctxSeqDead x = inlSeqDead x `seq` 1
ctxStrict x = strictNoUnf (inlStrict x)
ctxDisc x = discFun (inlDisc x)
ctxRule x = ruleFun (inlRule x)

ctxSeqLive, ctxLet :: Int -> (Maybe Int, Maybe Int)
ctxSeqLive x = let !r = inlSeqLive x in (r, r)
ctxLet x = let y = inlLet x in (y, y)

ctxLazy :: Int -> Maybe (Maybe Int)
ctxLazy x = Just (inlLazy x)

ctxRec :: Int -> Maybe Int
ctxRec x = let r = inlRec x r in r
```

The decisions, whitespace collapsed and shortened after `some_benefit`; `inlCase`, `inlSeqDead`, `inlSeqLive` and `inlStrict` are first decided in the gentle run, in `BoringCtxt`, and not inlined there, shown for `inlCase` and `inlStrict`:

```
Considering inlining: inlCase arg infos [TrivArg] interesting continuation BoringCtxt some_benefit False is exp: True is work-free: True guidance ALWAYS_IF(arity=1,unsat_ok=False,boring_ok=False) case depth = 0 inline depth = 1 ANSWER = NO
Considering inlining: inlCase arg infos [TrivArg] interesting continuation CaseCtxt some_benefit True ...
Considering inlining: inlSeqDead arg infos [TrivArg] interesting continuation CaseCtxt some_benefit True ...
Considering inlining: inlSeqLive arg infos [TrivArg] interesting continuation RhsCtxt(NonRecursive) some_benefit True ...
Considering inlining: inlStrict arg infos [TrivArg] interesting continuation BoringCtxt some_benefit False ...
Considering inlining: inlStrict arg infos [TrivArg] interesting continuation RhsCtxt(NonRecursive) some_benefit True ...
Considering inlining: inlDisc arg infos [TrivArg] interesting continuation DiscArgCtxt some_benefit True ...
Considering inlining: inlRule arg infos [TrivArg] interesting continuation RuleArgCtxt some_benefit True ...
Considering inlining: inlLet arg infos [TrivArg] interesting continuation RhsCtxt(NonRecursive) some_benefit True ...
Considering inlining: inlLazy arg infos [TrivArg] interesting continuation BoringCtxt some_benefit False ...
Considering inlining: inlRec arg infos [TrivArg, TrivArg] interesting continuation RhsCtxt(Recursive) some_benefit False is exp: True is work-free: True guidance ALWAYS_IF(arity=2,unsat_ok=False,boring_ok=False) case depth = 0 inline depth = 1 ANSWER = NO
```

The two refused calls stay:

```
ctxRec = \ x -> letrec { r = inlRec x r; } in r
ctxLazy = \ x -> Just (inlLazy x)
```

Whether `ValAppCtxt` arises was probed in `~/r/horde-ad/dist-inlcat/cases/A31-debug-info-changes-floating` (variants `plain` and `g1`, with `-dinline-check inlVal`): every `Considering inlining: inlVal` in its `build.log` reads `interesting continuation BoringCtxt`, and none `ValAppCtxt`; the desugarer puts no source note on `(inlVal x)` alone (`-ddump-ds` in `g1ticks`), and the notes it puts on the `let`, `if` and `case` around the other calls are pushed outside.

A second repro (`~/r/horde-ad/dist-inlcat/cases/A08-strictbind-and-scc`, variants `base`, `-dinline-check inl`; `strictbefore1`, with `-fstrictness-before=1`, `-dinline-check inlP1`; `prof`, `base` with `-prof`): a call of an INLINE `[1]` function in a demanded let, and a call in a `case` scrutinee with and without a cost centre around it.

```haskell
module M where

import N (strictNoUnf)

{-# INLINE [1] inlP1 #-}
inlP1 :: Int -> Maybe Int
inlP1 x = case x of { 0 -> Nothing; _ -> Just (x + 1) }

ctxDemandedLet :: Int -> Int
ctxDemandedLet x = let y = inlP1 x in strictNoUnf y + strictNoUnf (fmap negate y)

{-# INLINE inlScc #-}
inlScc :: Int -> Maybe Int
inlScc x = case x of { 0 -> Nothing; _ -> Just (x + 2) }

ctxScc :: Int -> Int
ctxScc x = case {-# SCC "c" #-} inlScc x of { Nothing -> 0; Just v -> v }

{-# INLINE inlNoScc #-}
inlNoScc :: Int -> Maybe Int
inlNoScc x = case x of { 0 -> Nothing; _ -> Just (x + 3) }

ctxNoScc :: Int -> Int
ctxNoScc x = case inlNoScc x of { Nothing -> 0; Just v -> v }
```

`N` is the first repro's. In `base` the demanded let's call is decided in its let's context, before demand analysis runs: `Considering inlining: inlP1 arg infos [TrivArg] interesting continuation RhsCtxt(NonRecursive) some_benefit True`, and never in `BoringCtxt`. In `strictbefore1` it is first considered after the added demand analysis, under `StrictBind`, `Considering inlining: inlP1 arg infos [TrivArg] interesting continuation BoringCtxt some_benefit False`, refused four times, and taken only once its argument is a value, `Considering inlining: inlP1 arg infos [ValueArg] interesting continuation BoringCtxt some_benefit True`. In `prof`, every decision on `inlScc` is `Considering inlining: inlScc arg infos [TrivArg] interesting continuation BoringCtxt some_benefit False`, refused, and the Core keeps the call, `ctxScc = \ x -> case scctick<c> inlScc x of { Nothing -> ctxNoScc1; Just v -> v }`, while the same call without the cost centre is decided in `Considering inlining: inlNoScc arg infos [TrivArg] interesting continuation CaseCtxt some_benefit True` and taken.

A third repro (`~/r/horde-ad/dist-inlcat/cases/A08-strictbind-first-decision`, variants `base`, `-dinline-check f`, and `v2c`, with `-dverbose-core2core` too): a self-recursive `f`, its own loop breaker until worker/wrapper splits it, called under a demanded let.

```haskell
module M (g) where

f :: [Int] -> Int
f [] = 0
f (x:xs) = x + f xs

{-# NOINLINE h #-}
h :: Int -> Int -> [Int]
h a b = a `seq` b `seq` [a, b]

g :: [Int] -> [Int]
g xs = let r = f xs in h r r
```

In the default pipeline no let binder is demanded before the first demand analysis, which `core_todo` runs after phase 0's run ([compiler/GHC/Core/Opt/Pipeline.hs#L261][g70]): `simplNonRecE` takes `StrictBind` only for `isStrUsedDmd (idDemandInfo bndr)` ([compiler/GHC/Core/Opt/Simplify/Iteration.hs#L2028][g71]), demand information is set by demand analysis (`setBindIdDemandInfo`, [compiler/GHC/Core/Opt/DmdAnal.hs#L314][g72]), and no interface carries it (`IfaceInfoItem`, [compiler/GHC/Iface/Syntax.hs#L470][g73]). So a call is first decided under `StrictBind` only where no earlier run decided it, as here: `g = \ xs -> let { r = f xs } in h r r` reaches demand analysis unchanged (`v2c`'s `M.dump-dmdanal`), and the first decision on its call, in the post-worker-wrapper run, is `Considering inlining: f arg infos [TrivArg] interesting continuation BoringCtxt some_benefit False`, `ANSWER = NO` (`build.log`), the wrapper reaching `g` in the next iteration, where `f` occurs once (A16): `g = \ xs -> case $wf xs of ww { __DEFAULT -> let { r = I# ww } in h r r }` (`M.dump-simpl`).

**Reproduces small:** yes: the demanded let's `BoringCtxt` where a demand analysis precedes the call's first simplifier run, and a cost centre's boring stop; in the default pipeline the demanded let's call has already been decided in an earlier context, unless its callee becomes inlinable only once worker/wrapper splits it, as the third repro's self-recursive `f`, a loop breaker until then (A11). `ValAppCtxt` does not arise, by the source, and the probe shows the same for source notes.

### A09. Without INLINE, a call of a body bigger than the call, nested in more than `-funfolding-case-threshold` multi-way cases (2 by default), pays a size penalty growing with the depth

**Rule.** The simplifier counts in `seCaseDepth` the multi-way cases it is inside: `mkDupableCaseCont` bumps it for a `case` with more than one alternative that does not diverge. For `UnfIfGoodArgs` guidance, `tryUnfolding` adds `size * (depth - t) / s` to the adjusted size when the depth exceeds `t = -funfolding-case-threshold` (default 2), with `s = -funfolding-case-scaling` (default 30). So the same call of the same function, with the same arguments and context, is inlined near the top of a function and refused deep in a nest of cases; the depth is the total from the top of the binding being simplified, not from the callee's definition (Note [Avoid inlining into deeply nested cases], its second wrinkle). `UnfWhen` guidance, under INLINE or for a tiny body, pays no penalty. Source: [compiler/GHC/Core/Opt/Simplify/Inline.hs#L331][g74] (`depth_penalty`), [#L153][g75] (Note [Avoid inlining into deeply nested cases]); [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4097][g76] (`mkDupableCaseCont`, `bumpCaseDepth`), [#L4108][g77] (`altsWouldDup`); [compiler/GHC/Core/Unfold.hs#L119][g78] (the defaults).

**Seen.** Not in our record.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A09-case-depth-penalty`, variants `base` and `thr6`, both `-dinline-check inl` and `-fno-worker-wrapper`, the latter so that `inlD` keeps its own guidance, A26; `thr6` adds `-funfolding-case-threshold=6`): A04's function called the same way under one two-way case and under seven.

```haskell
module M (inlD, shallow, deep) where

inlD :: Int -> Int -> Int
inlD k y = case k of
  0 -> y + 1
  1 -> y * 2
  2 -> y - 3
  3 -> y * y
  _ -> y

shallow :: Bool -> Int -> Maybe Bool
shallow a y = case a of
  False -> Nothing
  True -> Just (case inlD 2 y of { 0 -> True; _ -> False })

deep :: Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Int -> Maybe Bool
deep a b c d e f g y =
  case a of
    False -> Nothing
    True -> case b of
      -- ... and so on through c, d, e and f
              True -> case g of
                False -> Nothing
                True -> Just (case inlD 2 y of { 0 -> True; _ -> False })
```

The decisions, whitespace collapsed; the penalty is 153 * 5 / 30 in `base` and 153 * 1 / 30 in `thr6`:

```
Considering inlining: inlD arg infos [ValueArg, TrivArg] interesting continuation CaseCtxt some_benefit True is exp: True is work-free: True guidance IF_ARGS [20 60] 153 30 case depth = 1 inline depth = 1 depth based penalty = 0 adjusted size = 73 ANSWER = YES
Considering inlining: inlD arg infos [ValueArg, TrivArg] interesting continuation CaseCtxt some_benefit True is exp: True is work-free: True guidance IF_ARGS [20 60] 153 30 case depth = 7 inline depth = 1 depth based penalty = 25 adjusted size = 98 ANSWER = NO
```

and in `thr6`:

```
Considering inlining: inlD arg infos [ValueArg, TrivArg] interesting continuation CaseCtxt some_benefit True is exp: True is work-free: True guidance IF_ARGS [20 60] 153 30 case depth = 7 inline depth = 1 depth based penalty = 5 adjusted size = 78 ANSWER = YES
```

In `base`, `deep` keeps the call, `(case inlD deep1 y of { I# ds -> ...`; in `thr6` it does not.

**Reproduces small:** yes.

### A10. A phase on a pragma makes the unfolding inactive outside its phases; `[k]` and `[~k]` mean the same for NOINLINE as for INLINE

**Rule.** `callSiteInline` takes no unfolding whose activation is inactive in the current simplifier phase (`Inactive unfolding:` in `-dinline-check` output); a compulsory unfolding is always active. The phases run initial (the gentle run), 2, 1, 0, then final repeatedly. The parser makes `[k]` `ActiveAfter k` and `[~k]` `ActiveBefore k` whichever pragma carries it, and an omitted phase `AlwaysActive` for INLINE and INLINABLE and `NeverActive` for NOINLINE and OPAQUE. So INLINE [1] and NOINLINE [1] are both first inlined in phase 1 (NOINLINE [1] then as a binding without a pragma), and INLINE [~1] and NOINLINE [~1] already in the gentle run and no longer from phase 1. `ActiveAfter k` is inactive in the initial phase, so INLINE [2] is not inlined in the gentle run. The gentle run otherwise inlines like the later ones (its mode sets `sm_inline`, and `activeUnfolding` tests only that and the phase): a function without a pragma is inlined there too, contrary to Note [Inlining in gentle mode] (section 6, item 3); and the parser's reading of NOINLINE's phase is contrary to Note [inl_inline and inl_act] (section 6, item 2). Source: [compiler/GHC/Core/Opt/Simplify/Inline.hs#L110][g79] and [#L113][g80] (`callSiteInline`), [#L122][g81] (`activeUnfolding`); [compiler/GHC/Core/Opt/Simplify/Env.hs#L331][g82] (`isActive`); [compiler/GHC/Types/InlinePragma.hs#L443][g83] (`isActiveInPhase`), [#L354][g84] (`activeInPhase`), [#L382][g85] (`activeInInitialPhase`); [compiler/GHC/Parser.y#L2861][g86] (`explicit_activation`); [compiler/GHC/Parser/PostProcess.hs#L3094][g87] (`mkInlinePragma`); [compiler/GHC/Driver/Config/Core/Opt/Simplify.hs#L79][g68] (`initGentleSimplMode`, inheriting `sm_inline = True`).

**Seen.** `docs/perf-checklist.md` P, "Common principles": a phase control, `INLINE [n]`, kept to order inlining against rules or specialisation (horde-ad's `tscatterZRDict` and `tscatterZSDict`).

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A10-activation-phases`, variant `base` with `-dverbose-core2core` and `-dinline-check inl`; then, from its `post` hook, `python3 phases.py`, which writes `~/r/horde-ad/dist-inlcat/cases/A10-activation-phases/out/head/base/phases.txt`: for each `Simplifier` pass in `M.verbose-core2core`, the phase its header names and, for each caller and callee the table lists, whether the caller's right-hand side still names the callee): four functions with `[1]` and `[~1]` on INLINE and NOINLINE and one without a pragma, each called with a literal under a `case`, and an INLINE [1] function calling the INLINE [~1] one, `outer`, for U10's rule.

```haskell
module M where

{-# INLINE [1] inlI1 #-}
inlI1 :: Int -> Maybe Int
inlI1 x = case x of { 1 -> Nothing; _ -> Just (x + 1) }

{-# INLINE [~1] inlIT1 #-}
inlIT1 :: Int -> Maybe Int
inlIT1 x = case x of { 2 -> Nothing; _ -> Just (x + 2) }

{-# NOINLINE [1] inlN1 #-}
inlN1 :: Int -> Maybe Int
inlN1 x = case x of { 3 -> Nothing; _ -> Just (x + 3) }

{-# NOINLINE [~1] inlNT1 #-}
inlNT1 :: Int -> Maybe Int
inlNT1 x = case x of { 4 -> Nothing; _ -> Just (x + 4) }

useI1, useIT1, useN1, useNT1 :: Int
useI1 = case inlI1 5 of { Nothing -> 0; Just v -> v }
useIT1 = case inlIT1 5 of { Nothing -> 0; Just v -> v }
useN1 = case inlN1 5 of { Nothing -> 0; Just v -> v }
useNT1 = case inlNT1 5 of { Nothing -> 0; Just v -> v }

{-# INLINE [1] outer #-}
outer :: Int -> Int
outer x = case inlIT1 x of { Nothing -> 0; Just v -> v }

useOuter :: Int
useOuter = outer 5

inlPlain :: Int -> Maybe Int
inlPlain x = case x of { 6 -> Nothing; _ -> Just (x + 6) }

usePlain :: Int
usePlain = case inlPlain 5 of { Nothing -> 0; Just v -> v }
```

The table (`call`: the call is still there; `-`: gone):

```
initial [Gentle] | useI1:inlI1=call useIT1:inlIT1=- useN1:inlN1=call useNT1:inlNT1=- useOuter:outer=call useOuter:inlIT1=- usePlain:inlPlain=-
2 [main] | useI1:inlI1=call useIT1:inlIT1=- useN1:inlN1=call useNT1:inlNT1=- useOuter:outer=call useOuter:inlIT1=- usePlain:inlPlain=-
1 [main] | useI1:inlI1=- useIT1:inlIT1=- useN1:inlN1=- useNT1:inlNT1=- useOuter:outer=- useOuter:inlIT1=call usePlain:inlPlain=-
...
final [final] | useI1:inlI1=- useIT1:inlIT1=- useN1:inlN1=- useNT1:inlNT1=- useOuter:outer=- useOuter:inlIT1=call usePlain:inlPlain=-
```

`outer`'s unfolding in the interface keeps the call, and so does the final Core:

```
   CPR: 1, Inline: [1] (sat-args=1),
   Unfolding: Core: StableUser <1,FalseFalse>
              \ (x['GHC.Internal.Types.Many] :: GHC.Internal.Types.Int) ->
              case inlIT1 x of wild {
useOuter = case inlIT1 useOuter2 of { Nothing -> useOuter1; Just v -> v }
```

`inlPlain`'s decision in the gentle run, whitespace collapsed:

```
Considering inlining: inlPlain arg infos [ValueArg] interesting continuation BoringCtxt some_benefit True is exp: True is work-free: True guidance IF_ARGS [20] 51 20 case depth = 0 inline depth = 1 depth based penalty = 0 adjusted size = 11 ANSWER = YES
```

**Reproduces small:** yes.

### A11. A loop breaker is inlined only by `inline` (A13), INLINE or not, in its module or an importer; in a recursive group INLINE bindings are among the last chosen

**Rule.** In each recursive group the occurrence analyser marks enough bindings as strong loop breakers to cut every cycle, and `idUnfolding` of a strong loop breaker returns its unfolding trimmed to evaluatedness ([compiler/GHC/Types/Id.hs#L781][g88]; `unfoldingInfo`, `trimUnfolding`, [compiler/GHC/Types/Id/Info.hs#L611][g89]), so `callSiteInline` never considers it ([compiler/GHC/Core/Opt/Simplify/Inline.hs#L103][g90], the comment "idUnfolding checks for loop-breakers"): `-dinline-check` prints nothing for it. So too in an importer, whatever pragma or exposure flag gave it an unfolding (U05): the interface marks it `Unfolding(loop-breaker):`, loaded back as a strong loop breaker ([compiler/GHC/IfaceToCore.hs#L1868][g91]). `realUnfoldingInfo` keeps the unfolding for the specialiser, for demand analysis and for `hasInlineUnfolding` (U09). A self-recursive binding is always its own loop breaker (score 0), so INLINE on it does nothing at its calls (perf-checklist I2). Otherwise the binding with the lowest score is chosen (`nodeScore`, [compiler/GHC/Core/Opt/OccurAnal.hs#L1982][g92]; Note [Choosing loop breakers], [#L1318][g93]): a binding whose unfolding is inactive (NOINLINE) 0; a trivial right-hand side 10; a dictionary function 9; `UnfWhen` guidance (INLINE, or a body small enough for A02) 6; a constructor application 5; a stable unfolding (INLINABLE) 3; a binding occurring once 2; any other unfolding that can be inlined 1; no unfolding, or `UnfNever` guidance, 0. Ties go to the bigger binding, then to the previous loop breaker (`betterLB`, [#L2101][g94]; Note [Loop breakers, node scoring, and stability], [#L2126][g95]). So in a group of one INLINE binding and one without a pragma that is neither trivial nor small enough for A02, the latter is chosen and the INLINE one is inlined into it and at every call outside the group; in a group of two INLINE bindings, the bigger one is chosen and never inlined (Note [Loop breakers and INLINE/INLINABLE pragmas], [#L1648][g96]; Note [Self-recursion and loop breakers], [#L2111][g97]). RULES add dependency edges (Note [Rules and loop breakers], [#L1438][g98]). The `inline` function takes a loop breaker's unfolding regardless (A13).

**Seen.** `docs/perf-checklist.md` I2: INLINE on a self-recursive function, and "an exposed loop breaker is still never inlined, so all that exposure or INLINABLE can buy there is cross-module specialisation". And `docs/ghc-issue-floatin-duplicate-values-appendix-d-session-notes.md` in horde-ad: a NOINLINE `Dict0 (ADReady Concrete)` moves the loop breaker of the `Concrete` dictionary cycle off `$ctlambda`, which can then be inlined.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A11-loop-breakers`, variants `base` with `-dinline-check inl`, and `occ`, `-O -ddump-occur-anal -dsuppress-uniques -dsuppress-module-prefixes -dsuppress-type-applications -dsuppress-coercions`; both `-fno-worker-wrapper`, since worker/wrapper would make `inlOdd` a non-recursive wrapper over a recursive worker, which then breaks the loop instead): a self-recursive INLINE function, a pair with one INLINE, a pair with both INLINE, each called with a literal under a `case`.

```haskell
module M where

{-# INLINE inlSelf #-}
inlSelf :: Int -> Int
inlSelf 0 = 0
inlSelf n = n + inlSelf (n - 1)

{-# INLINE inlEven #-}
inlEven :: Int -> Bool
inlEven 0 = True
inlEven n = inlOdd (n - 1)

inlOdd :: Int -> Bool
inlOdd 0 = False
inlOdd n = inlEven (n - 1)

{-# INLINE inlPing #-}
inlPing :: Int -> Int
inlPing 0 = 0
inlPing n = inlPong (n - 1) + 1

{-# INLINE inlPong #-}
inlPong :: Int -> Int
inlPong 0 = 1
inlPong n = inlPing (n - 1) * 2 + inlPing (n - 2)

useSelf, useEven, useOdd, usePing, usePong :: Int
useSelf = case inlSelf 3 of { 0 -> 1; _ -> 2 }
useEven = case inlEven 3 of { True -> 1; False -> 2 }
useOdd = case inlOdd 3 of { True -> 1; False -> 2 }
usePing = case inlPing 3 of { 0 -> 1; _ -> 2 }
usePong = case inlPong 3 of { 0 -> 1; _ -> 2 }
```

The loop breakers, from `-ddump-occur-anal`; `inlEven` and `inlPing` carry no `Occ=LoopBreaker`:

```
inlSelf [InlPrag=INLINE (sat-args=1), Occ=LoopBreaker]
inlOdd [Occ=LoopBreaker]
inlPong [InlPrag=INLINE (sat-args=1), Occ=LoopBreaker]
```

`-dinline-check inl` prints decisions for `inlEven` and `inlPing` and none for `inlSelf`, `inlOdd` or `inlPong`. The Core, heads:

```
useSelf = case inlSelf useOdd1 of ...
useEven = case inlOdd useEven2 of ...
usePing = case inlPong useEven2 of ...
```

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A11-loop-breaker-choice`, variants `base`, `idinfo` `-O -ddump-simpl -dsuppress-uniques -dsuppress-module-prefixes`, and `all` `-O -fexpose-all-unfoldings -dinline-check countDown`): two mutually recursive pairs with INLINE on opposite members, a self-recursive function, and an importer of all three.

```haskell
module A (evenI, oddI, evenN, oddN, countDown) where

-- Mutually recursive pairs, INLINE on one member of each.
evenI :: Int -> Bool
{-# INLINE evenI #-}
evenI 0 = True
evenI n = oddI (n - 1)

oddI :: Int -> Bool
oddI 0 = False
oddI n = evenI (n - 1)

evenN :: Int -> Bool
evenN 0 = True
evenN n = oddN (n - 1)

oddN :: Int -> Bool
{-# INLINE oddN #-}
oddN 0 = False
oddN n = evenN (n - 1)

-- Self-recursive: its own loop breaker, with or without an exposed unfolding.
countDown :: Int -> [Int]
countDown n = if n == 0 then [] else n : countDown (n - 1)
```

```haskell
module B (useEven, useOdd, useCount) where

import A

useEven :: Int -> Bool
useEven n = evenI (n + 1)

useOdd :: Int -> Bool
useOdd n = oddN (n + 2)

useCount :: Int -> Int
useCount n = length (countDown n)
```

In each pair the member without INLINE is the loop breaker, `$woddI [InlPrag=[2], Occ=LoopBreaker] :: Int# -> Bool` and `$wevenN [InlPrag=[2], Occ=LoopBreaker] :: Int# -> Bool`, with the INLINE member inlined into it (`__DEFAULT -> $woddI (-# wild 2#);`), and the INLINE member calls it:

```
evenI
  = \ ds ->
      case ds of { I# ds1 ->
      case ds1 of wild1 {
        __DEFAULT -> $woddI (-# wild1 1#);
        0# -> True
      }
      }
```

B inlines both INLINE members (`Inlining done: evenI`, `Inlining done: oddN`). With `-fexpose-all-unfoldings`, `countDown`'s interface entry carries `Strictness: <1P(SL)>, Unfolding(loop-breaker): Core: <vanilla> ...`, yet `-dinline-check countDown` prints no `Considering inlining: countDown` at all, and B calls it: `useCount = \ n -> case $wlenAcc (countDown n) 0# of ww1 { __DEFAULT -> I# ww1 }`.

**Reproduces small:** yes.

### A12. At a call, rules are tried before inlining on the arguments as written; a rule that needs the arguments simplified loses to an active unfolding

**Rule.** For a call of `f`, `simplOutId` first tries `f`'s rules on the arguments as written, substituted but not simplified (Plan BEFORE), and only if `f` is a class method or its unfolding is active; then tries inlining, deciding on those unsimplified arguments (A07); and only if `f` was not inlined simplifies the arguments and tries the rules again (Plan AFTER). So a rule on a function with an active unfolding fires when its left-hand side matches the arguments as written (the matcher, by `exprIsConApp_maybe`, expands an argument that unfolds to a constructor application, such as `mkJ y` below), and otherwise the function is inlined first and the rule never fires: in particular a rule whose argument pattern appears only after another rule or an inlining rewrites the argument. With the unfolding inactive (INLINE [1], NOINLINE), Plan BEFORE is skipped and Plan AFTER matches the simplified arguments, so such rule cascades work. `-Winline-rule-shadowing` warns for a rule on a function whose unfolding is active in the phase where the rule becomes active (`dsWarnRuleShadowing`, [compiler/GHC/HsToCore.hs#L470][g99]). Source: [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L2433][g100] (`simplOutId`), [#L2513][g101] (`rebuildCall`, Plan AFTER), [#L2579][g102] (Note [tryRules: plan (BEFORE)], GHC [#21851](https://gitlab.haskell.org/ghc/ghc/-/work_items/21851), GHC [#22097](https://gitlab.haskell.org/ghc/ghc/-/work_items/22097)), [#L2622][g103] (Note [tryRules: plan (AFTER)]); [compiler/GHC/Core/Opt/Simplify/Utils.hs#L1505][g104] (`getUnfoldingInRuleMatch`); [compiler/GHC/HsToCore/Errors/Ppr.hs#L236][g105] (the warning).

**Seen.** horde-ad's `mapAccumL'` keeps `INLINE [1]` because without it GHC warns that its RULES may never fire, `mapAccumL'` possibly inlining first (commit 8b78b6566, its comment there).

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A12-rules-before-inlining`, variant `base` with `-ddump-rule-firings` and `-dinline-check inl`): an INLINE function and an INLINE [1] one, each with a rule on `Just`, the first called with `Just y`, with `mkJ y`, which unfolds to `Just y`, and with `g y`, which a rule rewrites to `Just y`, the second with `g y`.

```haskell
module M where

{-# NOINLINE target #-}
target :: Int -> Int
target x = x

{-# INLINE inlR #-}
inlR :: Maybe Int -> Int
inlR m = case m of { Nothing -> 0; Just v -> v * 3 + 1 }
{-# RULES "inlR/Just" forall v. inlR (Just v) = target v #-}

{-# INLINE [1] inlR1 #-}
inlR1 :: Maybe Int -> Int
inlR1 m = case m of { Nothing -> 0; Just v -> v * 3 + 2 }
{-# RULES "inlR1/Just" forall v. inlR1 (Just v) = target v #-}

{-# NOINLINE g #-}
g :: Int -> Maybe Int
g _ = Nothing
{-# RULES "g/Just" forall x. g x = Just x #-}

asWritten :: Int -> Int
asWritten y = inlR (Just y)

afterRule, afterRule1 :: Int -> Int
afterRule y = inlR (g y)
afterRule1 y = inlR1 (g y)

{-# INLINE mkJ #-}
mkJ :: Int -> Maybe Int
mkJ x = Just x

asExpandable :: Int -> Int
asExpandable y = inlR (mkJ y)
```

The rule firings include `Rule fired: inlR/Just (M)` twice (for `asWritten` and `asExpandable`) and `Rule fired: inlR1/Just (M)` once; `-dinline-check` shows one decision about `inlR`, the call in `afterRule`, whitespace collapsed:

```
Considering inlining: inlR arg infos [NonTrivArg] interesting continuation BoringCtxt some_benefit True is exp: True is work-free: True guidance ALWAYS_IF(arity=1,unsat_ok=False,boring_ok=False) case depth = 0 inline depth = 1 ANSWER = YES
```

The Core:

```
asWritten = target
afterRule = \ y -> case y of { I# x -> I# (+# (*# x 3#) 1#) }
afterRule1 = target
asExpandable = target
```

`build.log` has the warning `Rule "inlR/Just" may never fire because` ... for `inlR` and none for `inlR1`.

**Reproduces small:** yes.

### A13. `inline f` substitutes `f`'s unfolding as it is when the rule fires, whatever its guidance, a loop breaker's too, if `f` has one and built-in rules are on; once worker/wrapper has split `f`, that is the wrapper alone

**Rule.** `inline` (from `GHC.Exts`) is `NOINLINE [0]` identity in `GHC.Internal.Magic`, with a built-in rule `Inline` that rewrites `inline (f a b ..)` to `f`'s unfolding template applied to the arguments, looking through casts and ticks. The rule takes `realIdUnfolding`, so it ignores the guidance (`UnfNever` included), the context, the activation and loop-breaker status; it unfolds once, so a recursive function is unrolled one step. It does nothing where `f` has no unfolding template, as for an imported function whose interface carries none. A built-in rule is not gated by `-fno-enable-rewrite-rules`, which only makes user rules inactive; `matchRule` checks `roBuiltinRules`, which `-dno-builtin-rules` turns off. The unfolding is the one `f` has when the rule fires. In the defining module's first, gentle run, before worker/wrapper, that is its right-hand side, so the first repro's `inlHuge`, split later, comes in whole. Once worker/wrapper has split `f`, and so in every importer, it is the wrapper's stable unfolding (A26), the body having moved to the worker, so `inline f` brings in only the wrapper: the arguments taken apart and a call of `$wf`. That call is then decided by the ordinary rules: at variables it stays a call; at a literal, a worker with a vanilla unfolding (no pragma on `f`) may be inlined by size and discounts (A04), and was in the second repro, while an INLINABLE `f`'s worker carries the source-form unfolding (U08), sized as written (U04), and stayed a call. Only where `f` is not split, under INLINE (U09) or `-fno-worker-wrapper`, does `inline f` bring in the body of an imported `f`. A class method has no unfolding of its own (A15), so at a known dictionary the class-op rule fires first and `inline` then substitutes the instance method's unfolding, the wrapper's where worker/wrapper splits the method, as it does one taking an equality dictionary, which it unboxes (`canUnboxTyCon`, [compiler/GHC/Core/Opt/WorkWrap/Utils.hs#L685][g106]; Wrinkle (DNB2) of Note [Do not unbox class dictionaries], [#L754][g107]). Source: [compiler/GHC/Core/Opt/ConstantFold.hs#L2196][g108] (the `Inline` rule), [#L2665][g109] (Note [inlineId magic]), [#L2703][g110] (`match_inline`); [compiler/GHC/Core/Rules.hs#L730][g111] (`matchRule`, the `BuiltinRule` case); [compiler/GHC/Driver/Config/Core/Rules.hs#L19][g112] (`roBuiltinRules`); [compiler/GHC/Core/Opt/Simplify/Utils.hs#L1521][g113] (`activeRule`); [libraries/ghc-internal/src/GHC/Internal/Magic.hs#L58][g114].

**Seen.** Orthotope's summing functions, as recorded on 2026-10-14: "For INLINABLE operations, and those with no pragma, `inline` brings in the worker/wrapper split's wrapper. The worker stays out of line in both functions but returns its fields unboxed." And of `convert`: "`convert` is a class method, so `inline` doesn't apply." The second repro bears out the first statement. The call of `convert` was not at an unknown dictionary: the class-op rule fired, and `inline` brought the instance method's unfolding, which is a wrapper, worker/wrapper splitting every instance's `convert` for its `a ~ b`; the worker carries the INLINABLE unfolding, which the client specialises, as orthotope's `$w$s$w$cconvertN` and the third repro's `$s$w$cconvert` show; the `Convert.hi` of O11's X4 (by `ghc --show-iface`) gives `$fConvertArrayArray10_$cconvert` the unfolding `StableSystem <3,TrueFalse>` and `$w$cconvert` a `StableUser` one.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A13-inline-function`, variants `base`, `norules` with `-fno-enable-rewrite-rules`, `nobuiltin` with `-dno-builtin-rules`, all with `-ddump-rule-firings`): `inline` applied to a body past the creation threshold, to a self-recursive function and to an imported function from a module compiled with `-fomit-interface-pragmas`.

```haskell
{-# OPTIONS_GHC -fomit-interface-pragmas #-}
-- The interface carries no unfolding for anything here.
module N (hugeN) where

hugeN :: Int -> Int -> Int
hugeN k y = case k of
  1 -> y * 8 + 1
  -- ... forty alternatives, n -> y * (n + 7) + n
  40 -> y * 47 + 40
  _ -> y
```

```haskell
module M where

import GHC.Exts (inline)
import N (hugeN)

inlHuge :: Int -> Int -> Int
inlHuge k y = case k of
  1 -> y * 8 + 1
  -- ... the same forty alternatives
  40 -> y * 47 + 40
  _ -> y - 1

inlSelf :: Int -> Int
inlSelf 0 = 0
inlSelf n = n + inlSelf (n - 1)

useHuge, useSelf, useImported :: Int -> Int
useHuge y = inline inlHuge 3 y
useSelf y = inline inlSelf y
useImported y = inline hugeN 3 y
```

`Rule fired: Inline (BUILTIN)` is in the rule firings of `base` and `norules`, not of `nobuiltin`. The Core of `base`, the same in `norules`:

```
useHuge = \ y -> case y of { I# x -> I# (+# (*# x 10#) 3#) }
useSelf
  = \ y ->
      case y of { I# ds ->
      case ds of wild1 {
        __DEFAULT ->
          case $winlSelf (-# wild1 1#) of ww { __DEFAULT ->
          I# (+# wild1 ww)
          };
        0# -> useSelf1
      }
      }
useImported = \ y -> hugeN useImported1 y
```

and of `nobuiltin`:

```
useHuge = \ y -> $winlHuge 3# y
useSelf = inlSelf
```

A second repro (`~/r/horde-ad/dist-inlcat/cases/A13-inline-brings-wrapper-only`, variants `none`, `inlinable` and `inline` by `f`'s pragma, set by `-DINB` and `-DINL`, `noww` with `-fno-worker-wrapper`, and `rw`, `none` with `-ddump-rule-rewrites`): a strict function past the inlining threshold, and a client applying `inline` to it at variables and at a literal, and to `show` at `Int`.

```haskell
{-# LANGUAGE CPP, BangPatterns #-}
module Lib (f) where

-- A strict, non-recursive function past the inlining threshold, which
-- worker/wrapper splits unless it is INLINE.
#if defined(INL)
{-# INLINE f #-}
#elif defined(INB)
{-# INLINABLE f #-}
#endif
f :: Int -> Int -> Int
f !n !k =
  let a = n * k + (n `quot` 3) * (k + 1) - (n `rem` 5) * (k - 2)
      b = (a * a) `rem` 11 + (a `quot` 7) * (n - k) + (k * k) `rem` 13
      c = (b * n) `rem` 17 - (a * k) `quot` 19 + (n + k + a + b) `rem` 23
  in if a > b then c * 2 + a - b else if b > c then b * 3 - c + n else c + k
```

```haskell
module M (g, h, k) where

import GHC.Exts (inline)
import Lib (f)

-- The client asks for f's unfolding at each call: with variables,
g :: Int -> Int -> Int
g x y = inline f x y

-- and with a literal.
h :: Int -> Int
h x = inline f x 3

-- And at a class method, whose selector carries no unfolding.
k :: Int -> String
k x = inline show x
```

`rw`, in `M.dump-rule-rewrites`: `Before: inline TYPE: Int -> Int -> Int f x y After: \ n k -> case n of { I# ww -> case k of { I# ww1 -> case $wf ww ww1 of ww2 { __DEFAULT -> I# ww2 } } }` (whitespace collapsed), `f`'s unfolding in `none`'s `Lib.iface` being the wrapper's, `Strictness: <1!P(L)><1!P(L)>, CPR: 1, Inline: [2], Unfolding: Core: StableSystem <2,TrueFalse>`. `none`: `g = \ x y -> case x of { I# ww -> case y of { I# ww1 -> case $wf ww ww1 of ww2 { __DEFAULT -> I# ww2 } } }`, and at the literal the worker inlined into a copy of `M`'s own, `h = \ x -> case x of { I# ww -> case $wh ww of ww1 { __DEFAULT -> I# ww1 } }`. `inlinable`: the same `g`, and `h = \ x -> case x of { I# ww -> case $wf ww 3# of ww2 { __DEFAULT -> I# ww2 } }`. `inline`: `g = \ x y -> case x of { I# ww -> case y of { I# ww1 -> case $wg ww ww1 of ww2 { __DEFAULT -> I# ww2 } } }`, the body in `M`'s own worker; `noww`: the body in `g` itself, `g = \ x y -> case x of { I# ipv -> case y of { I# ipv1 -> let { a = -# ...`. At `show`, `rw` records `Rule fired` for `Class op show` and then `Inline`: `Before: inline TYPE: Int -> String $fShowInt_$cshow x After: \ x -> case x of { I# n -> itos n [] }`.

A third repro (`~/r/horde-ad/dist-inlcat/cases/A13-inline-method-equality`, variants `eq` and `noeq`, the latter by `-DNOEQ`, both with `-ddump-rule-rewrites`): orthotope's `Convert` cut down, an instance with an equality constraint on the element or without one, its INLINABLE method past the inlining threshold, and a client applying `inline` to it at a known instance at two sites.

```haskell
{-# LANGUAGE BangPatterns, MultiParamTypeClasses, FlexibleInstances, GADTs, CPP #-}
module Lib (Convert (..), X (..), Y (..)) where

class Convert a b where
  convert :: a -> b
  convertE :: a -> Either String b
  {-# INLINE convertE #-}
  convertE x = Right $! convert x

newtype X a = X [a]
newtype Y a = Y [a]

#if defined(NOEQ)
instance Num a => Convert (X a) (Y a) where
#else
instance (a ~ b, Num a) => Convert (X a) (Y b) where
#endif
  {-# INLINABLE convert #-}
  convert (X xs) = Y (go 0 xs)
    where
      go !k (y : ys) = y * fromIntegral k + y * y - fromIntegral (k * 3) : go (k + 1) ys
      go _ [] = []
```

```haskell
module M (g, h) where

import GHC.Exts (inline)
import Lib

g :: X Double -> Y Double
g x = inline convert x

h :: X Double -> Int
h x = case (inline convert x :: Y Double) of Y ys -> length ys
```

In `eq`'s `M.dump-rule-rewrites` the class-op rule fires first, `Before: convert TYPE: X Double TYPE: Y Double $dConvert After: $fConvertXY_$cconvert $d~ $fNumDouble`, then `Inline` brings the method's unfolding, the wrapper's, `Unfolding: Core: StableSystem <3,TrueFalse>` in `Lib.iface`: `After: (\ @a @b $d~ $dNum eta -> case $d~ of { Eq# ww -> $w$cconvert @~<Co:1> $dNum eta })`, and the worker's call is rewritten to the client's specialisation, `Rule: SPEC/M $w$cconvert @Double @Double`. In `noeq` the method is not split (`Lib.iface` has no `$w$cconvert`), and `inline` brings its body, ``After: (\ ds -> go lvl (ds `cast` <Co:2>)) `cast` <Co:7>`` (whitespace collapsed).

**Reproduces small:** yes.

### A14. `noinline f` blocks inlining only because `f` is then applied to no value argument; an INLINE binding with no arguments is inlined through it

**Rule.** `noinline` (from `GHC.Exts`) is a wired-in identity that CorePrep removes. It has no special treatment in the inliner: the desugarer rewrites `noinline (f x y)` to `noinline f x y`, so `f` is a variable with no value arguments in a lazy argument of `noinline`, a `BoringCtxt`. A function whose guidance needs arguments (`UnfWhen` with arity above 0, or `UnfIfGoodArgs`, whose benefit needs an interesting argument or context) is then not inlined. But an INLINE binding with no arguments has `UnfWhen` with arity 0 and `boring_ok` (A06), which needs neither, so for such an `x`, `x` is inlined inside `noinline x`, and so would be a binding with no arguments whose right-hand side is trivial, which gets the same guidance without a pragma (`uncondInline`, A02; from the source, not reproduced). The demand analyser treats `noinline f x` as lazy in `x` (Note [noinlineId magic], (W2)). Source: [compiler/GHC/Builtin/WiredIn/Ids.hs#L520][g115] (Note [noinlineId magic]); [compiler/GHC/HsToCore/Expr.hs#L798][g116] (`ds_app_var`, the `noinlineId` case); [compiler/GHC/Core/Opt/Simplify/Inline.hs#L310][g5] and [#L318][g27] (`enough_args`); [compiler/GHC/Core/Unfold/Make.hs#L169][g11] (`boring_ok` for arity 0).

**Seen.** Not in our record.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A14-noinline-function`, variant `base` with `-ddump-ds` and `-dinline-check inl`): `noinline` applied to an INLINE function with one argument, and to an INLINE binding with none.

```haskell
module M where

import GHC.Exts (noinline)

{-# NOINLINE expensive #-}
expensive :: Int -> Int
expensive n = sum [1 .. n]

{-# INLINE inlFun #-}
inlFun :: Int -> Maybe Int
inlFun x = case x of { 0 -> Nothing; _ -> Just (x + 1) }

{-# INLINE inlCaf #-}
inlCaf :: Int
inlCaf = expensive 200

useFun :: Int -> Int
useFun x = case noinline inlFun x of { Nothing -> 0; Just v -> v }

useCaf :: Int -> Int
useCaf y = case noinline inlCaf of { 0 -> y; _ -> 1 }
```

The decisions, whitespace collapsed:

```
Considering inlining: inlFun arg infos [] interesting continuation BoringCtxt some_benefit False is exp: True is work-free: True guidance ALWAYS_IF(arity=1,unsat_ok=False,boring_ok=False) case depth = 0 inline depth = 1 ANSWER = NO
Considering inlining: inlCaf arg infos [] interesting continuation BoringCtxt some_benefit False is exp: False is work-free: False guidance ALWAYS_IF(arity=0,unsat_ok=False,boring_ok=True) case depth = 0 inline depth = 1 ANSWER = YES
```

The desugared call `case noinline inlFun x of {` and the Core:

```
      case noinline inlFun x of { Nothing -> useFun1; Just v -> v }
useCaf3 = case $wexpensive 200# of ww { __DEFAULT -> I# ww }
useCaf2 = noinline useCaf3
```

**Reproduces small:** yes.

### A15. A dictionary function is inlined only if its class is unary, its methods otherwise selected by a rule

**Rule.** A dictionary function of a class with more than one method or superclass carries a `DFunUnfolding`, which `callSiteInline` never inlines; a class method selector has no unfolding at all ("No unfolding for a dictionary selector; the RULE does the work", `mkDictSelId`, [compiler/GHC/Types/Id/Make.hs#L367][g117]), so `inline` on a method does nothing by itself (A13). `op (df d1 ..)` is instead rewritten by the selector's built-in rule `Class op op`, which matches when `exprIsConApp_maybe` of the dictionary argument finds the constructor, through the `DFunUnfolding` or through a variable bound to such a call (Note [ClassOp/DFun selection]). For a unary class (one method, or no method and one superclass) the dictionary function gets an ordinary unfolding instead, the constructor application sized as its field, and is inlined (Note [Unary class magic], (UCM4) and (UCM5)). A dictionary function is CONLIKE, so a dictionary argument bound to one is a `ValueArg` (A07). Source: [compiler/GHC/Core/Opt/Simplify/Inline.hs#L117][g118] (`DFunUnfolding {} -> Nothing`); [compiler/GHC/Tc/TyCl/Instance.hs#L190][g119] (Note [ClassOp/DFun selection]); [compiler/GHC/Types/Id/Make.hs#L403][g120] and [#L447][g121] (the selector's rule, `dictSelRule`); [compiler/GHC/Core/Unfold/Make.hs#L86][g122] (`mkDFunUnfolding`, the unary case); [compiler/GHC/Core/TyCon.hs#L1458][g123] (Note [Unary class magic]); [compiler/GHC/Core/Unfold.hs#L855][g124] (`conSize`); [compiler/GHC/Types/InlinePragma.hs#L236][g125] (`dfunInlinePragma`, CONLIKE).

**Seen.** Not in our record.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A15-dictionaries-and-class-ops`, variant `base` with `-fno-specialise`, so that the overloaded calls are decided by inlining alone, `-ddump-rule-firings`, `-ddump-ds` and `-dinline-check inl`): a two-method class and a one-method class with instances at `Bool`, an overloaded function using each, called at `Bool`, and a method called on the known dictionary.

```haskell
module M where

class C a where
  op1 :: a -> Int
  op2 :: a -> Int

instance C Bool where
  op1 b = if b then 1 else 0
  op2 b = if b then 2 else 3

class S a where
  sop :: a -> Int

instance S Bool where
  sop b = if b then 4 else 5

inlOver :: C a => a -> Int
inlOver x = op1 x * 3 + op2 x * 5 + 7

inlOverS :: S a => a -> Int
inlOverS x = sop x * 3 + sop x * 5 + 8

useOver, useOverS :: Bool -> Int
useOver b = inlOver b
useOverS b = inlOverS b

useOp :: Bool -> Int
useOp b = op1 b
```

For A04's dictionary discount, the decision for `inlOver`, the dictionary's discount 180 for two methods each applied to an argument, whitespace collapsed:

```
Considering inlining: inlOver arg infos [ValueArg, TrivArg] interesting continuation BoringCtxt some_benefit True is exp: True is work-free: True guidance IF_ARGS [180 0] 94 10 case depth = 0 inline depth = 1 depth based penalty = 0 adjusted size = -116 ANSWER = YES
```

`-ddump-inlinings` records `Inlining done: $fSBool` and no inlining of `$fCBool`; the rule firings include `Rule fired: Class op op1 (BUILTIN)` and `Rule fired: Class op sop (BUILTIN)`. The desugared `useOp = \ b -> op1 $fCBool b` ends as the method itself, CSE making `useOp` the dictionary's field:

```
$fCBool = C:C useOp $fCBool_$cop2
$fSBool = C:S $fSBool_$csop
```

**Reproduces small:** yes.

### A16. A binding that occurs once, outside a lambda, or applied inside one when its right-hand side is trivial or a lambda, is substituted before it is simplified, whatever its size, with exceptions, chief among them INLINE and an occurrence inside a stable unfolding

**Rule.** At a non-recursive binding, before simplifying its right-hand side, `preInlineUnconditionally` substitutes it at its single occurrence and drops it, with no size or benefit test, when the occurrence analyser found it dead, or occurring once outside any lambda (for a top-level binding, only before the final phase), or once inside a lambda in an applied position with a right-hand side that is a value lambda, a literal, or a variable itself occurring many times or inside a lambda (`canInlineInLam`). An occurrence inside a stable unfolding (INLINE, INLINABLE) or a rule's right-hand side counts as many (Note [Occurrences in stable unfoldings and RULES]), so a binding used once in the body of an INLINE function is not substituted there, lest the unfolding grow by it at every call. It does not fire with `-fno-pre-inlining`, for an inactive activation, a top-level bottoming binding, a coercion variable, an exit join point (A20), or a binding with an INLINE pragma (Note [Stable unfoldings and preInlineUnconditionally]). An INLINABLE binding is substituted by its stable unfolding rather than its right-hand side. So a function without a pragma, called once, ends up in its caller even where `callSiteInline` would not inline it, and the same function under INLINE stays a call when its single call is in a boring context (A01): under INLINE less is then inlined. Source: [compiler/GHC/Core/Opt/Simplify/Utils.hs#L1657][g126] (`preInlineUnconditionally`), [#L1698][g127] (`one_occ`), [#L1733][g128] (`canInlineInLam`), [#L1745][g129] (`early_phase`), [#L1610][g130] (Note [Stable unfoldings and preInlineUnconditionally]), [#L1598][g131] (Note [pre/postInlineUnconditionally in gentle mode]); [compiler/GHC/Driver/Config/Core/Opt/Simplify.hs#L69][g132] (`sm_pre_inline`, `-fpre-inlining`); [compiler/GHC/Core/Opt/OccurAnal.hs#L2388][g133] (`occAnalUnfolding`, `markAllMany`); [compiler/GHC/Core/Opt/Simplify/Utils.hs#L1449][g134] (Note [Simplifying inside stable unfoldings]).

**Seen.** The comment on GHC [!12121](https://gitlab.haskell.org/ghc/ghc/-/merge_requests/12121), the FloatIn work for GHC [#24466](https://gitlab.haskell.org/ghc/ghc/-/work_items/24466) (`docs/ghc-issue-floatin-duplicate-values-comment.md` in horde-ad), its family M: once the late CSE leaves `g` a single use, the simplifier after float-in inlines `g` there, as HEAD does.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A16-pre-inline-unconditionally`, variants `base` and `nopre` with `-fno-pre-inlining`, both `-ddump-simpl-stats` and `-dinline-check inl`): the same body without a pragma and with INLINE, neither exported, each called once as a lazy constructor argument with a variable argument; and a third such body, `inlH`, called once inside an exported INLINE function.

```haskell
module M (useP, useI, wrapH) where

inlP :: Int -> Int
inlP k = case k of
  0 -> k + 1
  1 -> k * 2
  2 -> k - 3
  3 -> k * k
  _ -> k

{-# INLINE inlI #-}
inlI :: Int -> Int
inlI k = case k of
  0 -> k + 1
  1 -> k * 2
  2 -> k - 3
  3 -> k * k
  _ -> k - 1

useP, useI :: Int -> Maybe Int
useP y = Just (inlP y)
useI y = Just (inlI y)

inlH :: Int -> Int
inlH k = case k of
  0 -> k + 2
  1 -> k * 3
  2 -> k - 4
  3 -> k * k
  _ -> k - 2

{-# INLINE wrapH #-}
wrapH :: Int -> Maybe Int
wrapH y = Just (inlH y)
```

In `base`, `-dinline-check` prints no decision about `inlP`, which the simplifier statistics list under `PreInlineUnconditionally` (`1 inlP`), and prints a refusal of `inlI`, whitespace collapsed:

```
Considering inlining: inlI arg infos [TrivArg] interesting continuation BoringCtxt some_benefit False is exp: True is work-free: True guidance ALWAYS_IF(arity=1,unsat_ok=False,boring_ok=False) case depth = 0 inline depth = 1 ANSWER = NO
```

The Core of `base`:

```
useI = \ y -> Just (inlI y)
useP = \ y -> Just (case y of wild { I# ds -> ...
```

`inlH` is not pre-inlined but decided at its call, and refused:

```
Considering inlining: inlH arg infos [TrivArg] interesting continuation BoringCtxt some_benefit False is exp: True is work-free: True guidance IF_ARGS [20] 115 50 case depth = 0 inline depth = 1 depth based penalty = 0 adjusted size = 95 ANSWER = NO
wrapH = \ y -> Just (inlH y)
```

In `nopre`, `inlP` too is considered at its call, `Considering inlining: inlP arg infos [TrivArg] interesting continuation BoringCtxt some_benefit False` ... `ANSWER = NO`, and stays:

```
useP = \ y -> Just (inlP y)
```

**Reproduces small:** yes, except an INLINABLE binding substituted by its stable unfolding, which rests on the source.

### A17. After simplifying a local let, a small right-hand side used at most once in each branch is copied into the branches using it, but into a lambda only when work-free and in an interesting position, and never at top level

**Rule.** After simplifying the right-hand side of a non-top-level let, `postInlineUnconditionally` substitutes it at all occurrences and drops the binding, with no benefit test: never for an inactive activation, any loop breaker, one with a stable unfolding (INLINE, INLINABLE: Note [Stable unfoldings and postInlineUnconditionally]) or a top-level binding; then always when it is trivial; and never for any other join point ((DJ1) of Note [Duplicating join points]: `exprIsTrivial rhs = True` before `BC_Join {} <- bind_cxt = False`, [compiler/GHC/Core/Opt/Simplify/Utils.hs#L1831][g135] and [#L1832][g136]). Otherwise only a binding occurring at most once in each case branch (`OneOcc`) is considered: in at least 100 branches, no; once and outside any lambda, yes; demanded by the demand analyser, no; else outside lambdas when it occurs in one branch or is no bigger than the use threshold (`smallEnoughToInline`), and inside a lambda only when also in an interesting position with a work-free unfolding. So a thunk `let x = f y` used lazily in two branches is copied into both, each evaluating `f y` at most once, where the call-site inliner would never take a thunk (A06). The demand test applies only after the demand analyser has run; a let written in the source is decided earlier and copied even when used in every branch. Source: [compiler/GHC/Core/Opt/Simplify/Utils.hs#L1815][g137] (`postInlineUnconditionally`), [#L1866][g138] (`work_ok`), [#L1890][g139] (Note [Inline small things to avoid creating a thunk]), [#L1954][g140] (Note [Top level and postInlineUnconditionally]), [#L1984][g141] (Note [Stable unfoldings and postInlineUnconditionally]); [compiler/GHC/Core/Opt/Simplify/Inline.hs#L62][g142] (`smallEnoughToInline`).

**Seen.** The GHC !12121 comment (`docs/ghc-issue-floatin-duplicate-values-comment.md`), its rows for GHC [#2988](https://gitlab.haskell.org/ghc/ghc/-/work_items/2988): `x`, used in two of three alternatives, is inlined into both, a local function or a thunk, the thunk by `postInlineUnconditionally`.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A17-post-inline-unconditionally`, variant `base` with `-ddump-simpl-stats`): a thunk used lazily in two branches, one used in both branches of a two-way case, one used inside a lambda, and a top-level one used in two branches.

```haskell
module M where

{-# NOINLINE f #-}
f :: Int -> Int
f y = y * 1000

lazyTwo :: Int -> Int -> Maybe Int
lazyTwo b y = let x = f y in case b of { 0 -> Just x; 1 -> Just (x + 1); _ -> Nothing }

inLam :: Int -> Int -> Int
inLam y = let x = f y in \z -> x + z

top :: Int
top = f 7

topTwo :: Int -> Maybe Int
topTwo b = case b of { 0 -> Just top; 1 -> Just (top + 1); _ -> Nothing }

strictTwo :: Int -> Int -> Int
strictTwo b y = let x = f y in case b of { 0 -> x; _ -> x + 1 }
```

The Core, whitespace collapsed: `f y` in both branches of `lazyTwo`'s worker and of `strictTwo`, `x` kept in `inLam`, `top` kept:

```
$wlazyTwo = \ ww y -> case ww of { __DEFAULT -> Nothing; 0# -> Just (f y); 1# -> Just (case y of { I# ww1 -> case $wf ww1 of ww2 { __DEFAULT -> I# (+# ww2 1#) } }) }
inLam = \ y -> let { x = case y of { I# ww -> case $wf ww of ww1 { __DEFAULT -> I# ww1 } } } in \ z -> $fNumInt_$c+ x z
topTwo3 = Just top
topTwo2 = case top of { I# x -> I# (+# x 1#) }
strictTwo = \ b y -> case b of { I# ds -> case ds of { __DEFAULT -> case y of { I# ww -> case $wf ww of ww1 { __DEFAULT -> I# (+# ww1 1#) } }; 0# -> f y } }
```

The statistics: `PostInlineUnconditionally 1 y 1 x 1 x`, whitespace collapsed.

**Reproduces small:** yes, except the limit of 100 branches, which rests on the source.

### A18. Apart from A19's cases, a join point is inlined at a jump only where an argument the body scrutinises or applies is a value, or a free variable is more evaluated there; interesting arguments are not enough

**Rule.** For a join point with `UnfIfGoodArgs` guidance, `tryUnfolding` skips `some_benefit` and work-freeness: it inlines at a jump only when the adjusted size is within the threshold (A04, depth penalty included) and either some argument with a nonzero discount (one the body scrutinises or applies) is a `ValueArg`, or some free variable of the body has a better unfolding at the jump than at the join point's definition (`is_more_evald`; for example it is scrutinised between the two). A `NonTrivArg`, which earns other functions a benefit, does not count. The `-dinline-check` output lists each free variable as `(v, has an unfolding, evaluated at the jump, more evaluated at the jump)`. A join point whose body has one of A19's forms gets `UnfWhen` guidance instead (A19). A join point given no unfolding, as at its birth, is not inlined at all (U14). Source: [compiler/GHC/Core/Opt/Simplify/Inline.hs#L321][g143] (`isJoinId id, small_enough -> inline_join_point`), [#L349][g144] (`inline_join_point`), [#L424][g145] (`is_more_evald`), [#L455][g146] (Note [Inlining join points]).

**Seen.** The walk after a bang on orthotope's INLINE `vToList` (U15, its third repro): a join point over the vector's fields and the case binder, inlined at each jump that passes the binder as a constructor, `[TrivArg, TrivArg, TrivArg, ValueArg]` against `IF_ARGS [0 0 0 20]`, so the walk is copied into every branch. And a candidate, vector-stream's `cmp_loop1`, kept as a separate join point and given a thunk (`docs/vector-issue-storable-lazy-index.md`), not checked against that loop.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A18-join-point-inlining`, variant `base`, `-dinline-check inl`): two local functions that become join points, each jumped to twice: `inlJ` with a constructor and with a call; `inlK`, which scrutinises the free `m`, once where `m` has been scrutinised and once elsewhere.

```haskell
module M where

{-# NOINLINE g #-}
g :: Int -> Maybe Int
g n = Just n

valueArg :: Int -> Bool -> Int
valueArg n b =
  let inlJ x = case x of { Just v -> v * n + 1; Nothing -> n * 2 }
  in case b of { True -> inlJ (Just 3); False -> inlJ (g n) }

evaldFree :: Maybe Int -> Int -> Int -> Int
evaldFree m n k =
  let inlK y = case m of { Just v -> v * y + n; Nothing -> y * 2 }
  in case k of
       0 -> case m of { Nothing -> 0; _ -> inlK n }
       _ -> inlK (n + 1)
```

The decisions, whitespace collapsed:

```
Considering inlining: inlJ arg infos [NonTrivArg] interesting continuation BoringCtxt some_benefit True is exp: True is work-free: True guidance IF_ARGS [51] 92 20 case depth = 1 inline depth = 1 join (n, False, Just False, False) depth based penalty = 0 adjusted size = 62 ANSWER = NO
Considering inlining: inlJ arg infos [ValueArg] interesting continuation BoringCtxt some_benefit True is exp: True is work-free: True guidance IF_ARGS [51] 92 20 case depth = 1 inline depth = 1 join (n, False, Just False, False) depth based penalty = 0 adjusted size = 21 ANSWER = YES
Considering inlining: inlK arg infos [NonTrivArg] interesting continuation BoringCtxt some_benefit True is exp: True is work-free: True guidance IF_ARGS [20] 102 20 case depth = 1 inline depth = 1 join (n, False, Just False, False) (m, False, Just False, False) depth based penalty = 0 adjusted size = 72 ANSWER = NO
Considering inlining: inlK arg infos [TrivArg] interesting continuation BoringCtxt some_benefit False is exp: True is work-free: True guidance IF_ARGS [20] 102 20 case depth = 2 inline depth = 1 join (n, False, Just False, False) (m, False, Just True, True) depth based penalty = 0 adjusted size = 82 ANSWER = YES
```

**Reproduces small:** yes.

### A19. A join point is inlined unconditionally only if its body is trivial, a jump, or an application without free variables

**Rule.** For a join point, `calcUnfoldingGuidance` gives `UnfWhen` with `unsat_ok` and `boring_ok` --- inlined at every jump --- only when `uncondInlineJoin` holds (Note [Duplicating join points], (DJ3)): (a) the body is trivial; (b) it is a jump to another join point with trivial arguments, free variables allowed; (c) it is a data constructor or one of its own binders applied to trivial arguments, none of them a free variable or a literal. Otherwise the guidance is `UnfIfGoodArgs` and A18's rule decides, however small the body: `$j x = K f x`, with `f` free, stays a join point so that the code after it binds its pattern variable to `f` instead of abstracting over it ((DJ3)'s motivating example, GHC [#19996](https://gitlab.haskell.org/ghc/ghc/-/work_items/19996)). `mkDupableAlt` and `mkDupableStrictBind` make no join point at all for a body that (DJ3) would inline ((DJ2)); post-inlining a join point is A17's. Source: [compiler/GHC/Core/Unfold.hs#L502][g24] (`uncondInline`, `is_join`), [#L507][g147] (`uncondInlineJoin`); [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4474][g148] (Note [Duplicating join points], (DJ1) to (DJ5)).

**Seen.** GHC [#27862](https://gitlab.haskell.org/ghc/ghc/-/work_items/27862), item 3 (`docs/ghc-issue-redundant-bang-splits-match.md`, its reproducer reused there): `allBangs` keeps a join point `fail _ = (# axes, ww #)`, whose body has free variables and so is not (DJ3)'s case (c), on HEAD.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A19-join-point-unconditional`, variant `base`, `-dinline-check inl` and `-ddump-occur-anal`): local functions that become join points, each jumped to from two branches: a pair built from its own binders, a pair with a free variable, and a jump to another join point. `inlC` has a monomorphic local signature: without it the binding is generalised and `postInlineUnconditionally` takes it as an ordinary let before it becomes a join point.

```haskell
module M where

closedCon :: Int -> Bool -> (Int, Int)
closedCon n b =
  let inlC :: Int -> Int -> (Int, Int)
      inlC x y = (y, x)
  in case b of { True -> inlC n 1; False -> inlC 2 n }

freeCon :: Int -> Int -> Bool -> (Int, Int)
freeCon n m b =
  let inlF x = (m, x)
  in case b of { True -> inlF n; False -> inlF 3 }

indirect :: Int -> Int -> Int -> Int
indirect n m k =
  let inlB x y = x * y + m * n + k * x * y
      inlA x = inlB x m
  in case k of { 0 -> inlA n; 1 -> inlA m; _ -> inlB k k }
```

`inlC` is a join point (`join { inlC x y = (y, x) } in` in the occurrence analyser's output). The decisions, whitespace collapsed:

```
Considering inlining: inlC arg infos [ValueArg, TrivArg] interesting continuation BoringCtxt some_benefit True is exp: True is work-free: True guidance ALWAYS_IF(arity=2,unsat_ok=True,boring_ok=True) case depth = 1 inline depth = 1 ANSWER = YES
Considering inlining: inlA arg infos [TrivArg] interesting continuation BoringCtxt some_benefit False is exp: True is work-free: True guidance ALWAYS_IF(arity=1,unsat_ok=True,boring_ok=True) case depth = 1 inline depth = 1 ANSWER = YES
Considering inlining: inlF arg infos [ValueArg] interesting continuation BoringCtxt some_benefit True is exp: True is work-free: True guidance IF_ARGS [0] 10 10 case depth = 1 inline depth = 1 join (m, False, Just False, False) depth based penalty = 0 adjusted size = -10 ANSWER = NO
```

The Core, whitespace collapsed:

```
closedCon = \ n b -> case b of { False -> (n, closedCon2); True -> (closedCon1, n) }
freeCon = \ n m b -> join { inlF x = (m, x) } in case b of { False -> jump inlF freeCon1; True -> jump inlF n }
```

**Reproduces small:** yes.

### A20. An exit join point without a stable unfolding is never inlined back into its loop

**Rule.** The exitification pass, after the demand analyser, moves each exit path of a recursive join point (a branch with no recursive call) into a non-recursive join point `exit` bound outside the loop, abstracted over the variables it uses. The simplifier recognises such a join point by its occurrence info (`isExitJoinId`: a join point occurring once, inside the loop's lambda) and keeps it out of the loop: `preInlineUnconditionally` does not substitute it, and, unless it has a stable unfolding, `simplLetUnfolding` gives it none (U14), so neither `postInlineUnconditionally` nor a call site can take it. Without the rule its single jump would be pre-inlined at once. `-fno-exitification` keeps the exit code in the loop. Source: [compiler/GHC/Core/Opt/Exitify.hs][g149] (Note [Exitification], Note [Do not inline exit join points]); [compiler/GHC/Core/Opt/Simplify/Utils.hs#L1670][g150] (`preInlineUnconditionally`), [#L3063][g151] (`isExitJoinId`); [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4855][g152] (`simplLetUnfolding`); [compiler/GHC/Core/Opt/Pipeline.hs#L263][g153] (the pass, after `demand_analyser`).

**Seen.** GHC [#27893](https://gitlab.haskell.org/ghc/ghc/-/work_items/27893) (`docs/ghc-issue-exit-join-point-boxed-loop.md`, its reproducer there): an exit join point in an imported unfolding takes the loop's variables boxed, and `isExitJoinId` keeps it out of the client's copy of the loop.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A20-exit-join-points`, variants `base` and `noexit` with `-fno-exitification`): a counting loop whose exit computes a polynomial.

```haskell
module M where

loop :: Int -> Int -> Int -> Int
loop t n0 x0 = go n0 x0
  where
    go :: Int -> Int -> Int
    go 0 x = t * (x * x) + t * x + x
    go n x = go (n - 1) (x + t)
```

The Core of `base`, whitespace collapsed; the exit join point and its one jump survive to the end:

```
join { exit ww2 = case t of { I# x -> I# (+# (+# (*# x (*# ww2 ww2)) (*# x ww2)) ww2) } } in joinrec {
              0# -> jump exit ww3
```

and of `noexit`, which has no `exit`:

```
              0# -> case t of { I# x -> I# (+# (+# (*# x (*# ww3 ww3)) (*# x ww3)) ww3) }
```

**Reproduces small:** yes.

### A21. A variable scrutinised alone, with an expandable unfolding, is not inlined: the case is resolved through the unfolding instead

**Rule.** A variable with no arguments is a lone variable. In `CaseCtxt`, `interesting_call` is false for a lone variable whose unfolding is expandable (a constructor application, a lambda, a CONLIKE call), so it has no benefit and is not inlined however small (Note [Lone variables]); instead `rebuildCase` applies case-of-known-constructor through `exprIsConApp_maybe`, which extracts the constructor and its fields from the unfolding, and the binding stays shared for its other uses. A lone variable whose unfolding is not expandable does get the benefit in `CaseCtxt`, and then needs work-freeness (A06). In `DiscArgCtxt` and `RuleArgCtxt` a binding with no arguments has no benefit either. A lone variable that occurs only as the scrutinee is usually taken by pre-inlining (A16), since the occurrence analyser's binder swap replaces the variable by the case binder in the alternatives. Source: [compiler/GHC/Core/Opt/Simplify/Inline.hs#L412][g154] (`CaseCtxt -> not (lone_variable && is_exp)`), [#L618][g155] (Note [Lone variables]), [#L684][g156] (Note [Interaction of exprIsWorkFree and lone variables]); [compiler/GHC/Core/Opt/Simplify/Utils.hs#L597][g157] (`contArgs`, `lone`); [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L3268][g158] (`rebuildCase`, `exprIsConApp_maybe`), [#L3939][g159] (`knownCon`); [compiler/GHC/Core/SimpleOpt.hs#L1553][g160] (`exprIsConApp_maybe`).

**Seen.** Not in our record.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A21-lone-variable-known-constructor`, variants `base`, `-dinline-check inl`, and `iter`, `-ddump-simpl-iterations`): a local pair, scrutinised alone and also passed to a NOINLINE function; its right-hand side becomes a constructor application only in phase 2, when case-of-case is on, so that the scrutinee is decided in `CaseCtxt` (in the gentle run a scrutinee is a `BoringCtxt`, A08).

```haskell
module M (keep, mkPair, useLocal) where

{-# NOINLINE keep #-}
keep :: (Int, Int) -> Int
keep (a, b) = a - b

{-# INLINE [2] mkPair #-}
mkPair :: Int -> Int -> (Int, Int)
mkPair x y = (x * 2, y)

useLocal :: Int -> Int -> Int
useLocal x y =
  let inlP = mkPair x y
  in (case inlP of (a, _) -> a) + keep inlP
```

The decisions in `CaseCtxt`, whitespace collapsed: first with the pair, then with the pair's first field, which GHC binds apart under the name `inlP` too (`iter`'s `M.dump-simpl-iterations`: `let { inlP = case x of { I# x -> I# (*# x 2#) } } in let { inlP = (inlP, y) } in`); the field's binding, not expandable, gets the benefit but is not work-free:

```
Considering inlining: inlP arg infos [] interesting continuation CaseCtxt some_benefit False is exp: True is work-free: True guidance IF_ARGS [] 10 10 case depth = 0 inline depth = 1 depth based penalty = 0 adjusted size = -10 ANSWER = NO
Considering inlining: inlP arg infos [] interesting continuation CaseCtxt some_benefit True is exp: False is work-free: False guidance IF_ARGS [] 21 10 case depth = 0 inline depth = 1 depth based penalty = 0 adjusted size = 1 ANSWER = NO
```

The Core, whitespace collapsed: the case took the first field, `x2`, from the unfolding:

```
useLocal = \ x y -> case x of { I# x1 -> case y of { I# ww -> let { x2 = *# x1 2# } in case $wkeep x2 ww of ww1 { __DEFAULT -> I# (+# x2 ww1) } } }
```

**Reproduces small:** yes.

### A22. CONLIKE lets a rule match through a variable bound to a call, without inlining the variable

**Rule.** The rule matcher expands a variable in the term being matched when the variable's unfolding is expandable (`expandUnfolding_maybe`): a value, a constructor application, or an application of a CONLIKE function (`{-# NOINLINE CONLIKE f #-}`, `{-# INLINE CONLIKE f #-}`). So with `let x = f v in ... r x ...`, a rule on `r (f v)` fires through `x` only if `f` is CONLIKE; otherwise `x` is neither expanded by the matcher nor inlined, the call being work that inlining would duplicate, and the rule does not fire. The same expandability makes a CONLIKE call's binding a lone variable that is not inlined under a `case` (A21), and such a call or a variable bound to one is a `ValueArg` argument (`exprIsConLike`, A07); a dictionary function is CONLIKE (A15). Source: [compiler/GHC/Core/Rules.hs#L1137][g161] (`expandUnfolding_maybe`), [#L1715][g162] (Note [Expanding variables]); [compiler/GHC/Core/Utils.hs#L1947][g163] (`exprIsExpandable`) and Note [exprIsExpandable]; [compiler/Language/Haskell/Syntax/Binds/InlinePragma.hs#L138][g164] (Note [CONLIKE pragma]).

**Seen.** Not in our record.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A22-conlike`, variant `base` with `-ddump-rule-firings`): two NOINLINE functions, one CONLIKE, each with a rule on `r` applied to it, each called through a let-bound variable that is also returned, so that it is not inlined.

```haskell
module M where

{-# NOINLINE CONLIKE fC #-}
fC :: Int -> Maybe Int
fC v = Just v

{-# NOINLINE fP #-}
fP :: Int -> Maybe Int
fP v = Just v

{-# NOINLINE r #-}
r :: Maybe Int -> Int
r _ = 0

{-# RULES
"r/fC" forall v. r (fC v) = v + 100
"r/fP" forall v. r (fP v) = v + 200
  #-}

useC, useP :: Int -> (Int, Maybe Int)
useC v = let x = fC v in (r x, x)
useP v = let x = fP v in (r x, x)
```

The rule firings include `Rule fired: r/fC (M)` and no `r/fP`. The Core, whitespace collapsed:

```
useC = \ v -> (case v of { I# x -> I# (+# x 100#) }, fC v)
useP = \ v -> let { x = case $wfP v of { (# ww #) -> Just ww } } in (r x, x)
```

**Reproduces small:** yes.

### A23. A top-level function known to diverge is not inlined, unless it is no bigger than its call

**Rule.** When `calcUnfoldingGuidance` is called for a top-level bottoming binding (its demand signature ends in divergence, so from the first demand analysis on), it gives `UnfNever` unless `uncondInline` holds (A02): a call of such a function is not inlined, however small its adjusted size, so that FloatOut's floating of `error` calls to top level is not undone. A binding with no arguments whose right-hand side is trivial, or a function no bigger than its call, keeps `UnfWhen` and is inlined. Before the demand analyser the function is ordinary. Source: [compiler/GHC/Core/Unfold.hs#L358][g165] (`is_top_bottoming -> UnfNever`), [#L438][g166] (Note [Do not inline top-level bottoming functions]); [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4887][g167] (`mkLetUnfolding`, `is_bottoming = isDeadEndId id`); [compiler/GHC/Core/Opt/Simplify/Utils.hs#L1668][g168] (pre-inlining substitutes no top-level bottoming binding, Note [Top-level bottoming Ids]).

**Seen.** Not in our record.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A23-bottoming-functions`, variant `base`, `-fno-worker-wrapper` so that the functions keep their own guidance, A26; `-dinline-check inl`): a bottoming function bigger than its call, the same body returning the string instead, and a bottoming function no bigger than its call (GHC eta-reduces it to `errorWithoutStackTrace`), each called with a literal.

```haskell
module M (inlFail, inlFailTiny, inlOk, useFail, useFailTiny, useOk) where

inlFail :: Int -> Int
inlFail n = errorWithoutStackTrace ("bad index: " ++ show n ++ " out of range")

inlOk :: Int -> String
inlOk n = "bad index: " ++ show n ++ " out of range"

inlFailTiny :: String -> Int
inlFailTiny s = errorWithoutStackTrace s

useFail, useFailTiny :: Int -> Int
useFail x = case x of { 0 -> inlFail 7; _ -> x }
useFailTiny x = case x of { 0 -> inlFailTiny "x"; _ -> x }

useOk :: Int -> Int
useOk x = length (inlOk 7) + x
```

The decisions, whitespace collapsed: `inlFail` before demand analysis, too big, then `UnfNever` though its size, 290, is far below the creation threshold of 750; `inlOk` once its size has shrunk; `inlFailTiny`:

```
Considering inlining: inlFail arg infos [ValueArg] interesting continuation BoringCtxt some_benefit True is exp: True is work-free: True guidance IF_ARGS [20] 290 0 case depth = 1 inline depth = 1 depth based penalty = 0 adjusted size = 250 ANSWER = NO
Considering inlining: inlFail UnfNever
Considering inlining: inlOk arg infos [ValueArg] interesting continuation RuleArgCtxt some_benefit True is exp: True is work-free: True guidance IF_ARGS [20] 130 0 case depth = 0 inline depth = 1 depth based penalty = 0 adjusted size = 90 ANSWER = YES
Considering inlining: inlFailTiny arg infos [ValueArg] interesting continuation BoringCtxt some_benefit True is exp: True is work-free: True guidance ALWAYS_IF(arity=0,unsat_ok=True,boring_ok=True) case depth = 1 inline depth = 1 ANSWER = YES
```

The Core: the calls, floated to top level:

```
useFail1 = inlFail lvl2
useFailTiny1 = errorWithoutStackTrace lvl1
```

**Reproduces small:** yes.

### A24. NOINLINE keeps a function's body out of its callers but not its worker/wrapper wrapper, which is inlined in the final phase; OPAQUE keeps the call itself, unsplit

**Rule.** NOINLINE and OPAQUE without a phase both make the activation `NeverActive` (`mkInlinePragma`, [compiler/GHC/Parser/PostProcess.hs#L3094][g87]; `mkOpaquePragma`, [#L3113][g169]), so `callSiteInline` never takes the binding's unfolding (`Inactive unfolding:`, [compiler/GHC/Core/Opt/Simplify/Inline.hs#L113][g80]). Worker/wrapper still splits a NOINLINE function, as it would one without a pragma, so that callers can pass unboxed arguments and take an unboxed result (Note [Worker/wrapper for NOINLINE functions], [compiler/GHC/Core/Opt/WorkWrap.hs#L261][g170]): the worker inherits the original activation, never active, and keeps the NOINLINE `InlineSpec` (`work_act`, [#L835][g171]); the wrapper, which takes over the original name, gets the usual wrapper unfolding (A26), exposed like any stable one (U05), with activation `[final]`, A26's rule for a never-active function, whose activation begins in the final phase (`beginPhase NeverActive = FinalPhase`, [compiler/GHC/Types/InlinePragma.hs#L392][g172]). So from the final phase on a call of a NOINLINE `f` becomes a call of `$wf` with unboxed arguments, in its module and in an importer. OPAQUE turns worker/wrapper off for the binding: `tryWW` returns it whole ([compiler/GHC/Core/Opt/WorkWrap.hs#L585][g173]), the demand analyser strips the boxity from its demands and the CPR analyser its CPR, and it gets no unfolding, so every call stays a call of `f` passing and receiving boxed values (Note [OPAQUE pragma], [compiler/Language/Haskell/Syntax/Binds/InlinePragma.hs#L174][g174]). Specialisation and SpecConstr skip both.

**Seen.** `docs/perf-checklist.md` I2: NOINLINE "moves to the worker and leaves the wrapper inlinable only from the final phase".

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A24-noinline-opaque`, variant `base`, `-dinline-check inl`): the same strict function under NOINLINE and under OPAQUE, each called with one literal argument.

```haskell
module M where

{-# NOINLINE inlN #-}
inlN :: Int -> Int -> Int
inlN x y = x * y + 1

{-# OPAQUE inlO #-}
inlO :: Int -> Int -> Int
inlO x y = x * y + 2

useN, useO :: Int -> Int
useN x = inlN x 3 + 1
useO x = inlO x 3 + 1
```

`build.log` has `Inactive unfolding: inlN` and `Inactive unfolding: inlO`, and one decision about `inlN`, its wrapper in the final phase:

```
Considering inlining: inlN
  arg infos [TrivArg, ValueArg]
  interesting continuation CaseCtxt
  some_benefit True
  is exp: True
  is work-free: True
  guidance ALWAYS_IF(arity=2,unsat_ok=True,boring_ok=False)
  case depth = 0
  inline depth = 1
  ANSWER = YES
```

The interface: `inlN` is a wrapper active in the final phase, `inlO` keeps no boxity:

```
   Strictness: <1!P(L)><1!P(L)>, CPR: 1, Inline: [final],
   Unfolding: Core: StableSystem <2,TrueFalse>
   LambdaFormInfo: LFReEntrant 2, Arity: 2, Strictness: <1L><1L>,
   Inline:]
```

The Core, whitespace collapsed:

```
useN = \ x -> case x of { I# ww -> case $winlN ww 3# of ww1 { __DEFAULT -> I# (+# ww1 1#) } }
useO = \ x -> case inlO x useN1 of { I# x1 -> I# (+# x1 1#) }
```

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A24-noinline-opaque-ww`, variants `base` with `-dinline-check noi`, and `idinfo`, `-O -ddump-simpl -dsuppress-uniques -dsuppress-module-prefixes`, for the pragmas): a NOINLINE and an OPAQUE function of the same shape, and an importer calling both.

```haskell
module A (noi, opq) where

noi :: Int -> Int -> Int
{-# NOINLINE noi #-}
noi x y = x * y + 1

opq :: Int -> Int -> Int
{-# OPAQUE opq #-}
opq x y = x * y + 2
```

```haskell
module B (useBoth) where

import A

useBoth :: Int -> Int
useBoth n = noi n 3 + opq n 4
```

`noi` is split: `noi [InlPrag=NOINLINE[final]] :: Int -> Int -> Int` with interface unfolding `Strictness: <1!P(L)><1!P(L)>, CPR: 1, Inline: [final], Unfolding: Core: StableSystem <2,TrueFalse>`, and `$wnoi [InlPrag=NOINLINE] :: Int# -> Int# -> Int#`, which carries no unfolding. `opq [InlPrag=OPAQUE] :: Int -> Int -> Int` has no worker, and its interface entry ends `Strictness: <1L><1L>, Inline:]`: boxed demands, no CPR, no unfolding. Compiling B, `-dinline-check noi` prints `Inactive unfolding: noi` until the final phase, and B ends calling the worker unboxed and `opq` boxed:

```
useBoth
  = \ n ->
      case n of wild { I# ww ->
      case $wnoi ww 3# of ww2 { __DEFAULT ->
      case opq wild useBoth1 of { I# y -> I# (+# ww2 y) }
      }
      }
```

**Reproduces small:** yes.

### A25. A data constructor's wrapper is inlined only in the final phase, and one that unpacks a field not in a boring context

**Rule.** A data constructor gets a wrapper `$WK` when it unpacks a field or is a GADT, or belongs to a data family instance or has a datatype context, the wrapper evaluating and unboxing an unpacked field before applying the worker `K`; a strict field that is not unpacked is evaluated not by a wrapper but by the worker `K`, which is strict in it, the evaluation being inserted in STG ([compiler/GHC/Types/Id/Make.hs#L870][g175], `wrapper_reqd`; [compiler/GHC/Types/Id/Make.hs#L1156][g176], `-- Seqs are inserted in STG`). The wrapper carries INLINE CONLIKE with activation `[final]` (except for newtypes), so it is inactive in every earlier phase (Note [Activation for data constructor wrappers]); before then, case-of-known-constructor and rule matching treat it as CONLIKE and expand it (Note [DataCon wrappers are conlike], Note [exprIsConApp_maybe on data constructors with wrappers]). Its unfolding has `UnfWhen` guidance with `unsat_ok` and with `boring_ok` from `inlineBoringOk`, which is false for a wrapper that unpacks a field, since its body is a `case`; so in the final phase a strict constructor applied to variables in a boring context, such as a lazy constructor argument, stays a call of `$WK` --- at run time a thunk for the call --- while a wrapper whose body is just the worker applied to trivial arguments (a cast, a coercion) is inlined anywhere ((IB2) of Note [inlineBoringOk]). Source: [compiler/GHC/Types/Id/Make.hs#L785][g177] (`wrap_prag`), [#L939][g178] (`dataConWrapperInlinePragma`, INLINE CONLIKE), [#L943][g179] (Note [Activation for data constructor wrappers]), [#L964][g180] (Note [DataCon wrappers are conlike]), [#L804][g181] (`mkDataConUnfolding`); [compiler/GHC/Core/Unfold/Make.hs#L103][g182] (`mkDataConUnfolding`, `boring_ok = inlineBoringOk expr`); [compiler/GHC/Core/Unfold.hs#L293][g13] (`inlineBoringOk`); [compiler/GHC/Core/SimpleOpt.hs#L1314][g183] (Note [exprIsConApp_maybe on data constructors with wrappers]).

**Seen.** Orthotope, which builds without `StrictData`: in its builds' Core the one constructor wrapper called as a lazy argument, apart from `DynamicG`'s `$WA` passed to an unknown function in one scratch variant, is `$WAxis`, from `subArraysT`'s `reverse (zipWith Axis ots sh)`, whose loop conses each axis lazily, `ghc-internal:GHC.Internal.Types.: @Axis (Data.Array.Internal.$WAxis ipv ipv2) (go5 ipv1 ipv3)` (the tip's `Data/Array/Internal.dump-simpl`, whitespace collapsed), and inlining copies the loop into the modules that use it, the benchmark's Ops modules among them; the `OpsShaped.dump-stg-final` of CV, O26's build with the strict `convertE` default, holds the thunk, `go27_sat :: Data.Array.Internal.Axis = {ipv, ipv2} \u [] Data.Array.Internal.$WAxis ipv ipv2;`. In horde-ad, built with `StrictData`, no thunk calls a wrapper: of the 150642 thunks in the STG of its 72 modules under HEAD, none has a `$WK` call for its body, and its Core holds no saturated `$WK` call in a lazy position. Only its seven constructors with a field unpacked by `-funbox-small-strict-fields` (`AstVarName`, `FtkAndBoundsBounds`, `DeltaSliceR`, `InputId`, `NodeId`, `ArgsAdam`, `StateAdam`) have a wrapper that is not `boring_ok`, and each call of one is a tail call or a partial application. `StrictData`'s thunks there instead evaluate the fields and allocate the constructor, 3344 of them, the most entered building `AstProject2` in `AstInline`'s `inlineAst`.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A25-data-con-wrappers`, variants `base` with `-dinline-check $W` and `stg` with `-ddump-stg-final`): a constructor with a strict field, which `-O` unpacks (`-funbox-small-strict-fields`), and one with a strict field unpacked by its pragma, each applied to a variable as a lazy argument, and the first under a `case`.

```haskell
module M where

data S = S !Int

data U = U {-# UNPACK #-} !Int

boringS :: Int -> Maybe S
boringS x = Just (S x)

boringU :: Int -> Maybe U
boringU x = Just (U x)

caseS :: Int -> Int
caseS x = case S x of S y -> y + 1
```

`build.log` has `Inactive unfolding: $WS` (the phases before the final one), and in the final phase, whitespace collapsed:

```
Considering inlining: $WS arg infos [TrivArg] interesting continuation BoringCtxt some_benefit False is exp: True is work-free: True guidance ALWAYS_IF(arity=1,unsat_ok=True,boring_ok=False) case depth = 0 inline depth = 1 ANSWER = NO
Considering inlining: $WU arg infos [TrivArg] interesting continuation BoringCtxt some_benefit False is exp: True is work-free: True guidance ALWAYS_IF(arity=1,unsat_ok=True,boring_ok=False) case depth = 0 inline depth = 1 ANSWER = NO
```

The Core, whitespace collapsed:

```
boringS = \ x -> Just ($WS x)
boringU = \ x -> Just ($WU x)
caseS = \ x -> case x of { I# unbx -> I# (+# unbx 1#) }
```

In variant `stg` (`-ddump-stg-final`), the lazy argument is an updatable thunk:

```
boringS = \r [x] let { boringS_sat = \u [] $WS x; } in Just [boringS_sat];
```

**Reproduces small:** yes.

### A26. A worker/wrapper wrapper gets an always-inline stable unfolding, active from phase 2 or later after the function's rules, and is inlined only where an argument or the context is interesting

**Rule.** When worker/wrapper splits a function, the wrapper keeps the function's name and gets `mkWrapperUnfolding`: a `StableSystemSrc` unfolding of the wrapper body with `UnfWhen` guidance, the function's arity, `unsat_ok` True and `boring_ok` False ([compiler/GHC/Core/Unfold/Make.hs#L116][g184]; `wrap_unf`, [compiler/GHC/Core/Opt/WorkWrap.hs#L889][g185], in `mkWWBindPair`, [#L817][g186]). So, small as it is, a wrapper called with variable arguments in a boring context is not inlined (A01's rule, without the tiny-body exception), and the call goes through the wrapper to the worker; elsewhere it is inlined, at a call giving fewer arguments than its arity but at least one too, and the call becomes a call of `$wf` on unboxed arguments. Its activation is the latest of the function's own activation (the final phase for NOINLINE, A24), phase 2, and, for each rule about the function, the phase after the rule's first active phase (`mkStrWrapperInlinePrag`, [#L902][g187]; Note [Wrapper activation], [#L452][g188], points 1 to 4a), so it is never inlined in the initial phase, where specialisation and rules about the function are to fire first, and a client module does not inline it in its gentle run. The worker gets the same activation (`work_act` in `mkWWBindPair`; Note [Worker activation], [#L333][g189]), except under NOINLINE (A24), and, unless the function is INLINABLE (U08), an ordinary vanilla unfolding, exposed by the rules of U05. In the repros of A04, A05, A07, A09 and A23, worker/wrapper is switched off so that the functions keep their own guidance; with it on, the wrapper's `ALWAYS_IF(...,boring_ok=False)` guidance decides those calls instead.

**Seen.** Not in our record; horde-ad's comment at `astLetFun` (commit 8af6df9ac), on wrappers that "fail to specialize in other modules", falls under the specialisation appendix's "Which imported functions are specialised".

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A26-worker-wrapper-wrappers`, variant `base`, `-dinline-check inl`): a strict function in module `N`, split by worker/wrapper, called from `M` in a lazy argument and under a `case`.

```haskell
module N (inlW) where

inlW :: Int -> Int -> Int
inlW k y = case k of
  0 -> y + 1
  1 -> y * 2
  2 -> y - 3
  3 -> y * y
  _ -> y
```

```haskell
module M where

import N (inlW)

boring :: Int -> Int -> Maybe Int
boring k y = Just (inlW k y)

cased :: Int -> Int -> Bool
cased k y = case inlW k y of { 0 -> True; _ -> False }
```

`N`'s interface: the wrapper's activation and stable unfolding:

```
   Strictness: <1!P(1L)><1!P(L)>, CPR: 1, Inline: [2],
   Unfolding: Core: StableSystem <2,TrueFalse>
```

In `M`, `build.log` has `Inactive unfolding: inlW` (the gentle run), then, whitespace collapsed:

```
Considering inlining: inlW arg infos [TrivArg, TrivArg] interesting continuation BoringCtxt some_benefit False is exp: True is work-free: True guidance ALWAYS_IF(arity=2,unsat_ok=True,boring_ok=False) case depth = 0 inline depth = 1 ANSWER = NO
Considering inlining: inlW arg infos [TrivArg, TrivArg] interesting continuation CaseCtxt some_benefit True is exp: True is work-free: True guidance ALWAYS_IF(arity=2,unsat_ok=True,boring_ok=False) case depth = 0 inline depth = 1 ANSWER = YES
```

The Core, whitespace collapsed:

```
boring = \ k y -> Just (inlW k y)
cased = \ k y -> case k of { I# ww -> case y of { I# ww1 -> $wcased ww ww1 } }
```

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A26-wrapper-unfolding`, variant `base`, with `-dinline-check f`): two functions that worker/wrapper splits, one with a rule active from phase 1, and an importer of the other.

```haskell
module A (f, g) where

-- Both split by worker/wrapper: strict in both arguments, an Int result.
f :: Int -> Int -> Int
f x y
  | x > 1000 = x * y + 7 * x - y
  | x > 500 = x - y * 3 + 11
  | x > 300 = (x + y) * (x - y) + 5
  | x > 200 = x * x * y - 13
  | x > 100 = x * y * y + 17 * x - 3 * y
  | x > 50 = (x - 7) * (y + 9) - x * 21
  | x > 10 = x * 31 + y * 37 - x * y * 41
  | otherwise = (x + 43) * (y - 47) * (x - y)

-- A body differing in one guard, with a rule active from phase 1.
g :: Int -> Int -> Int
g x y
  | x > 1000 = x * y + 7 * x - y
  | x > 500 = x - y * 3 + 11
  | x > 300 = (x + y) * (x - y) + 5
  | x > 200 = x * x * y - 13
  | x > 100 = x * y * y + 17 * x - 3 * y
  | x > 50 = (x - 7) * (y + 9) - x * 21
  | x > 10 = x * 31 + y * 37 - x * y * 41
  | otherwise = (x + 53) * (y - 59) * (x - y)

{-# RULES "g/zero" [1] forall y. g 0 y = y #-}
```

```haskell
module B (useF) where

import A

useF :: Int -> Int
useF n = f n 3 + 1
```

The interface gives the wrapper `f` `Strictness: <1!P(L)><1!P(L)>, CPR: 1, Inline: [2], Unfolding: Core: StableSystem <2,TrueFalse>` over `case x of wild { GHC.Internal.Types.I# ww -> case y of wild1 { GHC.Internal.Types.I# ww1 -> case $wf ww ww1 of ww2 ...`, and the worker `$wf` `Strictness: <L><L>, Inline: [2], Unfolding: Core: <vanilla>`. With the rule, the entries of `g` and `$wg` both read `Inline: [0]`. Compiling B, `-dinline-check f` prints `Inactive unfolding: f` in the first passes before `f` is inlined (`Inlining done: f`), leaving `case $wf ww 3# of ww2 { __DEFAULT -> I# (+# ww2 1#) }`.

**Reproduces small:** yes.

### A27. In an unfolding written to an interface, a function imported through an hs-boot file is wrapped in `noinline`

**Rule.** An Id imported with `{-# SOURCE #-}` carries a `BootUnfolding`. When an unfolding that mentions such an Id is written to the interface, `toIfaceVar` replaces the reference by `noinline` applied to it, so wherever that unfolding is inlined, the boot-imported function is not inlined at that call (by A14's mechanism: it is then applied to no value argument). This breaks the loop that the occurrence analyser cannot detect across modules: inlining `eqRSR` in its own module exposes `eqSR`'s unfolding, which calls `eqRSR` again, and neither is a loop breaker. The `noinline` stays in the Core and CorePrep removes it. Source: [compiler/GHC/CoreToIface.hs#L657][g190] (`toIfaceVar`, `isBootUnfolding`), [#L704][g191] (Note [Inlining and hs-boot files]); [compiler/GHC/Builtin/WiredIn/Ids.hs#L520][g115] (Note [noinlineId magic], reason 2).

**Seen.** Not in our record.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A27-hs-boot-noinline`, variant `base`): the example of Note [Inlining and hs-boot files], two modules and the boot file of one.

```haskell
-- RSR.hs-boot
module RSR where

data RSR
eqRSR :: RSR -> RSR -> Bool
```

```haskell
module SR where

import {-# SOURCE #-} RSR

data SR = MkSR RSR

eqSR :: SR -> SR -> Bool
eqSR (MkSR r1) (MkSR r2) = eqRSR r1 r2
```

```haskell
module RSR where

import SR

data RSR = MkRSR SR

eqRSR :: RSR -> RSR -> Bool
eqRSR (MkRSR s1) (MkRSR s2) = eqSR s1 s2

foo :: RSR -> RSR -> Bool
foo x y = not (eqRSR x y)
```

`eqSR`'s unfolding in `SR`'s interface, whitespace collapsed:

```
case ds1 of wild1 { MkSR r2 -> GHC.Internal.Magic.noinline @(RSR.RSR -> RSR.RSR -> GHC.Internal.Types.Bool) RSR.eqRSR r1 r2 } }]
```

Compiling `RSR`, `-ddump-inlinings` records `Inlining done: eqRSR` and `Inlining done: eqSR`, and `foo` ends, whitespace collapsed:

```
case noinline eqRSR r1 r2 of { False -> True; True -> False }
```

**Reproduces small:** yes.

### A28. A derived Generic instance's `from` and `to` get INLINE [1] when the type is small

**Rule.** `-finline-generics`, on at `-O` and `-O2`, adds `{-# INLINE [1] from #-}` and `{-# INLINE [1] to #-}` to a derived `Generic` (or `Generic1`) instance when inlining is judged useful by the shape of the type: at most one constructor; or at most 4 constructors with at most 5 fields each; at most 8 with at most 2; at most 16 with at most 1; at most 24 with none; never above 24 constructors. Otherwise the methods have no pragma and are decided as in A03 and A04. `-finline-generics-aggressively` adds the pragmas whatever the shape; `-fno-inline-generics` never, unless `-finline-generics-aggressively` is also given. Source: [compiler/GHC/Tc/Deriv/Generics.hs#L351][g192] (`mkBindsRep`, `inlining_useful`, `inline1`), [#L1064][g193] (Note [Generics performance tricks]); [compiler/GHC/Driver/DynFlags.hs#L1340][g194] (on at levels 1 and 2).

**Seen.** Not in our record.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A28-inline-generics`, variants `base`, `nogen` with `-fno-inline-generics`, `aggr` with `-finline-generics-aggressively`): two derived instances, one inside the table and one outside it.

```haskell
{-# LANGUAGE DeriveGeneric #-}
module M where

import GHC.Generics (Generic)

data Small = SA Int Int | SB Int
  deriving Generic

data Big = B1 Int Int Int | B2 Int Int Int | B3 Int Int Int
         | B4 Int Int Int | B5 Int Int Int
  deriving Generic
```

The interface, `from` of each, whitespace collapsed; in `base`:

```
$fGenericSmall_$cfrom :: Small -> GHC.Internal.Generics.Rep Small x [HasNoCafRefs, TagSig: <TagFun[TagEPT]>, LambdaFormInfo: LFReEntrant 1, Arity: 1, Strictness: <1L>, Inline: [1] (sat-args=1), Unfolding: Core: StableUser <1,FalseFalse>
$fGenericBig_$cfrom :: Big -> GHC.Internal.Generics.Rep Big x [HasNoCafRefs, TagSig: <TagFun[TagEPT]>, LambdaFormInfo: LFReEntrant 1, Arity: 1, Strictness: <1L>, Unfolding: Core: <vanilla>
```

in `nogen`:

```
$fGenericSmall_$cfrom :: Small -> GHC.Internal.Generics.Rep Small x [HasNoCafRefs, TagSig: <TagFun[TagEPT]>, LambdaFormInfo: LFReEntrant 1, Arity: 1, Strictness: <1L>, Unfolding: Core: <vanilla>
```

and in `aggr`:

```
$fGenericBig_$cfrom :: Big -> GHC.Internal.Generics.Rep Big x [HasNoCafRefs, TagSig: <TagFun[TagEPT]>, LambdaFormInfo: LFReEntrant 1, Arity: 1, Strictness: <1L>, Inline: [1] (sat-args=1), Unfolding: Core: StableUser <1,FalseFalse>
```

`to` follows `from` in each variant.

**Reproduces small:** yes.

### A29. INLINE on a dispatcher over `typeRep` copies the case into every caller, where the comparisons stay but become constants and only the matching branch keeps a body

**Rule.** A dispatch written as a case over `typeRep @r`, each branch a pattern `Is @T` over `eqTypeRep`, is not decided at compile time even where `r` is fixed at the caller. Each branch tests `sameTypeRep`, which compares the two `typeRepFingerprint`s ([libraries/ghc-internal/src/GHC/Internal/Data/Typeable/Internal.hs#L692][g195], `sameTypeRep`); a known type's `TypeRep` is desugared to `mkTrCon` applied to its `TyCon` ([compiler/GHC/HsToCore/Binds.hs#L1785][g196], `ds_ev_typeable`), and `mkTrCon` computes the fingerprint by `fingerprintFingerprints` ([Internal.hs#L435][g197] and [#L444][g198], `mkTrCon`), an MD5 under `unsafeDupablePerformIO` ([libraries/ghc-internal/src/GHC/Internal/Fingerprint.hs#L48][g199]), which the simplifier does not evaluate. So when INLINE copies the dispatch into a caller at `Double`, the comparisons stay; having no free variables they float to top-level constants, evaluated once, and every call site cases on them. What the known type does decide is the branches' bodies: in a branch for another type the `HRefl` alternative would need `Int ~ Double`, so `filterAlts` drops it (`dataConCannotMatch`, [compiler/GHC/Core/Utils.hs#L1094][g200], called from `prepareAlts`, [compiler/GHC/Core/Opt/Simplify/Utils.hs#L2637][g201]), the known constructor then finds no alternative, and the branch becomes `impossibleError` (`missingAlt`, [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4008][g202]). Only the matching branch's kernel is left, at the caller's type and unboxed. Without INLINE on the dispatcher the case is compiled once, in the defining module, polymorphic: each call compares the argument's `TypeRep` at run time, and each branch runs the kernel at a type given only by the equality, so its accumulator, of the abstract type `r`, is boxed at every step.

**Seen.** `docs/pragmas-and-flags.md`, section "What goes", the paragraph on the `OpsConcrete` pragmas; commit 0a8d839b3, "Drop 165 inlining and specialisation pragmas and -flate-dmd-anal"; commit 7080e577d, "Restore OpsConcrete's higher-order and typeRep-dispatch INLINEs"; and the comment above `tkcast` in `src/HordeAd/Core/OpsConcrete.hs`. horde-ad's operations that dispatch on the element type, directly or through `contFromTypeable` and `contFromTKAllNum`, keep their INLINE "so that a caller at known types gets one monomorphic kernel"; with the dispatchers `tindexZR`, `tgatherZR` and their family INLINE as well, "each user call site received the whole case over the element types", which cost 309 s of package build (1380 s against 1071 s). The text left open whether the case is decided where the type is known. In the repro the comparisons are not decided where the type is known, and the branches' bodies are; GHC [#27879](https://gitlab.haskell.org/ghc/ghc/-/work_items/27879) (`docs/ghc-issue-late-specialise-no-float-out.md` in horde-ad) records the build in which no float-out followed and the `TypeRep` was rebuilt, MD5 included, on every call.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A29-typerep-dispatch-inline`, variants `inline` with the dispatcher `disp` INLINE, by `-DINL`, and `none` without a pragma, `contFrom` INLINE in both; `run` is `100000`; `measure.sh N`): a client calling `disp` at `Double` in a loop and at three more sites.

```haskell
{-# LANGUAGE CPP, BangPatterns, GADTs, PatternSynonyms, ViewPatterns, TypeOperators,
             PolyKinds, TypeApplications, ScopedTypeVariables,
             ConstraintKinds, RankNTypes, TypeAbstractions #-}
-- horde-ad's dispatch on the element type, cut down: contFrom is
-- contFromTypeable, disp a dispatcher such as tindexZR.
module Lib (module Lib) where

import Data.Type.Equality (type (~~))
import Type.Reflection

data Dict c a where
  Dict :: c a => Dict c a

pattern Is :: forall a b. Typeable a => a ~~ b => TypeRep b
pattern Is <- (eqTypeRep (typeRep @a) -> Just (HRefl :: a :~~: b))

-- INLINE throughout, as horde-ad's contFromTypeable.
contFrom :: forall r a. Typeable r => (Dict Num r -> a) -> a
{-# INLINE contFrom #-}
contFrom f = case typeRep @r of
  Is @Int -> f Dict
  Is @Double -> f Dict
  Is @Float -> f Dict
  _ -> error "contFrom: unexpected type"

-- The kernel, specialised at each type through the Dict.
sumK :: Num r => [r] -> r
{-# INLINABLE sumK #-}
sumK = go 0
  where go !acc [] = acc
        go !acc (y : ys) = go (acc + y) ys

-- The dispatcher, INLINE (variant inline) or without a pragma (none).
#if defined(INL)
{-# INLINE disp #-}
#endif
disp :: forall r. Typeable r => [r] -> r
disp xs = contFrom @r (\Dict -> sumK xs)
```

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import Lib
import System.Environment (getArgs)

-- Opaque, so that each iteration dispatches anew.
{-# OPAQUE pass #-}
pass :: Int -> a -> a
pass _ x = x

-- Three call sites at a known type.
site1, site2, site3 :: [Double] -> Double
site1 xs = disp xs + 1
site2 xs = disp (map (* 2) xs)
site3 xs = disp xs * disp (reverse xs)

main :: IO ()
main = do
  [repss] <- getArgs
  let reps = read repss :: Int
      xs = [1, 2, 3] :: [Double]
      loop :: Int -> Double -> Double
      loop 0 !acc = acc
      loop r !acc = loop (r - 1) (acc + disp (pass r xs))
  print (loop reps 0 + site1 xs + site2 xs + site3 xs)
```

`inline`: `Main.dump-inlinings` has `Inlining done: disp` at each of the five calls, and in `Main.dump-simpl` the `TypeRep`s are built and compared as top-level constants, `main17 = mkTrCon $tcInt []`, `main16 = sameTypeRep main17 main13` and `main15 = sameTypeRep main13 main13` (`main13` being `Double`'s), where `lvl10 = impossibleError main10`. The loop cases on them at every iteration, with whitespace collapsed: `case main16 of { False -> case main15 of { False -> case main12 of { False -> case main11 of {}; True -> case lvl10 of {} }; True -> case $wgo 0.0## (pass (I# wild) main_xs) of ww2 { __DEFAULT ->`; the other three sites share one more copy of the chain. `Main`'s Tidy Core is `{terms: 346,`. `none`: no `Inlining done: disp`; the loop calls `case disp (C:Typeable main10) (pass (I# wild) main_xs) of { D# y ->`, and `Main` is `{terms: 234,`. `Lib`'s `disp` tests the argument at each call, `case sameTypeRep disp7 (typeRep# $dTypeable) of { False -> case sameTypeRep disp6 (typeRep# $dTypeable) of {`, and its `Double` branch boxes the accumulator at each element, `` jump go ((D# (+## x y1)) `cast` <Co:12>) ys ``.

By `measure.sh 100000` (100000 and 200000 calls differenced, twice, the same figures): `inline` 149.3 instructions and 16.0 bytes a call, `none` 294.6 instructions and 64.0 bytes, on a list of three elements. The Core accounts for the bytes as the `I#` given to `pass`, in both, and in `none` one `D#` an element. Of the 145 instructions a call `none` runs beyond `inline`, about 118 are the two out-of-line `sameTypeRep` tests with the entries of the `TypeRep` constants they compare, about 14 the boxed accumulator, the loop 94 instructions a call against 80, 26 an element against 20, and about 16 the out-of-line call, by callgrind attributing each instruction to the nearest symbol before it, at 100000 and 200000 calls differenced (`~/r/horde-ad/dist-inlcat/cases/A29-typerep-cost/cgaddr.py`); the three overcount the 145 by 3.

The accumulator is boxed for U21's reason. A second repro (`~/r/horde-ad/dist-inlcat/cases/A29-typerep-cost`, variants `inline` and `none` as the first repro's; `castk`, with the dispatch written out and the kernel called at the branch's own type, by `-DCASTK`; `nonetypes` and `nonesig`, `none` dumping types and demand signatures; `Main` and `run` are the first repro's) has the first repro's `Lib` with `disp` also written as:

```haskell
-- ...
module Lib (module Lib) where
-- ...
#if defined(CASTK)
disp xs = case typeRep @r of
  Is @Int -> sumK @Int xs
  Is @Double -> sumK @Double xs
  Is @Float -> sumK @Float xs
  _ -> error "disp: unexpected type"
#else
disp xs = contFrom @r (\Dict -> sumK xs)
#endif
```

In `none` the kernel's loop is a join point at the abstract type, `joinrec { go [Occ=LoopBreaker, Dmd=SC(S,C(1,L))] :: r -> [r] -> r [LclId[JoinId(2)(Nothing)], Arity=2, Str=<1L><1L>,`, its accumulator equal to a `Double` only through the match's coercion, ``case acc1 `cast` (<Co:11> :: r ~R# Double) of { D# x ->`` (whitespace collapsed): strict, but of a type worker/wrapper cannot split (`canUnboxArg`, [compiler/GHC/Core/Opt/WorkWrap/Utils.hs#L624][g203]; `normSplitTyConApp_maybe`, [compiler/GHC/Core/Utils.hs#L3154][g204]). Called at the branch's own type, in `castk`, the kernel is the unboxed `$wgo1`, `: y ys -> case y of { D# y1 -> $wgo1 (+## ww y1) ys }`; there full laziness floats the tests out of `disp`'s lambda, so `castk` does not compare with `none` call for call.

**Reproduces small:** yes.

### A30. A default method recursing through its own method-level dictionary is no loop breaker: under INLINE an importer at known dictionaries inlines it without end, under INLINABLE it specialises it

**Rule.** An instance taking a default gets the default's pragma and body on its method (U11). Where the default recurses through a dictionary its method takes, as a method with its own constraint (`tappend :: Base t => ...`) does under an instance with a context, the instance method refers to itself only through that lambda-bound dictionary, not as a free variable, so the occurrence analyser, which groups bindings by their free variables (`occAnalRecBind` and `makeNode`, [compiler/GHC/Core/Opt/OccurAnal.hs#L1239][g205] and [#L1817][g206]), puts it in no recursive group and it is no loop breaker (A11 does not apply). In an importer calling it at known dictionaries, each recursive call becomes, once the dictionaries are known, a direct call of the same method. Under INLINE that call is saturated with two dictionaries as value arguments, so it has `some_benefit` and is inlined (A01, A07), and so is the next one: compiling the importer exhausts the simplifier's ticks. Under INLINABLE the importer specialises the method at the known dictionaries instead, and the specialisation's recursive calls go to itself through the specialisation rule. Without a pragma, in a module built `-fno-expose-overloaded-unfoldings`, the method's unfolding is exposed only if it is within the creation threshold (`addExternal`, `show_unfolding`, [compiler/GHC/Iface/Tidy.hs#L704][g207]: a stable unfolding always, a vanilla one when `profitable`, an overloaded one past the threshold only under `ExposeOverloaded`), so a default past the threshold is called out of line, with its dictionaries, every class method in it selected from them at run time. A point-free INLINE default (`size = (* 2) . shape`) gives the instance method a stable unfolding whose count covers only the instance's dictionary (E02) and whose template carries the default's body, not a call, and an instance method taking another default that calls it (`tsz a = size a + 1`) carries that body too, with or without the pragma, since the body is small. Where the class lacks the superclass whose method the default calls, as horde-ad's `BaseTensor` lacks `LetTensor` and `ShareTensor`, the default recurses through the class's own dictionary, which under the instance is the dictionary function applied to the instance's context, and the class-op rule (`dictSelRule`, [compiler/GHC/Types/Id/Make.hs#L447][g121]) turns that call into a direct call of the instance method itself: the method is then self-recursive in its defining module, hence a loop breaker (Note [Choosing loop breakers], [compiler/GHC/Core/Opt/OccurAnal.hs#L1318][g93]) and never inlined, and an importer specialises it under INLINE as under INLINABLE.

**Seen.** Commits 8b78b6566, "Drop INLINE from recursive functions and methods where it costs", b3c09d407, "Record what the INLINE on tunravelToListShare buys", and 1cf95b02c, "Make tappend INLINABLE and drop tunravelToListShare's pragma", the comments at `tappend` and `tunravelToListShare` in `src/HordeAd/Core/Ops.hs`, and `docs/pragmas-and-flags.md`, sections "What stays, and why" and "Pitfalls met": in `inlineMicroBench`, `AstRaw`'s `tappend` (its instance in `OpsAst`, built `-fno-expose-overloaded-unfoldings`, under `KnownSpan s =>`) ran 0.98 times INLINE's instructions under INLINABLE and 1.28 times with no pragma, and `tunravelToListShare` 1.045 times under INLINABLE and with no pragma alike. The repro gives the loss without a pragma (2.2 and 2.0 times INLINABLE's instructions here) and its cause, and, with horde-ad's class shape, INLINE equal to INLINABLE; not horde-ad's equality of no pragma and INLINABLE on `tunravelToListShare`.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A30-class-default-recursing`, variants `none`; `inlineA` and `inlinableA` with the pragma on `tappend`'s default, by `-DINL_A` and `-DINB_A`; `inlineU` and `inlinableU` on `tunravel`'s, by `-DINL_U` and `-DINB_U`; `inlineS` with INLINE on `size`'s, by `-DINL_S`; `inlineAchk`, `inlineA` with `-dinline-check $fLetT_$ctappend`; `nonenosup`, `inlineAnosup`, `inlinableAnosup`, `inlineUnosup` and `inlinableUnosup`, `none` and the four pragma variants with `Base` lacking its superclasses, by `-DNOSUP`, as horde-ad's `BaseTensor` does; `run` is `append 100000`; `measure.sh N`, and `measure-nosup.sh N` for the `NOSUP` variants): horde-ad's two defaults cut down, in a module opting out of exposure, with an instance under a context, called by a client in loops.

```haskell
{-# LANGUAGE CPP, BangPatterns, ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-expose-overloaded-unfoldings #-}
-- horde-ad's LetTensor and ShareTensor defaults, cut down, with an
-- instance in the same module built as OpsAst is, opting out of exposure.
module Lib (module Lib) where

import Data.Kind (Type)

-- A singleton for the tensor kind: a leaf or a product.
data K = KS | KR | KSh | KX | KP K K

class Let t where
  tlet :: t -> (t -> t) -> t
  -- tappend's shape: recurses through the class at each product.
  tappend :: Base t => K -> t -> t -> t
#if defined(INL_A)
  {-# INLINE tappend #-}
#elif defined(INB_A)
  {-# INLINABLE tappend #-}
#endif
  tappend k a b = case k of
    KS -> bappend a b
    KR -> tlet a $ \ !a' -> bappendR (bfst a') (bsnd b)
    KSh -> tlet b $ \ !b' -> bappendS (bsnd a) (bfst b')
    KX -> bappendX (bfst a) (bfst b)
    KP k1 k2 -> tlet a $ \ !a' -> tlet b $ \ !b' ->
      bpair (tappend k1 (bfst a') (bfst b')) (tappend k2 (bsnd a') (bsnd b'))

class Share t where
  tshare :: t -> t
  tunpair :: t -> (t, t)
  -- tunravelToListShare's shape: a list per leaf, zipped at each product.
  tunravel :: Base t => K -> t -> [t]
#if defined(INL_U)
  {-# INLINE tunravel #-}
#elif defined(INB_U)
  {-# INLINABLE tunravel #-}
#endif
  tunravel k u = case k of
    KS -> let !u' = tshare u in btoList u'
    KR -> let !u' = tshare u in btoListR (bfst u') ++ btoListS (bsnd u')
    KSh -> let !u' = tshare u in btoListS (bsnd u') ++ btoListX (bfst u')
    KX -> let !u' = tshare u in btoListX u' ++ btoListR (bsnd u')
    KP k1 k2 -> let (!u1, !u2) = tunpair u
                in zipWith bpair (tunravel k1 u1) (tunravel k2 u2)

#if defined(NOSUP)
class Base t where
#else
class (Let t, Share t) => Base t where
#endif
  bappend, bappendR, bappendS, bappendX :: t -> t -> t
  bpair :: t -> t -> t
  bfst, bsnd :: t -> t
  btoList, btoListR, btoListS, btoListX :: t -> [t]

-- A point-free default with INLINE (or none), called by
-- another default.
class Sized t where
  shape :: t -> Int
  size :: t -> Int
#if defined(INL_S)
  {-# INLINE size #-}
#endif
  size = (* 2) . shape
  tsz :: t -> Int
  tsz a = size a + 1

-- The instance, a small term language indexed by a span, its instances
-- under a KnownSpan context as horde-ad's AstRaw s.
class KnownSpan (s :: Type) where
  spanK :: proxy s -> Int

data Full
instance KnownSpan Full where
  spanK _ = 3

data T (s :: Type) = L !Int | Cat !Int (T s) (T s) | P (T s) (T s) | Fst (T s)
         | Snd (T s) | Sh (T s)

instance KnownSpan s => Let (T s) where
  tlet a f = f a
instance KnownSpan s => Share (T s) where
  tshare = Sh
  tunpair (P a b) = (a, b)
  tunpair u = (Fst u, Snd u)
instance KnownSpan s => Base (T s) where
  bappend = Cat (spanK ([] :: [s]))
  bpair = P
  bfst (P a _) = a
  bfst a = Fst a
  bsnd (P _ b) = b
  bsnd a = Snd a
  bappendR = Cat 1
  bappendS = Cat 2
  bappendX a b = Cat 4 b a
  btoList u = [u, Sh u]
  btoListR u = [Fst u, u]
  btoListS u = [Snd u, Sh u]
  btoListX u = [u, u]
instance KnownSpan s => Sized (T s) where
  shape (L n) = n + spanK ([] :: [s])
  shape _ = 1
```

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import Lib
import System.Environment (getArgs)

-- Opaque, so that each iteration computes anew.
{-# OPAQUE pass #-}
pass :: Int -> a -> a
pass _ x = x

depth :: T s -> Int
depth (L n) = n
depth (Cat n a b) = n + depth a + depth b
depth (P a b) = depth a + depth b
depth (Fst a) = depth a + 1
depth (Snd a) = depth a + 1
depth (Sh a) = depth a + 1

main :: IO ()
main = do
  [what, repss] <- getArgs
  let reps = read repss :: Int
      k = KP KS (KP KS KS)
      t = P (L 1) (P (L 2) (L 3)) :: T Full
      loopA, loopU, loopS :: Int -> Int -> Int
      loopA 0 !acc = acc
      loopA r !acc = loopA (r - 1) (acc + depth (tappend (pass r k) t t))
      loopU 0 !acc = acc
      loopU r !acc = loopU (r - 1) (acc + sum (map depth (tunravel (pass r k) t)))
      loopS 0 !acc = acc
      loopS r !acc = loopS (r - 1) (acc + tsz (pass r t))
  print $ case what of
    "append" -> loopA reps 0
    "unravel" -> loopU reps 0
    _ -> loopS reps 0
```

`none`: `Main` calls the instance method out of line with its dictionaries, `case $wdepth ($fLetT_$ctappend (C:KnownSpan $fKnownSpanFull_$cspanK) $dBase (pass (I# wild) k1) t4 t4)` (whitespace collapsed), with no `Inlining done: $fLetT_$ctappend`, and in `Lib` that method selects every class method from the dictionary, as `KX -> bappendX $dBase (bfst $dBase eta1) (bfst $dBase eta2);`. `inlinableA`: `Main` specialises it, `"SPEC/Main $fLetT_$ctappend @Full" forall $dKnownSpan $dBase1. $fLetT_$ctappend $dKnownSpan $dBase1 = $s$fLetT_$ctappend`, and the loop calls `case $wdepth ($s$fLetT_$ctappend (pass (I# wild) k1) t4 t4) of ww2`; `inlinableU` has `"SPEC/Main $fShareT_$ctunravel @Full"`. `inlineA` and `inlineU` fail compiling `Main`, `Simplifier ticks exhausted When trying RuleFired Class op bsnd` and `... Class op bfst`, and `inlineAchk` shows each decision, the dictionaries giving the benefit (whitespace collapsed): `Considering inlining: $fLetT_$ctappend arg infos [ValueArg, ValueArg, TrivArg, NonTrivArg, NonTrivArg] interesting continuation BoringCtxt some_benefit True is exp: True is work-free: True guidance ALWAYS_IF(arity=5,unsat_ok=False,boring_ok=False)`, followed by `ANSWER = YES`. `inlineS`: the instance's `size` has `Strictness: <MP(1C(1,L))><1L>, CPR: 1, Inline: (sat-args=0), Unfolding: Core: StableUser <1,FalseFalse>`, its template the default's body; in `inlineS` and `none` alike `$fSizedT_$ctsz = \ @s $dKnownSpan a -> case a of { __DEFAULT -> lvl1; L bx -> case spanK $dKnownSpan [] of { I# y -> I# (+# (*# (+# bx y) 2#) 1#)`.

By `measure.sh 100000` (100000 and 200000 calls differenced, twice, the same figures): `tappend` 1962.3 instructions and 848.0 bytes a call with no pragma, 873.6 and 512.0 under INLINABLE; `tunravel` 2293.2 and 1120.0 with no pragma, 1160.6 and 736.0 under INLINABLE; `tsz` 34.5 and 16.0 with and without INLINE on `size`.

**Reproduces small:** in part. The loss without a pragma and INLINABLE's specialisation, yes; the point-free default's body carried into the instance, yes. INLINE against INLINABLE: with the superclasses, under INLINE the client does not compile; without them (`NOSUP`), as in horde-ad, the instance method is a loop breaker, `Unfolding(loop-breaker): Core: StableUser <5,FalseFalse>` in `inlineAnosup`'s `Lib.iface` and `Rec { $fLetT_$ctappend = \ @s $dKnownSpan $dBase eta eta1 eta2 ->` in its `Lib.dump-simpl`, the client calling its specialisation `$s$fLetT_$ctappend`, never inlining it, and INLINE and INLINABLE run alike, by `measure-nosup.sh 100000` 873.6 instructions and 512.0 bytes a call at `tappend` against 1507.9 and 640.0 without a pragma, and 1160.6 and 736.0 at `tunravel` against 1761.3 and 1008.0; horde-ad's residues, 0.98 and 1.045, not reached. Two departures from horde-ad hide the case: with the instance under no context (`instance Base T`), the method's `Base T` is solved from the top-level instance, its dictionary argument is absent (`<A>`), and the defining module specialises the recursion itself, all three pragmas giving the same code; and with smaller defaults, the methods' vanilla unfoldings are within the creation threshold and exposed despite the opt-out, so that the importer inlines them at their recursive calls without a pragma too.

### A31. `-g` wraps expressions in source notes, at which exitification stops and under which floated literals stay apart

**Rule.** At any `-g` level the desugarer adds source notes (`needSourceNotes`, [compiler/GHC/Driver/Session.hs#L3956][g208]: `debugLevel dflags > 0`), ticks around most expressions, which the optimiser then carries. They change what it does in at least three places. Exitification descends from a `joinrec`'s body only through `case` and `let` (`exitifyRec`, [compiler/GHC/Core/Opt/Exitify.hs#L111][g209]); any other expression, a tick included, is returned as it is (`go _ ann_e = return (deAnnotate ann_e)`, [#L195][g210]), so a loop whose body is `src<...> case ...` gets no exit join point, and the exit path stays inline in the loop (A20). And, under `-g1`, constants floated to top level carry the source note of the definition they came from, the literal `"bad index: "#` under `inlFail`'s and again under `inlOk`'s, and stay two bindings where without `-g` the two definitions share one; CSE's lookup strips floatable ticks (Note [Dealing with ticks], [compiler/GHC/Core/Opt/CSE.hs#L560][g211]; `extendCSEnv`, [compiler/GHC/Core/Opt/CSE.hs#L888][g212]) and finds the earlier literal, but returns the hit wrapped again in the ticks it stripped (`try_for_cse`, [#L684][g213]), as `src<...> x`, while CSE merges a top-level string binding only by substituting a bare variable for it (`cse_bind`'s case for strings, [#L439][g214], and Note [Take care with literal strings], [#L527][g215]; `extendCSEnvWithBinding`, [#L487][g216], its `use_subst`, [#L509][g217]); so each literal keeps its own uses, and the expressions built on it, such as `unpackCString# lvl`, find no match either (second repro). And cast worker/wrapper splits `x = e |> co` only when the cast is the right-hand side's root (`tryCastWorkerWrapper`, [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L617][g218], any other right-hand side taking the equation for "All other bindings", [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L685][g219]), so under `-g` a binding `x = src<...> (e |> co)` keeps its cast (third repro). The simplifier's own treatment of a source note does not move a call's context: a soft-scoped tick (`tickishHasSoftScope`, [compiler/GHC/Types/Tickish.hs#L293][g220], true of `SourceNote`) gets the whole continuation pushed inside it (`simplTick`, [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L1457][g221]), so a call under one gets the arguments and context it would get without it.

**Seen.** `docs/perf-checklist.md`, section "The tools", the `tools/src-attrib.py` item, and commit 38602ca6f: "on the module it was tried on `-g1` changed what GHC floated and duplicated, so it does not predict what a pragma saves: build the change and compare with `core-diff`" (orthotope's test suite, two builds), which fits a build under GHC HEAD, where `-g1` nearly doubles the Core of most of the suite's test modules, and not one under 9.12.4 or 9.14.1, where no module of the suite grows past 1.15x. A sweep of every other case directory present on 2026-10-15 (`~/r/horde-ad/dist-inlcat/cases/A31-debug-info-changes-floating/sweep-g1.sh`, each variant built plain and with `-g1`, the Tidy Core compared with ticks suppressed) found the Core changed in many: of the three read, A07's by a case binder's name alone, A20's and A23's as here.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A31-debug-info-changes-floating`, variants `plain`, `g1` with `-g1`, both with `-dinline-check inlVal`, and `g1ticks`, `-g1` with `-dno-suppress-ticks`): A20's loop and A23's two functions sharing string literals, with A08's call shapes.

```haskell
module X where

-- A20's loop: the exit path of go, the 0 equation, is called at most once.
loop :: Int -> Int -> Int -> Int
loop t n0 x0 = go n0 x0
  where
    go :: Int -> Int -> Int
    go 0 x = t * (x * x) + t * x + x
    go n x = go (n - 1) (x + t)

-- A08's open question: an INLINE call applied in two steps, under a
-- let, a conditional and a case, each of which gets a source note.
{-# INLINE inlVal #-}
inlVal :: Int -> Int -> Maybe Int
inlVal x = \y -> case x of { 10 -> Nothing; _ -> Just (x + y + 10) }

ctxVal, ctxValLet, ctxValIf, ctxValCase :: Int -> Int -> Maybe Int
ctxVal x y = (inlVal x) y
ctxValLet x y = (let f = inlVal x in f) y
ctxValIf x y = (if x > 0 then inlVal x else inlVal (x + 1)) y
ctxValCase x y = (case x of { 11 -> inlVal x; _ -> inlVal (x + 2) }) y
```

```haskell
{-# OPTIONS_GHC -fno-worker-wrapper #-}
-- A23's module: the same string literals in a bottoming and a total
-- function.
module B (inlFail, inlOk, useFail, useOk) where

inlFail :: Int -> Int
inlFail n = errorWithoutStackTrace ("bad index: " ++ show n ++ " out of range")

inlOk :: Int -> String
inlOk n = "bad index: " ++ show n ++ " out of range"

useFail :: Int -> Int
useFail x = case x of { 0 -> inlFail 7; _ -> x }

useOk :: Int -> Int
useOk x = length (inlOk 7) + x
```

`plain`: `X`'s loop has `join { exit ww2 = case t of { I# x -> I# (+# (+# (*# x (*# ww2 ww2)) (*# x ww2)) ww2) } } in` and jumps to it, `0# -> jump exit ww3` (whitespace collapsed). `g1`: no `jump exit`; the branch keeps the body, `0# -> case t of { I# x -> I# (+# (+# (*# x (*# ww3 ww3)) (*# x ww3)) ww3) }`; `g1ticks` shows the tick in the way, `$wgo ww2 ww3 = src<X.hs:(8,5)-(9,31)> case ww2 of wild2 {`. In `B`, `plain`'s `inlFail` uses `inlOk`'s literals, `errorWithoutStackTrace (unpackAppendCString# inlOk3 (case n of { I# n1 -> ++ (itos n1 []) inlOk1 }))`, where `g1`'s has its own, `errorWithoutStackTrace (unpackAppendCString# lvl (case n of { I# n1 -> ++ (itos n1 []) lvl2 }))`, `g1ticks` giving `inlOk3` and `lvl` the same literal, each under its own definition's source note.

A second repro (`~/r/horde-ad/dist-inlcat/cases/A31-cse-ticked-literals`, variants `plain` and `g1`, and `plainu` and `g1u`, the same keeping uniques, all with `-ddump-cse -dno-suppress-ticks`): the first repro's `B` alone. In `plainu`'s CSE output the second literal's uses are the first's, `inlFail` using `lvl_sXu` and `lvl_sXX`, `errorWithoutStackTrace (unpackAppendCString# lvl_sXu (case n_avT of wild_aUs { I# n_aUt -> ++ (itos n_aUt []) lvl_sXX }))`; in `g1u`'s, each literal is under its definition's source note, `lvl_sXA = src<...> "bad index: "#`, and `inlFail` keeps its own, `errorWithoutStackTrace (unpackAppendCString# lvl_sXA (case n_avT of wild_aUs { I# n_aUt -> ++ (itos n_aUt []) lvl_sY2 }))` with `lvl_sY2 = src<...> unpackCString# lvl_sXB`, while a hit that is not a string becomes a ticked alias, `lvl_sXZ = src<...> src<...> lvl_sXX`, the source notes' spans elided here.

A third repro (`~/r/horde-ad/dist-inlcat/cases/A31-cast-under-note`, variants `plain`, `g1` with `-g1`, and `g1trace`, `-g1` with `-ddump-simpl-trace`, all with `-dno-suppress-ticks -dsuppress-idinfo -dsuppress-module-prefixes`): a binding whose right-hand side is a newtype's cast of a saturated call.

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

`plain` splits `n1` into the worker `n2` and a cast of it, inlined at the uses, ``n1 = n2 `cast` (Sym N:N :: Int ~R# N)`` and ``ns = : @N (n2 `cast` (Sym N:N :: Int ~R# N)) ns1``; `g1` keeps the cast under the source note, ``n1 = src<...> case $wf 3# of ww { __DEFAULT -> (I# ww) `cast` (Sym N:N :: Int ~R# N) }``, with no `n2`, its uses naming `n1`, `ns = src<...> : @N (src<...> n1) ns1` (whitespace collapsed, the source notes' spans elided); `g1trace` records the refusal, ``tcww:no bndr: n1 rhs: src<...> (f (src<...> I# 3#)) `cast` (Sym N:N :: Int ~R# N)``.

**Reproduces small:** yes, the exitification, the literals and what keeps them apart, and the cast. Rebuilt under HEAD, orthotope at "Rotate ranked arrays through DynamicG's rotate" shows how they act on the module the Seen names: its test module DynamicTest and library module `Data.Array.Internal.ShapedS` were each recompiled alone with `-dannot-lint` and every pass dumped. `-g1` leaves what Float out does with a given input as it was: `-dannot-lint` names no Float out pass in DynamicTest, and the first Float out floats as many lets with the module's notes as without them; the second floats 34167 against 34233, its input differing after Exitification. What `-g1` moves is what CSE merges. The module's own source notes keep each floated copy of vector's and orthotope's call-stack literals apart, whether or not the copies' notes differ, and with them the `unpackCString#`, `SrcLoc`, `PushCallStack` and `undefined` built on each. That nearly doubles the Tidy Core (DynamicTest 91,455 terms to 165,784); the library's `-g1` alone changes it only by names. Exitification stops almost only at the library's notes, which an importer keeps only under `-g` (DynamicTest's exit join points: 140 with no notes, 138 with the module's, 1 with the library's too). And 111 bindings of DynamicTest keep their cast under their notes, a trace of its simplifier recording 2894 refusals by `tryCastWorkerWrapper` with notes above the cast and none with the cast at the root. The exitification and the literals are posted as a comment on GHC [#21471](https://gitlab.haskell.org/ghc/ghc/-/work_items/21471), `docs/ghc-issue-g-changes-core-21471-comment.md` in horde-ad, and the cast, with a correction about the literals, as a second, `docs/ghc-issue-g-cast-ww-21471-comment.md` in horde-ad.

### A32. `-funfolding-use-threshold=0` leaves INLINE and wrapper unfoldings inlining, but stops the size-judged ones, so what they would have brought into the client, base's `eqInt` and friends among it, stays in the library's compiled code

**Rule.** The use threshold bounds only a size-judged decision: an `UnfIfGoodArgs` unfolding is inlined when its size plus any depth penalty less its discounts is at most the threshold (`small_enough`, `tryUnfolding`, [compiler/GHC/Core/Opt/Simplify/Inline.hs#L338][g222]), and it bounds worker/wrapper's choice to give a small function an always-inline unfolding (U07). An `UnfWhen` unfolding never consults it: INLINE ones, base's `eqInt` and `ltInt` being `INLINE [1]` ([libraries/ghc-internal/src/GHC/Internal/Classes.hs#L342][g223] and [#L563][g224]), worker/wrapper wrappers (A26) and constructor wrappers (A25). So at 0 a client still inlines `eqInt` at every call of it in the client's Core. What it stops is the inlining of size-judged unfoldings, an INLINABLE function's or its worker's (U04, U08), sized at the importer with the importer's threshold (U06): their bodies stay calls, and the small functions and constructor wrappers inside them, which the client would have inlined after inlining the body, are inlined only in the defining module's compiled copy. Counted in the client, those inlinings disappear.

**Seen.** Orthotope's benchmark built `-funfolding-use-threshold=0`, the second item numbered 1075 (2026-10-12) and the table above it: the inlinings lost against B0, the first pragma pass's base build, at the default threshold, by owner: base "eqInt 113, ltInt 61, leInt 55, build 48, foldr 30", vector "Storable basicLength 66", orthotope "RSlice's, RRuns', RFill's and OdoLevel's constructor wrappers" "($WRSlice 11, $WRRuns 6, $WRFill 6)", and "A constructor wrapper called out of line returns the `Route` built". The repro gives the mechanism for base's functions. The counted constructor wrappers were `Route`'s, `$WRSlice`, `$WRRuns` and `$WRFill`, lost in the benchmark's `Materialize` module, each allocating its `Route` when called out of line; the second repro shows how.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A32-use-threshold-zero`, variants `base` and `zero`, the flag on both modules, `-dinline-check $w`; `run` is `r 100000`; `measure.sh N`): INLINABLE helpers using `==`, `<` and list functions, called from a client.

```haskell
module Lib (R (..), mkR, eqR, ltCount, sumTo) where

-- A constructor with strict fields, which -O unpacks, so with a wrapper $WR.
data R = R !Int !Int

-- INLINABLE helpers, each small, each using a constructor wrapper or
-- one of base's small functions in its source-form unfolding.
{-# INLINABLE mkR #-}
mkR :: Int -> Int -> R
mkR a b = R (a + 1) b

{-# INLINABLE eqR #-}
eqR :: R -> R -> Bool
eqR (R a b) (R c d) = a == c && b == d

{-# INLINABLE ltCount #-}
ltCount :: [Int] -> Int -> Int
ltCount xs t = length (filter (< t) xs)

{-# INLINABLE sumTo #-}
sumTo :: Int -> Int
sumTo n = sum [x * x | x <- [1 .. n]]
```

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main, useR, useLt, useSum) where

import Lib
import System.Environment (getArgs)

-- A client calling each helper.
{-# NOINLINE useR #-}
useR :: Int -> Int -> Bool
useR a b = eqR (mkR a b) (mkR b a)

{-# NOINLINE useLt #-}
useLt :: [Int] -> Int
useLt xs = ltCount xs 5

{-# NOINLINE useSum #-}
useSum :: Int -> Int
useSum n = sumTo n + 1

main :: IO ()
main = do
  [what, repss] <- getArgs
  let reps = read repss :: Int
      xs = [1 .. 8] :: [Int]
      loop :: Int -> Int -> Int
      loop 0 !acc = acc
      loop r !acc = loop (r - 1) $ acc + case what of
        "r" -> if useR r (r + 1) then 1 else 0
        _ -> useLt (r : xs)
  print (loop reps 0)
```

`base`: the worker of `eqR` is inlined into `Main`, `Considering inlining: $weqR arg infos [NonTrivArg, TrivArg, NonTrivArg, TrivArg] interesting continuation BoringCtxt some_benefit True is exp: True is work-free: True guidance IF_ARGS [0 0 0 0] 120 10 case depth = 0 inline depth = 1 depth based penalty = 0 adjusted size = 50 ANSWER = YES` (whitespace collapsed), giving `$wuseR = \ ww ww1 -> case ==# (+# ww 1#) (+# ww1 1#) of { __DEFAULT -> False; 1# -> tagToEnum# (==# ww1 ww)`, and `Main.dump-inlinings` records `Inlining done: eqInt`, `Inlining done: ltInt` and `Inlining done: foldr`. `zero`: the same decision ends `adjusted size = 50 ANSWER = NO`, `Main` calls the workers, `$wuseR = \ ww ww1 -> $weqR (+# ww 1#) ww1 (+# ww1 1#) ww` and `$wuseLt = \ xs -> $wltCount xs lvl`, and none of the three is inlined in `Main`.

By `measure.sh 100000` (100000 and 200000 iterations differenced, twice, the same figures): `useR` 64.3 instructions at the default threshold and 67.3 at 0, `useLt` 294.3 and 388.3, the bytes equal (16.0 and 40.0 a call), each figure including the loop's own work.

A second repro (`~/r/horde-ad/dist-inlcat/cases/A32-threshold-zero-con-wrappers`, variants `base` and `zero`, `-dinline-check $W`): a sum type with strict fields and an INLINABLE function building it, a product as the first repro's `R`, and a client passing each to a NOINLINE consumer.

```haskell
module Lib (Route (..), R (..), mkRoute, mkR) where

data Route = RSlice !Int !Int | RRuns !Int !Int | RFill !Int

data R = R !Int !Int

{-# INLINABLE mkRoute #-}
mkRoute :: Bool -> Int -> Int -> Route
mkRoute c a b = if c then RSlice a b else RRuns b a

{-# INLINABLE mkR #-}
mkR :: Int -> Int -> R
mkR a b = R (a + 1) b
```

```haskell
module Main (main, useRoute, useR) where

import Lib
import System.Environment (getArgs)

{-# NOINLINE consumeRoute #-}
consumeRoute :: Route -> Int
consumeRoute (RSlice a b) = a + b
consumeRoute (RRuns a b) = a * b
consumeRoute (RFill a) = a

{-# NOINLINE consumeR #-}
consumeR :: R -> Int
consumeR (R a b) = a - b

{-# NOINLINE useRoute #-}
useRoute :: Int -> Int -> Int
useRoute a b = consumeRoute (mkRoute (a > 3) a b)

{-# NOINLINE useR #-}
useR :: Int -> Int -> Int
useR a b = consumeR (mkR a b)

main :: IO ()
main = do
  [n] <- map read <$> getArgs
  print (useRoute n (n + 1) + useR n 3)
```

`base`: `Lib.iface` has no `$wmkRoute`, `mkRoute` carrying `Unfolding: Core: StableSystem <3,TrueFalse>`, and `Main.dump-inlinings` has `Inlining done: $WRSlice` and `Inlining done: $WRRuns`, `$wuseRoute = \ ww ww1 -> case ># ww 3# of { __DEFAULT -> $wconsumeRoute (RRuns ww1 ww); 1# -> $wconsumeRoute (RSlice ww ww1) }`. `zero`: neither inlining, and `$wuseRoute = \ ww ww1 -> $wconsumeRoute ($wmkRoute (tagToEnum# (># ww 3#)) ww ww1)`.

**Reproduces small:** yes, for base's functions. Tried and not showing it: the comparisons written in the client itself, `eqInt` and `ltInt` inlined at both thresholds; and the helpers with no pragma, the client inlining `mkR`, `eqR`, `ltCount` and `sumTo` at both thresholds and no `eqInt` at either. The constructor wrappers, yes, by the second repro, with a function returning two constructors, which CPR does not cover: at the default threshold worker/wrapper leaves it unsplit with an always-inline unfolding holding `$WRSlice` and `$WRRuns` (U07), which the client inlines; at 0 it splits it, and the worker's INLINABLE unfolding holding them is size-judged and not inlined, the client calling `$wmkRoute`. In the first repro's client no `$WR` call appears at either threshold: `mkR`'s unfolding is always-inline at both, holding `$WR` at the default threshold and the worker constructor `R` at 0, and the `$WR` application it brings meets `eqR`'s `case`, which resolves it as a known constructor without inlining the wrapper (Note [exprIsConApp_maybe on data constructors with wrappers], [compiler/GHC/Core/SimpleOpt.hs#L1314][g183]).

### A33. INLINE on a `HasCallStack` function copies each `HasCallStack` call it makes into every caller as a static call-stack node; CSE merges the inlined copies that hold no stack, unless each shares a recursive group with what floats out of it

**Rule.** A call of a function with a `HasCallStack` constraint is solved by pushing the call site onto the caller's own stack (`EvCsPushCall`, Note [Overview of implicit CallStacks], [compiler/GHC/Tc/Types/Evidence.hs#L1114][g225], plan PUSH). Inside a `HasCallStack` function that stack is its lambda-bound argument, so each push for a call it makes is computed at run time: passed lazily, as here, it is a thunk allocated at every call. Inlined at a call site whose own stack is a constant (the site pushed onto `EmptyCallStack`), the inlined body's pushes become constant expressions too, and float to top level as static data: each call site gets its own node for every `HasCallStack` call in the body, chained to its own site node, where without the inlining it gets the site node alone. The nodes differ by their site, so they are never merged, and neither is code referring to them; what an inlined body contains that refers to no stack, here a local loop, floats out as identical copies, which CSE merges (on this tree; U18 gives the case in which identical copies holding a non-recursive `let` stayed apart, GHC [#27892](https://gitlab.haskell.org/ghc/ghc/-/work_items/27892), and the tree's patch for it), unless error branches float out of each copy: the second float-out puts the bindings floated out of a recursive top-level binding into that binding's own `Rec` group (`floatTopBind`, [compiler/GHC/Core/Opt/FloatOut.hs#L153][g226]; `do_pair`'s top-level case, [#L197][g227], Note [floatBind for top level]), and CSE identifies two recursive bindings only when each is a self-recursive binding standing alone (`cseBind`, [compiler/GHC/Core/Opt/CSE.hs#L400][g228]; Note [CSE for recursive bindings], [#L334][g229]): in a larger group ([#L422][g230]) a member's right-hand side is looked up as an ordinary expression, and a copy that names its group's own binders matches no other copy.

**Seen.** Orthotope's test suite, as recorded on 2026-10-10: "Inlined, the chain from each test call site through Dynamic.hs and DynamicG.hs to each `error` becomes static data in the test module. `PushCallStack` bindings rise from 524 to 598 with `transpose` and to 597 with `slice`, against 21 and 15 call sites." And of inlined `slice`: "becomes top-level workers `$wslc`, 5 new copies, 505 terms. The two I compared are identical once renamed, so CSE left duplicates". The copies held a non-recursive `let`: the Core that reading came from shows `$wslc3` inside `Rec {` under the header `-- RHS size: {terms: 101, types: 108, coercions: 0, joins: 0/1}`, the `let` being the lazy pair of `where (i, ns) = slc sl sh ts`; that build used this catalogue's compiler, with U18's patch, and what kept the copies apart is what the second repro shows: orthotope's `slc` has error branches. The comparison of two copies had renamed every `lvl` away, so it could not see copies that differ in the call-stack nodes they refer to.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A33-callstack-chains-static`, variants `inline` and `none` by `slc`'s pragma, set by `-DINL`, and `inlinenocse`, `inline` with `-fno-cse`; `run` is `100000`; `measure.sh N`): a `HasCallStack` operation calling a `HasCallStack` check twice, with a local loop, and a client calling it at four sites.

```haskell
{-# LANGUAGE CPP #-}
-- A checked operation over a checked helper, both HasCallStack, as
-- orthotope's Dynamic and DynamicG over error.
module Lib (slc, check) where

import GHC.Stack (HasCallStack)

{-# NOINLINE check #-}
check :: HasCallStack => Int -> Int -> Int
check n i = if i < 0 || i >= n then error ("index " ++ show i) else i

-- INLINE (variant inline) or no pragma (none).
#if defined(INL)
{-# INLINE slc #-}
#endif
slc :: HasCallStack => Int -> Int -> Int -> [Int]
slc n i k = go (check n i) (check n (i + k - 1))
  where
    -- A local loop closed over nothing: each inlined copy can float to
    -- top level whole.
    go a b
      | a > b = []
      | otherwise = a : go (a + 1) b
```

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main, s1, s2, s3, s4) where

import Lib (slc)
import System.Environment (getArgs)

-- Four call sites.
{-# NOINLINE s1 #-}
{-# NOINLINE s2 #-}
{-# NOINLINE s3 #-}
{-# NOINLINE s4 #-}
s1, s2, s3, s4 :: Int -> Int
s1 i = sum (slc 10 i 2)
s2 i = sum (slc 10 i 3)
s3 i = sum (slc 20 i 2)
s4 i = sum (slc 20 i 3)

main :: IO ()
main = do
  [repss] <- getArgs
  let reps = read repss :: Int
      loop :: Int -> Int -> Int
      loop 0 !acc = acc
      loop r !acc = loop (r - 1) (acc + s1 (r `rem` 8))
  print (loop reps 0 + s2 1 + s3 2 + s4 3)
```

`inline`: each site's node, as `$dIP9 = PushCallStack $dIP1 $dIP8 EmptyCallStack`, and under it one node for each of `slc`'s two calls of `check`, located in `Lib` (`lvl6 = SrcLoc main14 lvl3 lvl5 17# 17# 17# 22#`), `lvl7 = PushCallStack lvl1 lvl6 $dIP9` and `lvl9 = PushCallStack lvl1 lvl8 $dIP9`, all top-level constants; the site's worker passes them, `$ws4 = \ ww -> case $wcheck (C:IP lvl9) 20# (+# 2# ww) of ww2 { __DEFAULT -> case $wcheck (C:IP lvl7) 20# ww of ww1 { __DEFAULT -> $wgo1 ($wgo (I# ww1) ww2) 0#` (whitespace collapsed); `Main`'s Tidy Core is `{terms: 482,`. `none`: the site's node alone, `$ws4 = \ ww -> $wgo1 ($wslc (C:IP $dIP9) 20# ww 3#) 0#`, no `lvl7 = PushCallStack`, `{terms: 332,`; `Lib`'s worker pushes at each call of `check`, lazily, `$wcheck (C:IP (case ip $dIP of wild1 { __DEFAULT -> PushCallStack slc9 slc8 wild1; FreezeCallStack ds1 -> wild1 }))`. The loops copied to the four sites, `go` from `slc` and `sum`'s own, are two bindings in `inline`, no `$wgo2`, and eight in `inlinenocse`, up to `$wgo7`.

By `measure.sh 100000` (100000 and 200000 calls of `s1` differenced, twice, the same figures; and `size` of `Main.o`): `inline` 232.9 instructions and 160.0 bytes a call, 3614 bytes of text and 2272 of data; `none` 260.9 and 208.0, 2781 and 1552; `inlinenocse` 232.9 and 160.0, 5177 and 4512. The 48 bytes a call more that `none` allocates are, by the Core, the two thunks of `Lib`'s pushes, three words each.

A second repro (`~/r/horde-ad/dist-inlcat/cases/A33-slc-copies`, variants `cs`; `nocs`, without `HasCallStack`, by `-DNOCS`; `noerr`, `nocs` with `slc` written without its error branches, by `-DNOERR`; all with `-ddump-cse`): orthotope's generic `slice` with its local recursive `slc`, INLINE under the wrapper's INLINE `slice`, as the Seen's probe had them, and a client slicing one array at five sites.

```haskell
{-# LANGUAGE CPP #-}
module Lib (T (..), A (..), slice) where

#if !defined(NOCS)
import GHC.Stack (HasCallStack)
#define HCS HasCallStack =>
#else
#define HCS
#endif

data T = T [Int] Int [Double]  -- strides, offset, values
data A = A [Int] T             -- shape, view

{-# INLINE gslice #-}
gslice :: HCS [(Int, Int)] -> A -> A
gslice asl (A ash (T ats ao v)) = A rsh (T ats o v)
  where (o, rsh) = slc asl ash ats
#if defined(NOERR)
        slc ((k,n):sl) (_:sh) (t:ts) = (i + k*t, n:ns) where (i, ns) = slc sl sh ts
        slc _ sh _ = (ao, sh)
#else
        slc ((k,n):sl) (s:sh) (t:ts) | k < 0 || k > s || n < 0 || n > s - k = error $ "slice: out of bounds: slice=" ++ show (k, n) ++ " size=" ++ show s
                                     | otherwise = (i + k*t, n:ns) where (i, ns) = slc sl sh ts
        slc (_:_) [] _ = error "slice: slice list too long"
        slc [] sh _ = (ao, sh)
        slc _ _ _ = error "slice: violated contract: not one stride per dimension"
#endif

{-# INLINE slice #-}
slice :: HCS [(Int, Int)] -> A -> A
slice ss = gslice ss
```

```haskell
module Main (main) where

import Lib

x :: A
x = A [4, 5] (T [5, 1] 0 [0 .. 19])

shape :: A -> [Int]
shape (A sh _) = sh

main :: IO ()
main = do
  print (shape (slice [(1, 2)] x))
  print (shape (slice [(0, 3), (1, 2)] x))
  print (shape (slice [(2, 2)] x))
  print (shape (slice [(1, 1), (0, 4)] x))
  print (shape (slice [(0, 4), (2, 3)] x))
```

In `nocs` each copy holds the `let`, `ds6 = case $wslc sl sh ts of { (# ww, ww1 #) -> (ww, ww1) } } in`, and at CSE it shares a `Rec` group with the error branches floated out of it, `Rec { lvl = : $fShowCallStack1 [] lvl = \ s x n -> error` (whitespace collapsed), so the copies stay apart, `$wslc4` among them in the final Core, as in `cs`. In `noerr` each copy is a `Rec` of one binding, and CSE merges the five, `let` and all, `$wslc = $wslc` four times in its output, no `$wslc1` left.

**Reproduces small:** yes, the chains, and the duplicates by the second repro: the first repro's copies have no error branch, and CSE merges them.

### A34. A check that fails with `error` makes its function strict in what only the other branch uses; called through a worker/wrapper split, the function forces that first, and inlined whole it checks first, so inlining changes which error a caller gets

**Rule.** A branch that calls `error` is a dead end ([compiler/GHC/Types/Demand.hs#L1597][g231], Note [Dead ends]), whose demand type is `botDmdType` ([Demand.hs#L1950][g232]), the bottom demand on every free variable (`botDmdEnv`, [Demand.hs#L1848][g233]); joined with the other branch, it leaves strict an argument that only the other branch uses. `error` throws with `raise#` ([libraries/ghc-internal/src/GHC/Internal/Err.hs#L44][g234]), whose exceptions GHC treats as imprecise, with the divergence `botDiv` rather than the precise `exnDiv` ([compiler/GHC/Builtin/primops.txt.pp#L2841][g235], `RaiseOp`; [Demand.hs#L1610][g236], Note [Precise exceptions and strictness analysis]), so GHC may evaluate that argument before the check. Worker/wrapper does so wherever it splits the function, a NOINLINE one (A24) and a client's specialisation of an INLINABLE one included: the wrapper takes the argument apart before calling the worker that holds the check (E13, A26); and once the wrapper is inlined at a call whose argument is `undefined`, the call is `case undefined of ...`, which the simplifier folds to `undefined`. Inlined whole, as with INLINE, the function's Core keeps the check in front, the argument used only past it. So a test that expects the check's error from a function given an undefined array gets it where the function is inlined whole, and not where a wrapper forces the array first.

**Seen.** Orthotope's test suite, as recorded on 2026-10-11: a test "expecting the shape check's \"Shape\" error and getting `Prelude.undefined`", with the explanation, marked there not verified, "inlined, the shape check runs before the array is forced. A specialised wrapper that isn't inlined can be strict in its array argument and force the `undefined` first". Orthotope's commit "Note how GHC orders failures around the Shape checks", the note at `natT` in `Data/Array/Internal/Shape.hs`: with ShapedG's `index` INLINABLE, an undefined array was forced before `index`'s check; `GHC.Exts.lazy` on the array, or `pseq`, fixed the order but blocked simplification.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/A34-inlined-check-changes-error`, variants `inline`, `total` INLINE by `-DINL`; `noinline`, NOINLINE; `spec`, `total` overloaded and INLINABLE by `-DSPEC`, so that `Main` calls its own specialisation, with `-ddump-spec -ddump-worker-wrapper`; `speclit`, `spec` with a small body by `-DSMALL` and the shape a literal by `-DLIT`; `run` holds the wrong shape, 9, passed at run time so that the check is not folded): a function with a shape check in front of its use of the array, called with a wrong shape and `undefined` for the array.

```haskell
{-# LANGUAGE CPP #-}
module Lib (Arr (..), total) where

-- An array: its shape and its elements.
data Arr = Arr ![Int] [Double]

-- The shape check comes first in the source; the array is used only after
-- it.  INL inlines it at the caller; SPEC makes it overloaded and INLINABLE,
-- so the caller calls its own specialisation; otherwise NOINLINE.  SMALL
-- gives it a small body.
#if defined(SPEC)
total :: (Eq i, Num i) => [i] -> Arr -> Double
{-# INLINABLE total #-}
#else
total :: [Int] -> Arr -> Double
#if defined(INL)
{-# INLINE total #-}
#else
{-# NOINLINE total #-}
#endif
#endif
total sh a
  | sh /= [2, 3] = error "Shape"
#if defined(SMALL)
  | otherwise = case a of Arr _ xs -> sum xs
#else
  | otherwise = case a of
      Arr sh' xs -> sum (zipWith (*) xs (cycle [1, 2, 3]))
                    + fromIntegral (product sh') + fromIntegral (length sh)
#endif
```

```haskell
{-# LANGUAGE CPP #-}
module Main (main) where
import Control.Exception
import Lib
import System.Environment (getArgs)

main :: IO ()
main = do
  -- As the test: a wrong shape, read from the command line so that it is
  -- not folded, and an array that is never meant to be read.
  [s] <- getArgs
#if defined(LIT)
  -- The shape a literal instead.
  r <- try (evaluate (total [9] undefined))
#else
  r <- try (evaluate (total [read s] undefined))
#endif
  case r of
    Left (ErrorCall msg) -> putStrLn ("error: " ++ takeWhile (/= '\n') msg)
    Right x -> print x
```

`inline`, `Main.dump-simpl`: the check, the list equality, is scrutinised first, and `undefined` sits in its passing branch:

```
                        case seq#
                               (case $fEqList_$s$c==
                                       (: (case $w$sreadNumber2
```

```
                                of {
                                  False -> error (C:IP total11) main15;
                                  True -> case undefined (C:IP main5) of {}
                                })
```

`noinline`, `Lib.dump-simpl`: the wrapper takes the array apart before the worker checks the shape; in `Main.dump-simpl` the evaluated call is then `undefined`:

```
total
  = \ sh a ->
      case a of { Arr ww ww1 ->
      case $wtotal sh ww ww1 of ww2 { __DEFAULT -> D# ww2 }
      }
```

```
main6 = undefined (C:IP lvl3)
```

`spec`, `Main.dump-worker-wrapper`: the client's specialisation split the same way, and `Main.dump-simpl` the same fold:

```
$stotal
  = \ sh a ->
      case case a of wild { Arr ww ww -> $w$stotal sh ww ww } of ww
      { __DEFAULT ->
      D# ww
      }
```

```
main6 = undefined (C:IP lvl19)
```

`speclit`, `Main.dump-simpl`: the specialisation inlined whole, its check first:

```
main6
  = case $fEqList_$c== $fEqInteger lvl16 $stotal2 of {
      False -> $stotal1;
      True -> case lvl14 of {}
    }
```

Run, `inline` and `speclit` print `error: Shape`, `noinline` and `spec` `error: Prelude.undefined`.

**Reproduces small:** yes. Under the same pragma, `speclit`'s small body is inlined whole and `spec`'s is not: which error is seen follows whether the call ends in the function's whole body or in a wrapper, not the pragma alone.

## 2. Eta-expansion and saturation

How eta-expansion, eta-reduction and saturation change where a binding inlines: the binding itself, and the bindings it calls or that call it; and, in E15 to E19, how floating and tag inference meet them.

### E01. An INLINE function is inlined only at a call giving every value argument its left-hand side names

**Rule.** The saturation count of an INLINE unfolding is the number of patterns on the definition's left-hand side, plus one for each dictionary argument and less one for each required type argument; it is not the arity of the type nor the arity GHC later gives the binding. A call with fewer value arguments is never inlined, whatever its context, except by `inline` (A13): the unfolding is made with `ug_unsat_ok = needSaturated`, and `tryUnfolding` requires `n_val_args >= uf_arity`. The count is set from the match group by `add_inl_arity` ([compiler/GHC/Tc/Gen/Sig.hs#L615][g237], applied to INLINE alone, not INLINABLE, from `lhsBindVisArity` at [#L622][g238]), turned into a value-argument count by `findSatArity` ([compiler/GHC/HsToCore/Binds.hs#L474][g239]), and passed to `mkInlineUnfoldingWithArity` by `makeCorePair` ([compiler/GHC/HsToCore/Binds.hs#L441][g240]), which sets `ug_unsat_ok = needSaturated` ([compiler/GHC/Core/Unfold/Make.hs#L165][g241]); the test is `enough_args` in `tryUnfolding` ([compiler/GHC/Core/Opt/Simplify/Inline.hs#L318][g27]). The interface records both numbers: `Arity:` is the binding's arity, `Inline: (sat-args=N)` and the `<N,unsat_ok boring_ok>` after `StableUser` are the unfolding's count and flags (`IfWhen`, [compiler/GHC/Iface/Syntax.hs#L495][g242]). So a function whose left-hand side names fewer arguments is inlined at more call sites, and naming one more argument stops its inlining at every call one argument short.

**Seen.** Orthotope's INLINE wrappers, point-free, inlined at the benchmark's partial calls; expanded to name all their arguments, they were not, and the benchmark's `reduce (+) 0` then boxed every element. `docs/perf-checklist.md` I1: a partly applied `S.zipWithA (+)` left `$szipWithA` copies in the client; its `map toVector as` is E02's, and `rerank2` saturated in a lambda E07's.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/E01-inline-needs-lhs-arity`, variants `base` checking `reduce3`, `r2` checking `reduce2`): the same INLINE fold with three patterns or two, each applied to two arguments under `map`, and the three-pattern one also under a lambda that saturates it.

```haskell
{-# LANGUAGE BangPatterns #-}
module M where

{-# INLINE reduce3 #-}
reduce3 :: (Int -> Int -> Int) -> Int -> [Int] -> Int
reduce3 f z xs = go z xs
  where go !acc [] = acc
        go !acc (y : ys) = go (f acc y) ys

{-# INLINE reduce2 #-}
reduce2 :: (Int -> Int -> Int) -> Int -> [Int] -> Int
reduce2 f z = \xs -> go z xs
  where go !acc [] = acc
        go !acc (y : ys) = go (f acc y) ys

part3, sat3, part2 :: [[Int]] -> [Int]
part3 xss = map (reduce3 (+) 0) xss
sat3 xss = map (\xs -> reduce3 (+) 0 xs) xss
part2 xss = map (reduce2 (+) 0) xss
```

The interface gives both functions `Arity: 3`, and different counts:

    reduce2: Arity: 3, ... Inline: (sat-args=2), Unfolding: Core: StableUser <2,FalseFalse>
    reduce3: Arity: 3, ... Inline: (sat-args=3), Unfolding: Core: StableUser <3,FalseFalse>

At `part3`'s call, `-dinline-check reduce3`:

    Considering inlining: reduce3
      arg infos [NonTrivArg, ValueArg]
      interesting continuation RuleArgCtxt
      some_benefit True
      ...
      guidance ALWAYS_IF(arity=3,unsat_ok=False,boring_ok=False)
      ...
      ANSWER = NO

and at `part2`'s, `-dinline-check reduce2`, the same but `guidance ALWAYS_IF(arity=2,unsat_ok=False,boring_ok=False)` and `ANSWER = YES`. The Core: `part3` passes the out-of-line `reduce3`, whose loop calls the unknown `f` on boxed `Int`s, while `part2` and the saturated `sat3` (CSE makes it `part2`) get an unboxed loop:

    part5 = reduce3 $fNumInt_$c+ part2_z
    part3 = \ xss -> map part5 xss
          (in reduce3)  : y ys -> jump go (f acc1 y) ys
    part1 = \ eta -> case $wgo 0# eta of ww { __DEFAULT -> I# ww }
    part2 = \ xss -> map part1 xss
          (in $wgo)     : y ys -> case y of { I# y1 -> $wgo (+# ww y1) ys }
    sat3 = part2

**Reproduces small:** yes.

### E02. A point-free INLINE definition counts only its dictionaries, so it is inlined where it is passed unapplied

**Rule.** The saturation count of E01 counts the left-hand side's patterns, so a definition with none, `f = ...`, gets a count equal to its number of dictionary arguments: `findSatArity` adds one per invisible runtime binder to the visible count ([compiler/GHC/HsToCore/Binds.hs#L487][g243] and [#L495][g244]). An overloaded point-free INLINE function therefore counts as saturated once its dictionary is applied, which every occurrence at a known type is, so it is inlined where it is passed unapplied (under `map`, as an argument) --- given `some_benefit`, which a dictionary argument (`ValueArg`) or a `RuleArgCtxt` supplies ([compiler/GHC/Core/Opt/Simplify/Inline.hs#L402][g245], [#L414][g246]). A monomorphic one has count 0, and `mkInlineUnfoldingWithArity` then sets `boring_ok` regardless of size ([compiler/GHC/Core/Unfold/Make.hs#L169][g11], Note [Honour INLINE on 0-ary bindings] at [#L267][g42]), so it is inlined at every occurrence, a lone variable included. Naming the argument raises the count by one, and then the unapplied occurrence is not inlined (E01); where the function is overloaded, the specialiser makes a copy for the call's type, which inherits the INLINE pragma with the dictionary dropped from its count and is itself left unapplied, as here `sumEta_$ssumEta`.

**Seen.** `docs/perf-checklist.md` I1: `map toVector as` in `concatOuter` and `ravel` left `$stoVector` copies in the client, the shape `useEta` shows; and orthotope's point-free INLINE wrappers, inlined at partial calls where named ones were not (E01).

**Repro** (`~/r/horde-ad/dist-inlcat/cases/E02-inline-point-free-counts-dicts`, variants `base`, `eta` and `int`, each checking one of the three functions, by `-dinline-check sumPF`, `sumEta` and `sumIntPF`): one INLINE sum written point-free and overloaded, naming its list and overloaded, and point-free at `Int`, each passed unapplied to `map`.

```haskell
{-# LANGUAGE BangPatterns #-}
module M where

{-# INLINE sumPF #-}
sumPF :: Num a => [a] -> a
sumPF = go 0
  where go !acc [] = acc
        go !acc (x : xs) = go (acc + x) xs

{-# INLINE sumEta #-}
sumEta :: Num a => [a] -> a
sumEta ys = go 0 ys
  where go !acc [] = acc
        go !acc (x : xs) = go (acc + x) xs

{-# INLINE sumIntPF #-}
sumIntPF :: [Int] -> Int
sumIntPF = go 0
  where go !acc [] = acc
        go !acc (x : xs) = go (acc + x) xs

usePF, useEta, useIntPF :: [[Int]] -> [Int]
usePF xss = map sumPF xss
useEta xss = map sumEta xss
useIntPF xss = map sumIntPF xss
```

The interface's unfolding counts, `<count,unsat_ok boring_ok>`: `sumEta` `Inline: (sat-args=1), Unfolding: Core: StableUser <2,FalseFalse>`; `sumPF` `Inline: (sat-args=0), Unfolding: Core: StableUser <1,FalseFalse>`; `sumIntPF` `Inline: (sat-args=0), Unfolding: Core: StableUser <0,FalseTrue>`; and the specialised copy `sumEta_$ssumEta` `Arity: 1, Strictness: <1L>, CPR: 1, Inline: (sat-args=1), Unfolding: Core: StableUser <1,FalseFalse>`. The decisions at the three `map` calls, each condensed to one line:

    Considering inlining: sumPF     arg infos [ValueArg]  RuleArgCtxt  guidance ALWAYS_IF(arity=1,unsat_ok=False,boring_ok=False)  ANSWER = YES
    Considering inlining: sumEta    arg infos [ValueArg]  RuleArgCtxt  guidance ALWAYS_IF(arity=2,unsat_ok=False,boring_ok=False)  ANSWER = NO
    Considering inlining: sumIntPF  arg infos []          RuleArgCtxt  guidance ALWAYS_IF(arity=0,unsat_ok=False,boring_ok=True)   ANSWER = YES

and the Core (CSE makes `usePF` the same as `useIntPF`):

    useIntPF1 = \ eta -> case $wgo 0# eta of ww { __DEFAULT -> I# ww }
    useIntPF = \ xss -> map useIntPF1 xss
    useEta = \ xss -> map sumEta_$ssumEta xss
    usePF = useIntPF
    sumEta_$ssumEta = \ eta -> case $wgo 0# eta of ww { __DEFAULT -> I# ww }

In this module the two end alike, `map` calling a top-level function of the same body in each (the inlined one floated out as `useIntPF1`); what the rule decides is whether the body reaches the consumer's simplification at all, which matters where the consumer could use it, as orthotope's did.

**Reproduces small:** yes.

### E03. An over-saturated INLINE call is inlined whatever its context, so a pragma-free alias of an INLINE function whose left-hand side names fewer arguments grows to its body, and one whose left-hand side names as many is eta-reduced to it (E04)

**Rule.** An INLINE unfolding is taken at a call with enough arguments when `boring_ok || some_benefit` (A01), and `calc_some_benefit` counts a call with more value arguments than the unfolding's count as interesting whatever its context (`interesting_call`, `| over_saturated = True`, [compiler/GHC/Core/Opt/Simplify/Inline.hs#L408][g247]). So for a pragma-free alias `fmap g x = mapA g x` of an INLINE `mapA` whose body is not tiny (`boring_ok` False, A01): where `mapA`'s left-hand side names one argument, the alias's call over-saturates it and `mapA` is inlined, the alias growing to `mapA`'s body; a pragma-free binding, it is then split by worker/wrapper, the wrapper getting a stable unfolding (`mkWrapperUnfolding`, [compiler/GHC/Core/Unfold/Make.hs#L116][g184]) and the worker an ordinary one, which, without an exposure flag, is exposed only below `-funfolding-creation-threshold` (`calcUnfoldingGuidance` gives `UnfNever` above it, and `addExternal` exposes an `UnfNever` unfolding only under `-fexpose-all-unfoldings`, or `-fexpose-overloaded-unfoldings` for an overloaded binding, [compiler/GHC/Iface/Tidy.hs#L745][g248]). Where `mapA` names both arguments, the call is exactly saturated with trivial arguments in a boring context and is not inlined; `rebuildLam` then eta-reduces the alias's right-hand side ([compiler/GHC/Core/Opt/Simplify/Utils.hs#L2041][g249]), since `mapA`'s arity is at least the two lambdas removed (`tryEtaReduce`, `is_eta_reduction_sound`, [compiler/GHC/Core/Opt/Arity.hs#L2771][g250], the test `fun_arity fun >= incoming_arity` at [#L2781][g251]), and the alias is `mapA` itself. A client's call of the alias then becomes either a call of the worker, out of line, or a call of the INLINE `mapA`, which the client's arguments may make worth inlining (here `(+ 1)`, a `ValueArg`). So the eta form of one binding decides the inlining of another.

**Seen.** Read from orthotope's interfaces on 2026-10-14: with Shaped `mapA` naming one argument, `fmap a b = mapA a b` became `$w$cfmap` with no unfolding, called out of line; naming two, `fmap` was eta-reduced to `mapA`. And naming Shaped `mapA`'s array saved boxed `liftA2` 176 to 640 bytes a call forced at the small size, 48 an element at the large (orthotope's comment at Shaped `mapA`: `liftA2`'s default `fmap f x <*> y` over-saturated it, growing `liftA2` past what a client inlines).

**Repro** (`~/r/horde-ad/dist-inlcat/cases/E03-alias-oversaturates-inline`, variants `base` and `m2`, `-dinline-check mapA1` and `-dinline-check mapA2`, and `thr`, `base` with `-funfolding-creation-threshold=5000`): two array types with the same INLINE map, its left-hand side naming one argument or two, each with a `Functor` instance whose `fmap` names both, and a client applying `fmap (+ 1)`.

```haskell
module M where

data Arr1 a = Arr1 !Int [a]
data Arr2 a = Arr2 !Int [a]

{-# INLINE mapA1 #-}
mapA1 :: (a -> b) -> Arr1 a -> Arr1 b
mapA1 f = \a -> case a of
  Arr1 n xs -> case n of
    0 -> Arr1 0 []
    1 -> Arr1 1 (map f xs)
    2 -> Arr1 2 (map f (reverse xs))
    3 -> Arr1 3 (map f (drop 1 xs) ++ map f (take 1 xs))
    4 -> Arr1 4 (map f (drop 2 xs) ++ map f (take 2 xs))
    _ -> Arr1 n (map f (drop 3 xs) ++ map f (take 3 xs))

{-# INLINE mapA2 #-}
mapA2 :: (a -> b) -> Arr2 a -> Arr2 b
mapA2 f a = case a of
  Arr2 n xs -> case n of
    ... -- as mapA1, with Arr2

instance Functor Arr1 where
  fmap g x = mapA1 g x

instance Functor Arr2 where
  fmap g x = mapA2 g x
```

```haskell
module C where
import M

incr1 :: Arr1 Int -> Arr1 Int
incr1 a = fmap (+ 1) a

incr2 :: Arr2 Int -> Arr2 Int
incr2 a = fmap (+ 1) a
```

In `M`, at the two `fmap`s:

    Considering inlining: mapA1
      arg infos [TrivArg, TrivArg]
      interesting continuation BoringCtxt
      some_benefit True
      ...
      guidance ALWAYS_IF(arity=1,unsat_ok=False,boring_ok=False)
      ...
      ANSWER = YES
    Considering inlining: mapA2
      arg infos [TrivArg, TrivArg]
      interesting continuation BoringCtxt
      some_benefit False
      ...
      guidance ALWAYS_IF(arity=2,unsat_ok=False,boring_ok=False)
      ...
      ANSWER = NO

and the dictionaries:

    $fFunctorArr1 = C:Functor $fFunctorArr1_$cfmap $fFunctorArr1_$c<$
    $fFunctorArr2 = C:Functor mapA2 $fFunctorArr2_$c<$

`$fFunctorArr1_$cfmap` is a wrapper, `Strictness: <L><1!P(1L,L)>, CPR: 1, Inline: [2], Unfolding: Core: StableSystem <2,TrueFalse>`, and its worker `$w$cfmap` has `LambdaFormInfo: LFReEntrant 3, Arity: 3, Strictness: <L><1L><L>, Inline: [2]]`, no unfolding; under `thr` the same entry ends `Inline: [2], Unfolding: Core: <vanilla>`. In `C`, `incr1` calls the worker in every variant:

    case $w$cfmap incr4 ww ww1 of { (# ww2, ww3 #) -> Arr1 ww2 ww3 }

while `mapA2` is inlined (`arg infos [ValueArg, TrivArg]`, `inline depth = 2`, `ANSWER = YES`) and `incr2` gets its own worker, `case $wincr2 ww ww1 of { (# ww2, ww3 #) -> Arr2 ww2 ww3 }`, holding the fused loops.

**Reproduces small:** yes; the worker's missing unfolding needs a body past the default creation threshold, which the six-way case gives.

### E04. Eta-reduction turns `\x y -> f x y` into `f` only when `f` is a variable whose arity, or the calling context, covers the lambdas; it reaches INLINE unfoldings but leaves their count

**Rule.** When the simplifier rebuilds a lambda, `rebuildLam` tries eta-reduction first, under `-fdo-eta-reduction` ([compiler/GHC/Core/Opt/Simplify/Utils.hs#L2040][g252]), on at every optimisation level ([compiler/GHC/Driver/DynFlags.hs#L1303][g253]). `tryEtaReduce` ([compiler/GHC/Core/Opt/Arity.hs#L2702][g254]) succeeds only if, after stripping the lambdas' arguments, what is left is a variable, possibly applied to types (`ok_fun`, [#L2763][g255]): it never leaves a partial application, so `\x -> g 3 x` stays a lambda (Note [Do not eta reduce PAPs], [#L2553][g256]). It is sound, in `is_eta_reduction_sound` ([#L2771][g250]), when the variable's arity is at least the number of value lambdas removed (`fun_arity fun >= incoming_arity`), or when the context is known to call the lambda with that many arguments, taken from the demand put on it (`all_calls_with_arity`, Note [Eta reduction based on evaluation context] at [#L2613][g257]), or when only type and dictionary lambdas are removed; never for the binding's own recursive group, nor for a join point, a function with no binding or a strict worker (`cantEtaReduceFun`, [compiler/GHC/Core/Utils.hs#L2380][g258]). Nothing in it depends on the variable's pragma, and its unfolding matters only by saying it is evaluated, which lets a variable of arity 0 count as arity 1 (`fun_arity`, [compiler/GHC/Core/Opt/Arity.hs#L2789][g259], criterion (E)): a NOINLINE `f` is reduced to like any other. Stable unfoldings are simplified in a mode that switches eta-expansion off but inherits eta-reduction (`updModeForStableUnfoldings`, [compiler/GHC/Core/Opt/Simplify/Utils.hs#L1207][g260]), so an INLINE alias's template is reduced too, to a bare variable; but its count stays its left-hand side's, as `simplStableUnfolding` keeps an `UnfWhen` guidance and refreshes only `boring_ok` ([compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4920][g261]). The effect on inlining: a reduced pragma-free alias is a trivial binding, inlined as the function at every occurrence however applied; an INLINE alias reduced to the same variable is still inlined only at calls with all its left-hand side's arguments (E01), so with the pragma it is inlined at fewer sites than without; and an alias that cannot be reduced keeps its own unfolding, with its own count.

**Seen.** Orthotope's `fmap a b = mapA a b`, reduced to `mapA` where `mapA`'s left-hand side named two arguments (E03).

**Repro** (`~/r/horde-ad/dist-inlcat/cases/E04-eta-reduction-conditions`, variants `base`, `-dinline-check inlineG`, and `noreduce`, with `-fno-do-eta-reduction`): one module of aliases of NOINLINE functions, each placed so that one condition decides, and a client applying the pragma-free alias and the INLINE alias to one argument each.

```haskell
module M where

-- g and g2 are lazy and return a list, so worker/wrapper leaves them alone.
{-# NOINLINE g #-}
g :: Int -> Int -> [Int]
g x y = [x, y]

{-# NOINLINE g2 #-}
g2 :: Int -> Int -> [Int]
g2 x y = [y, x]

-- k has arity 1: its second lambda sits behind an expensive let.
{-# NOINLINE k #-}
k :: Int -> Int -> Int
k x = let t = expensive x in \y -> t + y

{-# NOINLINE expensive #-}
expensive :: Int -> Int
expensive x = sum [1 .. x]

-- h calls its argument with two arguments, strictly.
{-# NOINLINE h #-}
h :: (Int -> Int -> Int) -> Int
h c = c 1 2 + c 3 4

aliasG :: Int -> Int -> [Int]
aliasG x y = g x y            -- head g, arity 2

papG :: Int -> [Int]
papG x = g 3 x                -- would reduce to a PAP, g 3

aliasK :: Int -> Int -> Int
aliasK x y = k x y            -- head k, arity 1 < 2

strictK :: Int
strictK = h (\x y -> k x y)   -- k in a context calling it with two

lazyK :: Maybe (Int -> Int -> Int)
lazyK = Just (\x y -> k x y)  -- k in a lazy context

{-# INLINE inlineG #-}
inlineG :: Int -> Int -> [Int]
inlineG x y = g2 x y          -- an INLINE alias
```

```haskell
module C where
import M

c1, c2 :: [Int] -> [[Int]]
c1 xs = map (aliasG 1) xs
c2 xs = map (inlineG 1) xs
```

In `M` by default (`lazyK`'s lambda, not reduced, is shared with `aliasK` by CSE):

    aliasG = g
    papG = \ x -> g papG1 x
    aliasK = \ x y -> k x y
    strictK = case $wh k of ww { __DEFAULT -> I# ww }
    lazyK = Just aliasK
    inlineG = g2

and `inlineG`'s interface entry `Inline: (sat-args=2), Unfolding: Core: StableUser <2,FalseTrue> g2]`. Under `noreduce`: `aliasG = \ x y -> g x y`, `inlineG = \ x y -> g2 x y`, `strictK = case $wh aliasK of ww { __DEFAULT -> I# ww }`. In `C` by default `c4 = g c5` and `c6 = inlineG c5`, the second after

    Considering inlining: inlineG
      arg infos [ValueArg]
      interesting continuation RuleArgCtxt
      ...
      guidance ALWAYS_IF(arity=2,unsat_ok=False,boring_ok=True)
      ...
      ANSWER = NO

and under `noreduce` the unreduced pragma-free alias is inlined unsaturated as a small function (A02), `c4 = \ y -> g c1_x y`, the INLINE one still not, `c5 = inlineG c1_x`.

**Reproduces small:** yes.

### E05. A partial application on a right-hand side is not eta-expanded, so the INLINE function it names is inlined at its callers rather than in the definition

**Rule.** `tryEtaExpandRhs` expands a binding's right-hand side only if `wantEtaExpansion` holds ([compiler/GHC/Core/Opt/Simplify/Utils.hs#L2192][g262]), which is False for a variable, a literal, and any application whose head, under type lambdas, casts and ticks, is a variable: a partial application `f = g a` keeps no lambda (Note [Which RHSs do we eta-expand?], [#L2228][g263], and Note [Do not eta-expand PAPs], [#L2247][g264], which gives as one reason that expanding `f = g d` "might in turn make g inline (if it has an inline pragma)", [#L2267][g265]). The arity analysis still runs and its result is recorded as the binding's arity (`addLetBndrInfo`, [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L1005][g266]), so the interface says `Arity: 1` over an unfolding with no lambda. That unfolding, `g a`, has no value binders, so its guidance is `IF_ARGS []` (`calcUnfoldingGuidance`, [compiler/GHC/Core/Unfold.hs#L362][g267]; it is not trivial, so `uncondInline` fails, [#L505][g268]), and every call with an argument over-saturates it, which `calc_some_benefit` counts as interesting in any context ([compiler/GHC/Core/Opt/Simplify/Inline.hs#L408][g247]). So: written point-free, `f` stays a small partial application, and the INLINE `g` (needing both arguments, E01) is not inlined into it but at its callers: a call `f x` over-saturates `f`'s small unfolding, which is inlined, giving `g a x`, where `g` is saturated and can be inlined; written `f x = g a x`, `g` is inlined into `f`, which grows, may be split by worker/wrapper, and is then called by the callers, out of line if too big. A point-free composition is not a partial application of the INLINE function: `negComp = mapA negate . mapA abs`, tried beside this repro, became a lambda with `mapA` inlined into it and was split by worker/wrapper like the named form.

**Seen.** Eta-expanding orthotope's point-free wrappers without a pragma changed the benchmark's Core, `OpsRanked` and `OpsDynamic` 1.1% fewer terms and `OpsShaped` 0.4% more; expanding about five hundred point-free functions, most of them with a pragma, moved bytes only at boxed Dynamic and Ranked `toVector`, which, named, took 32 bytes a call less when forced at a small dense view (N).

**Repro** (`~/r/horde-ad/dist-inlcat/cases/E05-pap-rhs-not-eta-expanded`, variants `base`, `-dinline-check negPF`, and `eta`, `-dinline-check negEta`): one pragma-free function over an INLINE map, point-free or naming its array, and a client taking each result apart.

```haskell
module M where

data Arr = Arr !Int [Int]

{-# INLINE mapA #-}
mapA :: (Int -> Int) -> Arr -> Arr
mapA f a = case a of
  Arr n xs -> case n of
    0 -> Arr 0 []
    1 -> Arr 1 (map f xs)
    2 -> Arr 2 (map f (reverse xs))
    3 -> Arr 3 (map f (drop 1 xs) ++ map f (take 1 xs))
    4 -> Arr 4 (map f (drop 2 xs) ++ map f (take 2 xs))
    _ -> Arr n (map f (drop 3 xs) ++ map f (take 3 xs))

negPF :: Arr -> Arr
negPF = mapA negate

negEta :: Arr -> Arr
negEta a = mapA negate a
```

```haskell
module C where
import M

c1, c2 :: Arr -> [Int]
c1 a = case negPF a of Arr _ ys -> ys
c2 a = case negEta a of Arr _ ys -> ys
```

In `M`, `negPF = mapA $fNumInt_$cnegate`, with interface entry `LambdaFormInfo: LFReEntrant 1, Arity: 1, Strictness: <1!P(1L,L)>, CPR: 1, Unfolding: Core: <vanilla> mapA GHC.Internal.Num.$fNumInt_$cnegate]`; `mapA` is inlined into `negEta` alone (`Inlining done: mapA`), which worker/wrapper then splits (`Unfolding: Core: StableSystem <1,TrueFalse>`, the wrapper). In `C`:

    Considering inlining: negPF
      arg infos [TrivArg]
      interesting continuation BoringCtxt
      some_benefit True
      is exp: True
      is work-free: True
      guidance IF_ARGS [] 20 60
      case depth = 0
      inline depth = 1
      depth based penalty = 0
      adjusted size = -50
      ANSWER = YES

followed by `Inlining done: mapA`, so `c1 = \ a -> case a of { Arr ww ww1 -> $wc1 ww ww1 }` holds `mapA`'s loops, while `c2` calls the worker, `case $wnegEta ww ww1 of { (# _, ww3 #) -> ww3 }`.

**Reproduces small:** yes, the mechanism; no cost is measured here, and which form is cheaper depends on the program (orthotope's moved bytes at a few bindings only).

### E06. A stable unfolding's template is eta-expanded to the binding's arity: an INLINE one keeps its count but gains the callee's body, an INLINABLE one gets a new count

**Rule.** The desugarer makes an INLINE unfolding from the right-hand side as written, while eta-expanding the right-hand side itself to the saturation count (`makeCorePair`, [compiler/GHC/HsToCore/Binds.hs#L466][g269] and [#L468][g270]). Each time the simplifier processes the binding, it simplifies the stable unfolding in a mode with eta-expansion off (`updModeForStableUnfoldings`, [compiler/GHC/Core/Opt/Simplify/Utils.hs#L1207][g260]) and afterwards eta-expands the result to the binding's own arity, the one arity analysis gave the right-hand side, if that is higher and `wantEtaExpansion` holds (`eta_expand` in `simplStableUnfolding`, [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4957][g271]; Note [Eta-expand stable unfoldings] at [#L4964][g272]). For an INLINE unfolding (`UnfWhen`) the guidance is kept, only `boring_ok` refreshed ([#L4920][g261]), so the count stays the left-hand side's; but the template now has the expanded lambdas, and at the next simplification a function it calls, now saturated in it, can be inlined into it. So a point-free INLINE alias `myMap = genMap` of an INLINE `genMap` that needs three arguments counts one (its dictionary, E02) and carries `genMap`'s body: at a call applying `myMap` to its dictionary and one more argument, `genMap`'s body is inlined, where the same call of `genMap` is not inlined (E01). The repro is the example of Note [Eta-expanding at let bindings], whose account of it HEAD contradicts (section 6, item 1). For an INLINABLE unfolding (`UnfIfGoodArgs`) the guidance is recomputed from the expanded template (`mkLetUnfolding`, [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4939][g273]), so its count follows the binding's arity, not the left-hand side's; an importer recomputes it again from the template in the interface (`IfNoGuidance`, [compiler/GHC/Iface/Syntax.hs#L494][g274]), which is already expanded.

**Seen.** Not in our record. Orthotope's Shaped `Functor` instance has this shape, `fmap = mapA` under `INLINE fmap` (orthotope's `Data/Array/Internal/Shaped.hs`, checkout at "Condense the account of unorderedRouteT's sort and merge"), unmeasured as such.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/E06-stable-unfolding-eta-expanded`, variants `base`, `-dinline-check genMap`; `pick`, `-dinline-check pick`; `ds`, `-O -ddump-ds -dsuppress-uniques -dsuppress-module-prefixes`, dumping the desugarer's output; `noeta`, with `-fno-do-lambda-eta-expansion`): the Note's example, with a client applying `myMap` and `genMap` to the function but not the list; and an INLINABLE function whose second lambda sits behind a `case`, applied in the client to one argument.

```haskell
module M where

class C a where
  op :: a -> Int

class C a => D a where
  op2 :: a -> Int

instance C Int where
  op x = x + 1

instance D Int where
  op2 x = x + 2

{-# INLINE genMap #-}
genMap :: C a => (Int -> Int) -> [a] -> [Int]
genMap f xs = map (\x -> f (op x)) xs

{-# INLINE myMap #-}
myMap :: D a => (Int -> Int) -> [a] -> [Int]
myMap = genMap

{-# INLINABLE pick #-}
pick :: Bool -> Int -> [Int]
pick b = case b of
  True -> \y -> [y, y + 1, y * 2, y - 3]
  False -> \y -> [y * 3, y - 1, y + 7, y]
```

```haskell
module C where
import M

viaMy, viaGen :: [[Int]] -> [[Int]]
viaMy xss = map (myMap negate) xss
viaGen xss = map (genMap negate) xss

viaPick :: [Int] -> [[Int]]
viaPick ys = map (pick True) ys
```

The desugarer gives `myMap` `Guidance=ALWAYS_IF(arity=1,unsat_ok=False,boring_ok=False) Tmpl= \ (@a) ($dD [Occ=Once1] :: D a) -> genMap @a ($p1D @a $dD)}]`; the interface has `LambdaFormInfo: LFReEntrant 3, Arity: 3, ... Inline: (sat-args=0), Unfolding: Core: StableUser <1,FalseFalse>` over a template of three lambdas ending

    GHC.Internal.Base.map @a @GHC.Internal.Types.Int (\ (x['GHC.Internal.Types.Many] :: a) -> eta (op @a $dC x)) eta1]

In the client, `genMap` given two of its three arguments is not inlined and is specialised instead, while `myMap` at the same call is inlined with `genMap`'s body (the decision condensed to one line):

    Considering inlining: genMap  arg infos [ValueArg, NonTrivArg]  RuleArgCtxt  guidance ALWAYS_IF(arity=3,unsat_ok=False,boring_ok=False)  ANSWER = NO
    viaMy1 = \ eta1 -> map viaMy2 eta1
    viaGen1 = $sgenMap $fNumInt_$cnegate

Under `noeta` the template keeps its one lambda, `Inline: (sat-args=0), Unfolding: Core: StableUser <1,FalseFalse> \ @a ($dD['GHC.Internal.Types.Many] :: D a) -> genMap @a ($p1D @a $dD)]`, and the client's two calls compile alike, `viaMy1 = $sgenMap $fNumInt_$cnegate` and `viaGen = viaMy`: the expansion is what carries `genMap`'s body.

`pick`'s desugared unfolding has `Guidance=IF_ARGS [330] 620 120`, one argument; its interface entry `LambdaFormInfo: LFReEntrant 2, Arity: 2, Strictness: <1L><L>, Inline:, Unfolding: Core: StableUser` carries a two-lambda template, and in the client `guidance IF_ARGS [233 120] 426 80`, two arguments, so `pick True` is an unsaturated call of it (here not inlined, being too big).

**Reproduces small:** yes; the desugarer's eta-expansion of the right-hand side is from the source.

### E07. A lambda that is not a right-hand side is eta-expanded only if it already has a value lambda, so `\z -> f a z` can saturate an INLINE `f` where `f a` cannot

**Rule.** When the simplifier rebuilds a lambda that is not the right-hand side of a binding, `rebuildLam`, after failing to eta-reduce it, eta-expands it to the arity of its body (`exprEtaExpandArity`), provided eta-expansion is on and the lambda already binds at least one value variable ([compiler/GHC/Core/Opt/Simplify/Utils.hs#L2046][g275] to [#L2049][g276]; Note [Eta expanding lambdas] at [#L2085][g277]). A partial application passed as an argument is not a lambda and is not expanded (nor is one on a right-hand side, E05). So `apply2 (f a)` leaves `f` applied to one argument, while `apply2 (\z -> f a z)`, with `f` of arity 3, becomes `apply2 (\z eta -> f a z eta)`, in which `f` is saturated and an INLINE `f` is inlined (E01). Eta-reduction does not undo it, the result being a lambda over a body that is not a bare call. `-fno-do-lambda-eta-expansion` switches the expansion off here as on right-hand sides (`sm_eta_expand`, [compiler/GHC/Core/Opt/Simplify/Env.hs#L279][g278]).

**Seen.** `docs/perf-checklist.md` I1: `rerank2` reached 1.02 times its control once made INLINE with its arrays moved into a lambda, so that its calls saturate it; and `map (\a -> toVector a) as` in place of `map toVector as` measured no gain there; why was not read.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/E07-argument-lambda-eta-expanded`, variants `base`; `noeta`, with `-fno-do-lambda-eta-expansion`; and `nofl`, with `-fno-full-laziness`, so the lambda stays where it was written; all `-dinline-check reduce3`): E01's INLINE fold given one argument and passed to a NOINLINE consumer, bare or under a lambda naming one more.

```haskell
{-# LANGUAGE BangPatterns #-}
module M where

{-# INLINE reduce3 #-}
reduce3 :: (Int -> Int -> Int) -> Int -> [Int] -> Int
reduce3 f z xs = go z xs
  where go !acc [] = acc
        go !acc (y : ys) = go (f acc y) ys

{-# NOINLINE apply2 #-}
apply2 :: (Int -> [Int] -> Int) -> [Int] -> [[Int]] -> [Int]
apply2 f zs xss = zipWith f zs xss

bare, lam :: [Int] -> [[Int]] -> [Int]
bare zs xss = apply2 (reduce3 (+)) zs xss
lam zs xss = apply2 (\z -> reduce3 (+) z) zs xss
```

By default `bare1 = reduce3 $fNumInt_$c+` and `lam1 = \ z eta -> lam_go z eta` (the inlined loop); under `noeta`, `lam1 = \ z -> reduce3 $fNumInt_$c+ z`. Under `nofl` the expanded lambda stays `apply2`'s argument, `apply2 (\ z eta -> case z of { I# ww -> ...`, and the log shows the call refused at two arguments and taken at three, each decision condensed to one line:

    Considering inlining: reduce3  arg infos [NonTrivArg, TrivArg]            BoringCtxt  guidance ALWAYS_IF(arity=3,unsat_ok=False,boring_ok=False)  ANSWER = NO
    Considering inlining: reduce3  arg infos [ValueArg, TrivArg, TrivArg]  BoringCtxt  guidance ALWAYS_IF(arity=3,unsat_ok=False,boring_ok=False)  ANSWER = YES

**Reproduces small:** yes.

### E08. A lambda behind work joins a pragma-free binding's count only if the work is cheap or the lambda one-shot (`oneShot`, the state hack)

**Rule.** A binding without a pragma has the count of the value lambdas of its right-hand side after `tryEtaExpandRhs` (E05), and the arity it is expanded to is `findRhsArity`'s ([compiler/GHC/Core/Opt/Arity.hs#L896][g279]). `arityType` passes a lambda through a `let` or an application argument with `floatIn` ([#L1272][g280], used by `arityApp` at [#L1297][g281] and for a `let` at [#L1623][g282]), which marks the lambda expensive unless the bound expression or argument is cheap (`myExprIsCheap`, [#L1527][g283]); `safeArityType` then cuts the arity at the first lambda that is not one-shot once it or a lambda before it is expensive ([#L832][g284]). A lambda is one-shot if its body certainly diverges, if its binder says so, as `GHC.Exts.oneShot` makes it, or, by the state hack, if it binds a `State#` token (`arityLam`, [#L1262][g285], with `idStateHackOneShotInfo`; `isStateHackType`, [#L253][g286]), which `-fno-state-hack` turns off ([#L255][g287]). The count follows: a binding whose second lambda sits behind an expensive `let` has count 1, guidance `IF_ARGS` with one discount; behind a cheap `let`, or behind an expensive one with the lambda one-shot, count 2, and a small body is then inlined at a partial call as an unsaturated `UnfWhen` (A02). Inlined at `map (f 3)`, the count-1 form leaves `let t = expensive 3` outside the lambda `map` calls, computed once; the one-shot count-2 form puts `expensive 3` inside it, computed for every element: the one-shot promise allows that, and the use here breaks the promise. An IO action counts its `State#` argument under the state hack (the interface `Arity: 2` for `Int -> IO Int`) and not without it.

**Seen.** Not in our record.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/E08-arity-work-and-one-shot`, variants `base` and `nostatehack`, `-fno-state-hack`, both `-dinline-check eta`): four pragma-free functions whose second lambda sits behind an expensive `let`, a cheap `let` (a partial application), an expensive `let` with the lambda marked `oneShot`, and an expensive `let` in an IO action; a client gives each its first argument.

```haskell
module M where

import GHC.Exts (oneShot)

{-# NOINLINE expensive #-}
expensive :: Int -> Int
expensive x = sum [1 .. x]

etaExp :: Int -> Int -> Int
etaExp x = let t = expensive x in \y -> t + y

etaCheap :: Int -> Int -> Int
etaCheap x = let t = max x in \y -> t y + y

etaOne :: Int -> Int -> Int
etaOne x = let t = expensive x in oneShot (\y -> t + y)

etaIO :: Int -> IO Int
etaIO x = let t = expensive x in return (t + 1)
```

```haskell
module C where
import M

uExp, uCheap, uOne :: [Int] -> [Int]
uExp ys = map (etaExp 3) ys
uCheap ys = map (etaCheap 3) ys
uOne ys = map (etaOne 3) ys

uIO :: IO Int
uIO = etaIO 3
```

Interface arities: `etaExp` `Arity: 1`, `etaCheap` and `etaOne` `Arity: 2`, `etaIO` `LambdaFormInfo: LFReEntrant 2, Arity: 2, Strictness: <ML><L>,` under `base` and `Arity: 1` under `nostatehack`. The guidance line of each decision at the client's calls:

    etaExp    guidance IF_ARGS [20] 100 60
    etaCheap  guidance ALWAYS_IF(arity=2,unsat_ok=True,boring_ok=False)
    etaOne    guidance ALWAYS_IF(arity=2,unsat_ok=True,boring_ok=False)
    etaIO     guidance ALWAYS_IF(arity=0,unsat_ok=True,boring_ok=True)   (base, the cast wrapper)
    etaIO1    guidance IF_ARGS [20 0] 51 10        (base; etaIO = etaIO1 `cast` <Co:6> in M)
    etaIO     guidance IF_ARGS [20] 61 10          (nostatehack)

All are inlined. The Core of `uExp` and `uOne`:

    uExp_t = case $wexpensive 3# of ww1 { __DEFAULT -> I# ww1 }
    uExp1 = \ y -> $fNumInt_$c+ uExp_t y
    uOne1 = \ v -> case $wexpensive 3# of ww1 { __DEFAULT -> case v of { I# y -> I# (+# ww1 y) } }

**Reproduces small:** yes.

### E09. Lambdas under a `case` on an argument join the count, unless `-fpedantic-bottoms`; a branch that is neither a lambda nor bottom stops them

**Rule.** For `case scrut of alts`, `arityType` takes the arity the alternatives share and keeps it if, without `-fpedantic-bottoms`, the scrutinee is cheap (a variable is), or if it is ok for speculation; otherwise it marks the first lambda expensive (`addWork`), so `safeArityType` cuts the arity there; a scrutinee that is certainly bottom gives no lambdas at all ([compiler/GHC/Core/Opt/Arity.hs#L1604][g288]; Note [Dealing with bottom], [#L466][g289]). Alternatives combine pointwise (`andArityType`, [#L1304][g290]); where one has run out of lambdas, a bottoming one yields to the other, and otherwise the other's lambdas are all marked expensive, or dropped under `-fpedantic-bottoms` (`andWithTail`, [#L1316][g291]). So by default `f b = case b of {True -> \y -> ...; False -> \y -> ...}` gets arity 2, and so does `case b of {True -> \y -> ...; False -> error ...}`; under `-fpedantic-bottoms` (`ao_ped_bot`, [compiler/GHC/Driver/Config/Core/Opt/Arity.hs#L13][g292]) both get arity 1, a lifted argument being neither cheap there nor ok for speculation; and with a variable of function type in one branch, `False -> k`, the lambda in the other is not exposed with or without the flag. The count of the pragma-free unfolding follows (E08), and with it which calls are saturated: by default `map (f True)` is a partial call of a count-2 unfolding, inlined only as a small `UnfWhen` with `unsat_ok` (A02); under `-fpedantic-bottoms` it saturates a count-1 one.

**Seen.** Not in our record.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/E09-arity-case-pedantic-bottoms`, variants `base` and `pedantic`, `-fpedantic-bottoms`, both `-dinline-check pb`): three pragma-free functions whose last lambda sits under a `case` on their first argument, with the other branch a lambda, a function-typed variable, or `error`; a client gives each all its arguments but the last.

```haskell
module M where

pbCase :: Bool -> Int -> Int
pbCase b = case b of
  True -> \y -> y + 1
  False -> \y -> y * 2

pbTail :: Bool -> (Int -> Int) -> Int -> Int
pbTail b k = case b of
  True -> \y -> y + 1
  False -> k

pbBot :: Bool -> Int -> Int
pbBot b = case b of
  True -> \y -> y + 1
  False -> error "pbBot"
```

```haskell
module C where
import M

uCase, uBot :: [Int] -> [Int]
uCase ys = map (pbCase True) ys
uBot ys = map (pbBot True) ys
uTail :: [Int] -> [Int]
uTail ys = map (pbTail False negate) ys
```

Interface arities, `base` then `pedantic`: `pbCase` `LambdaFormInfo: LFReEntrant 2, Arity: 2, Strictness: <1L><1!P(L)>,` then `LambdaFormInfo: LFReEntrant 1, Arity: 1, Strictness: <1L>,`; `pbBot` `[TagSig: <TagFun[TagEPT]>, LambdaFormInfo: LFReEntrant 2, Arity: 2,` then `[TagSig: <TagFun[TagDunno]>, LambdaFormInfo: LFReEntrant 1, Arity: 1, Strictness: <1L>, Unfolding: Core: <vanilla>`; `pbTail` `LambdaFormInfo: LFReEntrant 2, Arity: 2, Strictness: <1L><ML>,` under both. At the client, `base` then `pedantic`, the guidance line of each decision on `pbCase` and `pbBot`:

    pbCase  guidance ALWAYS_IF(arity=2,unsat_ok=True,boring_ok=False)   then   guidance ALWAYS_IF(arity=1,unsat_ok=True,boring_ok=True)
    pbBot   guidance ALWAYS_IF(arity=2,unsat_ok=True,boring_ok=False)   then   guidance ALWAYS_IF(arity=1,unsat_ok=True,boring_ok=True)

each inlined in both (these bodies are small enough for `UnfWhen`, A02); with larger bodies the same count decides whether the call is saturated.

**Reproduces small:** yes, the counts; no repro here shows a decision that the flag turns from yes to no.

### E10. A CallStack bound before a lambda counts as cheap, so `HasCallStack` does not cut the count; `-fdicts-cheap` does the same for a let-bound dictionary not already cheap

**Rule.** `myExprIsCheap` treats an expression of `CallStack` type, or of a `HasCallStack` (`IP ... CallStack`) dictionary type, as cheap whatever it computes, and, under `-fdicts-cheap` (off by default), any expression of dictionary type ([compiler/GHC/Core/Opt/Arity.hs#L1527][g283], the `cheap_dict` test at [#L1531][g293]; Note [Eta expanding through CallStacks] at [#L1414][g294], Note [Eta expanding through dictionaries] at [#L1435][g295]). The desugarer binds a function's pushed `CallStack` between its dictionary lambda and its value lambdas, so without this the value lambdas would be expensive and cut (E08); with it, `withCS :: HasCallStack => Int -> String` has arity 2, while the same shape with an `Int` computed in that place has arity 1. The count of the pragma-free unfolding follows (E08). The dictionary test is `isDictTy`, a class predicate ([compiler/GHC/Core/Predicate.hs#L247][g296]), and a type reaches `myExprIsCheap` only from `arityType`'s let, letrec and case-scrutinee callers ([compiler/GHC/Core/Opt/Arity.hs#L1625][g297], [#L1632][g298], [#L1611][g299]), an argument being costed without one ([#L1594][g300]); so `-fdicts-cheap` moves only a let- or case-bound binding of class type that is not cheap already and that survives until arity analysis.

**Seen.** `docs/pragmas-and-flags.md`, "Flags": horde-ad keeps `-fdicts-cheap`, `grad k MapAccum` allocating 6.4 times as much without it on GHC 9.14.1, and on HEAD 4.75 times at size 100 and 5.36 times at 1000. The binding is the `EqH (PlainOf target) (TKScalar Int)` dictionary of `tsoneHot`'s context, in `interpretAst`'s copies specialised in `AstInterpret` at a fixed span and taking `ADReady target`: `$p1CommonTargetEqOrd @(PlainOf target) d @Int $dNumScalarInt`, a quantified superclass selected and applied to its `NumScalar Int` argument, two value arguments where `isCheapApp` counts a class-op application cheap only at one ([compiler/GHC/Core/Utils.hs#L1972][g301]). Without the flag it is bound between the environment lambda and the term lambda, and the FullSpan, PlainSpan and PrimalSpan copies have arity 2 instead of 3, the DualSpan one, whose term binder is one-shot, keeping 3; `mapAccum`'s body is interpreted through them once per element, from the `HFun` that `interpretAstHFun` builds over an abstract target. Removing the `tsoneHot` branch, the flag still off, gives the copies arity 3 and the with-flag allocation to 0.2%.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/E10-arity-callstack-and-dicts`, variants `base`, `dictscheap` with `-fdicts-cheap`, and `ds`, `-O -ddump-ds -dsuppress-uniques -dsuppress-module-prefixes`, dumping the desugarer's output): a `HasCallStack` function and an `Int` lookalike, and functions binding a dictionary before their value lambda, for `-fdicts-cheap`, the last two passing it to a NOINLINE function.

```haskell
{-# LANGUAGE ImplicitParams #-}
module M where

import GHC.Stack (HasCallStack, callStack, prettyCallStack)

{-# NOINLINE push #-}
push :: Int -> Int
push s = s * 7 + 1

{-# NOINLINE expensive #-}
expensive :: Int -> Int
expensive x = sum [1 .. x]

withCS :: HasCallStack => Int -> String
withCS = \x -> show x ++ prettyCallStack callStack

withInt :: Int -> Int -> String
withInt s = let s2 = push s in \x -> show x ++ show s2

dSel :: Ord a => a -> Bool
dSel = \x -> x == x

dFun :: Eq a => a -> [a] -> Bool
dFun x = \ys -> [x] == ys

ipLet :: Int -> Int -> Int
ipLet n = let ?p = expensive n in \y -> y + ?p

{-# NOINLINE elemN #-}
elemN :: Eq a => a -> [a] -> Bool
elemN x ys = any (== x) ys

dFunKept :: Eq a => a -> [a] -> Bool
dFunKept x = \ys -> elemN [x] [ys]

{-# NOINLINE useP #-}
useP :: (?p :: Int) => Int -> Int
useP y = y + ?p

ipKept :: Int -> Int -> Int
ipKept n = let ?p = expensive n in \y -> useP y
```

The desugarer binds `withCS`'s pushed stack before the lambda, not work-free: `Value=False, ConLike=False, WorkFree=False, Expandable=False, Guidance=IF_ARGS [] 340 0}] $dIP = C:IP @"callStack" @CallStack (pushCallStack ...`. In both variants `withCS` has `Arity: 2, Strictness: <MP(1L)><1!P(L)>, Inline: [2],` (its wrapper's entry) and `withInt` keeps its `let` outside its lambda:

    withInt = \ s -> let { lvl = case s of { I# ww -> case $wpush ww of ww1 { __DEFAULT -> itos ww1 [] } } } in \ x -> ...

`dFunKept` keeps its dictionary in a `let` before the lambda, `LFReEntrant 1, Arity: 1,` in `base`'s `M.iface`:

    dFunKept = \ @a $dEq -> let { $dEq1 = $fEqList $dEq } in (\ x ys -> dFunKept1 $dEq1 (: x []) (: ys [])) `cast` <Co:8>

and under `-fdicts-cheap` takes all three arguments, `LFReEntrant 3, Arity: 3,`, building the dictionary at each call:

    dFunKept1 = \ @a $dEq eta eta1 -> dFunKept2 ($fEqList $dEq) (: eta []) (: eta1 [])

`dFun` and `dSel` in `base`: `dFun = \ @a $dEq x ys -> $fEqList_$c== $dEq (: x []) ys` and `dSel = \ @a $dOrd eta -> == ($p1Ord $dOrd) eta eta`. The desugarer binds `ipKept`'s parameter as a constructor application, `$dIP = C:IP @"p" @Int (expensive n) } in \ (y :: Int) -> useP $dIP y`, and after simplification, under `-fdicts-cheap` too, the binding is the `Int`: `ipKept = \ n -> let { $dIP = case n of { I# ww -> case $wexpensive ww of ww1 { __DEFAULT -> I# ww1 } } } in \ y ->`.

**Reproduces small:** yes: the CallStack rule, and `-fdicts-cheap` at `dFunKept`, whose dictionary-function application `$fEqList $dEq` is let-bound before the lambda, arity 1 without the flag and 3 with it, the dictionary then built at every call. The flag changed no other arity here (`dSel` 2, `dFun` 3, `ipLet` and `ipKept` 1 in both variants): `dSel`'s superclass selection is a class-op application with one argument, cheap already (`isCheapApp`, its `ClassOpId` case, [compiler/GHC/Core/Utils.hs#L1972][g301]); the class-op rule consumes `dFun`'s dictionary-function application where the method selection meets it; and the simplifier turns the implicit parameter's binding in `ipLet` and `ipKept` into the `Int` it holds, which is not of class type.

### E11. A local function's lambdas, or an unexported top-level function's, become one-shot and join its count when every call applies it to that many arguments

**Rule.** `findRhsArity` combines the arity type of a right-hand side with the binder's use: the demand put on it, and the call arity, if `-fcall-arity` ran (`useSiteCallCards`, [compiler/GHC/Core/Opt/Arity.hs#L986][g302]; used at [#L928][g303]). A lambda that, by that demand, each partial application calls at most once is made one-shot (`combineWithCallCards`, [#L960][g304]; Note [Combining arity type with demand info] at [#L1090][g305]), so expensive work in front of it no longer cuts the arity (E08); under `-fpedantic-bottoms` the call must be exactly once rather than at most once (wrinkle (CAD1)). A function used only at full application then has the full count, and the same function shared at a partial application keeps the work outside and a count of 1. A top-level function that is not exported gets the same: demand analysis treats the module as nested lets whose body is the exported binders and gives a top-level binder of nonzero type arity its use-site demand (Note [Analysing top-level bindings], [compiler/GHC/Core/Opt/DmdAnal.hs#L206][g306]; `isInterestingTopLevelFn`, [#L145][g307]; `setBindIdDemandInfo`, [#L314][g72]), and Call Arity analyses it as well (its `isExportedId` test, [compiler/GHC/Core/Opt/CallArity.hs#L449][g308]); an exported function gets no demand from its uses and keeps its arity.

**Seen.** Not in our record.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/E11-arity-from-call-sites`, variant `base`): one local function whose second lambda sits behind an expensive `let`, called with both arguments at every use, and a copy of it shared at one argument.

```haskell
module M where

{-# NOINLINE expensive #-}
expensive :: Int -> Int
expensive x = sum [1 .. x]

twoArgs :: Int -> Int -> Int
twoArgs n m = f n m + f m n
  where
    {-# NOINLINE f #-}
    f x = let y = expensive x in \p -> y * p + x

shared :: Int -> Int -> [Int]
shared n m = let g = f n in [g m, g n]
  where
    {-# NOINLINE f #-}
    f x = let y = expensive x in \p -> y * p + x
```

Both local functions end at top level; the first was expanded (the lambda `eta`) and split by worker/wrapper, the second keeps its `let` outside its second lambda:

    twoArgs_f = \ x eta -> case x of { I# ww -> case eta of { I# ww1 -> case $wf ww ww1 of ww2 { __DEFAULT -> I# ww2 } } }
    shared_f = \ x -> let { y = case x of { I# ww -> case $wexpensive ww of ww1 { __DEFAULT -> I# ww1 } } } in \ p -> ...
    shared = \ n m -> let { g = shared_f n } in : (g m) (: (g n) [])

A second repro (`~/r/horde-ad/dist-inlcat/cases/E11-top-level-call-demand`, variants `base`; `nocallarity` with `-fno-call-arity`; `pedantic`, `nocallarity` with `-fpedantic-bottoms`; `dmd`, `nocallarity` with `-ddump-stranal` and, of the two suppression flags, `-dsuppress-uniques` alone): the same shape at top level, once exported and once not, both NOINLINE and called with both arguments.

```haskell
module M (client, topExp) where

{-# NOINLINE expensive #-}
expensive :: Int -> Int
expensive x = sum [1 .. x]

{-# NOINLINE topLocal #-}
topLocal :: Int -> Int -> Int
topLocal x = let y = expensive x in \p -> y * p + x

{-# NOINLINE topExp #-}
topExp :: Int -> Int -> Int
topExp x = let y = expensive x in \p -> y * p + x

client :: Int -> Int -> Int
client n m = topLocal n m + topLocal m n + topExp n m + topExp m n
```

In `dmd`, `topLocal` carries its uses' demand, `topLocal [InlPrag=NOINLINE, Dmd=LC(L,C(1,!P(L)))] :: Int -> Int -> Int [LclId, Arity=1,` at the first demand analysis and `Arity=2,` at the second, with `topLocal = \ (x [Dmd=1!P(L)] :: Int) (p [Dmd=1!P(L), OS=OneShot] :: Int) ->`, and `topExp` none, `topExp [InlPrag=NOINLINE] :: Int -> Int -> Int [LclIdX, Arity=1,`. Their interfaces give `topLocal` `LFReEntrant 2, Arity: 2,` in `nocallarity` and `pedantic`, and `topExp` `LFReEntrant 1, Arity: 1,`.

**Reproduces small:** yes, the arity, at top level with the demand that causes it; for the local functions `-dsuppress-all` hides the demand.

### E12. A partial application passed to an inlined higher-order function that uses it in more than one branch is copied to its uses and saturated there; a lambda that saturates the same call grows first, stays bound, and is called

**Rule.** When an INLINE higher-order function is inlined, its function parameter is let-bound to the argument. If the parameter is used in more than one branch, `postInlineUnconditionally` substitutes the binding at its uses only under A17's conditions, testing the right-hand side after simplifying it. A partial application `zipWithA (+)` of an INLINE `zipWithA` stays small, `zipWithA` not being inlined into it (E01), so it is copied to each use, where the loop applies it in full and `zipWithA` is inlined into the loop; full laziness then binds what depends only on values fixed outside the loop (here a lifted `strides n n`) once, before the loop. A lambda `\x y -> zipWithA (+) x y` saturates `zipWithA`, which is inlined into it (E01), so it is too big to copy: it stays bound, is floated to top level (it is closed), is split by worker/wrapper, and the loop calls its worker once a row, which recomputes the shape-only values at every call. So saturating a call can move the INLINE function's body out of the loop it was meant to be inlined into. With the parameter used once, both forms are inlined into the loop (tried: the two clients then compiled to the same Core). Source: A17's and E01's.

**Seen.** Orthotope's benchmark: Dynamic `rerank2` with `ARR.zipWithA (+)` partly applied had `zipWithA` inlined in its loop over rows and `getStridesT isha` and `isha == ishb` bound once outside it; with `\ x y -> ARR.zipWithA (+) x y` the loop called a top-level `$weta8` once a row, which computed them at every call; the saturated form allocated less and, at the large size, ran 1.7 to 4.2% more instructions.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/E12-pap-vs-lambda-argument`, variant `base`, with `-dinline-check rowFn` and `-ddump-simpl-stats`): an INLINE `zipWithA` whose result carries a lifted value computed from the two shapes alone, and an INLINE `rerank2` that applies its function parameter `rowFn`, at two places, to rows of one inner shape; a client passes `zipWithA (+)` or `\x y -> zipWithA (+) x y`.

```haskell
{-# LANGUAGE BangPatterns #-}
module M where

data Arr = Arr !Int [Int] [Int]

{-# NOINLINE strides #-}
strides :: Int -> Int -> [Int]
strides n m = [n * 31 + m, n + m]

{-# INLINE zipWithA #-}
zipWithA :: (Int -> Int -> Int) -> Arr -> Arr -> Arr
zipWithA f (Arr n _ xs) (Arr m _ ys) = case n of
  0 -> Arr n [] []
  1 -> Arr n (strides n m) (zipWith f xs ys)
  2 -> Arr n (strides n m) (zipWith f (reverse xs) ys)
  3 -> Arr n (strides n m) (zipWith f (drop 1 xs) (take 1 ys) ++ zipWith f xs ys)
  4 -> Arr n (strides n m) (zipWith f (drop 2 xs) (take 2 ys) ++ zipWith f ys xs)
  _ -> Arr n (strides n m) (zipWith f (drop 3 xs) (take 3 ys) ++ zipWith f xs xs)

{-# INLINE rerank2 #-}
rerank2 :: (Arr -> Arr -> Arr) -> Int -> [[Int]] -> [[Int]] -> [Arr]
rerank2 rowFn !n xss yss = case xss of
  [] -> [rowFn (Arr n [] []) (Arr n [] [])]
  _ -> zipWith (\xs ys -> rowFn (Arr n [] xs) (Arr n [] ys)) xss yss
```

```haskell
module C where
import M

cPart, cSat :: Int -> [[Int]] -> [[Int]] -> [Arr]
cPart n xss yss = rerank2 (zipWithA (+)) n xss yss
cSat n xss yss = rerank2 (\x y -> zipWithA (+) x y) n xss yss
```

The statistics: `44 PostInlineUnconditionally` includes `3 f 1 rowFn 1 xs 1 ys`, one `rowFn` binding substituted; `UnfoldingDone` includes `3 zipWithA 3 flipSeq 2 rerank2` and, later, `2 rowFn`, the floated wrapper. In `$wcPart` the shape-only thunks are bound before the row loop and shared by every row:

    let { wild2 = I# ww } in let { lvl21 = strides wild2 wild2 } in ...
      letrec { go2 = ... __DEFAULT -> Arr wild4 lvl21 (let { z1 = go ipv ipv } in ...

while `$wcSat`'s loop calls the worker of the floated lambda, which builds `strides` at each call (the wrapper inlined at both uses: `Considering inlining: rowFn ... guidance ALWAYS_IF(arity=2,unsat_ok=True,boring_ok=False)`, `ANSWER = YES`):

    : (case $wrowFn ww ipv ww ipv5 of { (# ww1, ww2, ww3 #) -> Arr ww1 ww2 ww3 }) (go2 ipv4 ipv3)
    $wrowFn = \ ww ww1 ww2 ww3 -> case ww of wild3 { __DEFAULT -> (# wild3, strides (I# wild3) (I# ww2), ...

**Reproduces small:** yes, given three conditions found by trying: the parameter used in two branches (used once, both forms were inlined into the loop), `zipWithA` big enough that the lambda holding it is not small, and the shape-only value lifted and bound outside the loop's `case` on the shape (`rerank2` strict in it), so that full laziness can float it. Orthotope's generic `rerank2` (`Data/Array/Internal/DynamicG.hs`, checkout at "Condense the account of unorderedRouteT's sort and merge") applies `f` at two places too, its one-subarray case and its `zipWith` over the subarrays.

### E13. Worker/wrapper splits a function only at lambdas its right-hand side shows

**Rule.** `splitFun` splits a binding at its arity only if its right-hand side has that many value lambdas on top (`collectNValBinders_maybe ww_arity rhs`, [compiler/GHC/Core/Opt/WorkWrap.hs#L766][g309]; `workWrapArity`, [compiler/GHC/Core/Opt/WorkWrap/Utils.hs#L291][g310]), and otherwise leaves it whole without eta-expanding it (Note [Don't eta expand in w/w], [compiler/GHC/Core/Opt/WorkWrap.hs#L699][g311]). A partial application on a right-hand side is not eta-expanded by the simplifier (E05), so it is not split while it remains one, though its arity, strictness and CPR signature say it could be; where it is not inlined at its calls (NOINLINE here), callers pass and receive boxed values. Worker/wrapper does not split an INLINE function at all (U09), keeps a small one whole (U07) and splits an INLINABLE one, moving its unfolding to the worker (U08); the wrapper's unfolding, unlike an INLINE one (E01), can be inlined at a call giving fewer arguments than its arity but at least one (A26). The worker's arity is the number of arguments left after unboxing (`work_arity`, [#L880][g312]).

**Seen.** Orthotope's `fmap`, split into a wrapper and `$w$cfmap`, its callers calling the worker out of line (E03).

**Repro** (`~/r/horde-ad/dist-inlcat/cases/E13-worker-wrapper-and-eta`, variant `base`, `-dinline-check work3`): a strict function returning a product, too big to inline, and two NOINLINE functions over it, one point-free and one naming its arguments; a client calls both, and passes `work3` to `map` with none and with one of its three arguments.

```haskell
module M where

data P = P !Int !Int

work3 :: Int -> Int -> Int -> P
work3 k x y = case k `rem` 4 of
  0 -> P (x * y + k) (x - y)
  1 -> P (x + y * k) (y - x)
  2 -> P (x * k - y) (x + y + k)
  _ -> P (x `quot` (y + 1)) (k * x * y)

{-# NOINLINE papW #-}
papW :: Int -> Int -> P
papW = work3 7

{-# NOINLINE namedW #-}
namedW :: Int -> Int -> P
namedW a b = work3 7 a b
```

```haskell
module C where
import M

usePap, useNamed :: Int -> Int -> Int
usePap a b = case papW a b of P x _ -> x
useNamed a b = case namedW a b of P x _ -> x

none :: [Int] -> [Int -> Int -> P]
none ks = map (\k -> work3 k) ks
one :: [Int] -> [Int -> P]
one xs = map (work3 1) xs
```

`papW`'s interface entry has `LambdaFormInfo: LFReEntrant 2, Arity: 2, Strictness: <1!P(L)><1!P(1L)>, CPR: 1, Inline:]`, a strict and CPR signature but no worker; it became a lambda only after the split, when `work3`'s wrapper was inlined into it at one argument (`Considering inlining: work3 arg infos [ValueArg] interesting continuation RhsCtxt(NonRecursive) ... guidance ALWAYS_IF(arity=3,unsat_ok=True,boring_ok=False) ... ANSWER = YES`). `namedW` was split, `$wnamedW = \ ww ww1 -> ...`. `work3`'s wrapper has `Unfolding: Core: StableSystem <3,TrueFalse>`. In the client:

    usePap = \ a b -> case papW a b of { P bx _ -> I# bx }
    (useNamed)  case $wnamedW ww ww1 of { (# ww2, _ #) -> I# ww2 }
    none = \ ks -> map work3 ks
    one1 = \ x y -> case x of { I# ww1 -> case y of { I# ww2 -> P (+# ww1 ww2) (-# ww2 ww1) } }

the wrapper not inlined with no argument (`arg infos []`, `RuleArgCtxt`, `ANSWER = NO`; the lambda in `none` was eta-reduced to `work3`, E04) and inlined with one, after which the worker, given the known `k`, was inlined too.

**Reproduces small:** yes.

### E14. A join point jumped to only from inside a loop's exit join point is taken for an exit join point and, without a stable unfolding, gets none, so it is not inlined at its jumps; saturating a call can give a caller such a join point taking a vector boxed, which bangs on unrelated bindings can undo

**Rule.** A join point jumped to only from inside a loop's exit join point is taken for an exit join point and, without a stable unfolding, gets none, so it is not inlined at its jumps. Orthotope's boxed join point is such a join point. It has the shape of a worker/wrapper wrapper (below), taking the vector apart and jumping to a worker that takes its fields, as a split by the arguments' demands would (`workWrapArity`, [compiler/GHC/Core/Opt/WorkWrap/Utils.hs#L291][g310]); and a small model of that shape shows what keeps it at the jumps: `isExitJoinId` classifies it as an exit join point. The occurrence analyser adds a non-recursive join point's right-hand-side usage at each of its jumps (`mkOneOcc`, [compiler/GHC/Core/Opt/OccurAnal.hs#L3881][g313]; Note [Occurrence analysis for join points], [#L632][g314]), so a join point jumped to only from a loop's exit join point, the jumps to that exit join point sitting inside the loop's `joinrec`, has one occurrence inside a lambda; `isExitJoinId` classifies any join point with such an occurrence as an exit join point ([compiler/GHC/Core/Opt/Simplify/Utils.hs#L3063][g151]; Note [Do not inline exit join points]), so `simplLetUnfolding`, unless the join point has a stable unfolding ([compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4847][g315]), gives it none ([compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4855][g152]), and no jump to it is considered for inlining again (A20). In the Seen's saturated build, as in the model, the box-passing jumps sit in the fill loops' exit join points, which there are workers of vector's own `foldlM'` continuations rather than join points Exitification made. This route needs `$j18` to have no stable unfolding, though a wrapper made by worker/wrapper has one (`mkWrapperUnfolding`, [compiler/GHC/Core/Unfold/Make.hs#L116][g184]), and it has none: in that build's `OpsDynamic`, recompiled with its unfoldings in the dumps, `$j18` (`$j_s3N7g` in the occurrence analyses) has no `Unf=` in any of them, is `OnceL3` from the first, three analyses before Exitification, and no `Considering inlining` line names it (section 6, item 9). The tree's patch to `freshly_born_join_point` does not bear on it: its test ([compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4850][g316]) is false of a join point occurring once. No eta rule bears either: a join point is never eta-expanded (`findRhsArity` returns `False` for one, [compiler/GHC/Core/Opt/Arity.hs#L897][g317]; Note [Do not eta-expand join points] at [#L1143][g318]) nor is a call of one eta-reduced below its join arity (`cantEtaReduceFun`, [compiler/GHC/Core/Utils.hs#L2380][g258]).

**Seen.** Orthotope's benchmark: saturating the summed reading's call of Storable `zipWithA` (Dynamic) made a join point of the summing function take the result's `Data.Vector.Storable.Vector` boxed, building that box, 32 bytes, once a call, where the partly applied form passed its fields. In the saturated build (against the tip of 2026-10-14, "Condense the account of unorderedRouteT's sort and merge") the join point takes the vector boxed and does nothing but evaluate its list argument, unpack the vector and jump to `$w$j_0` with the fields, its caller building the box to jump to it, where the tip jumps to `$w$j_0` with the fields; rows written `uncurry (\ a b -> ARR.zipWithA (+) a b)` allocate as the saturated ones in every cell, refuting the guess that the box comes from `inline` unfolding the row; a build whose other rows are saturated and whose `zipWithA.singleR` row is unchanged pays the same 32 bytes at that row (H), a module-level effect. Banging every argument of the wrapper modules that their demands give as strict removed exactly that box, though those rows call none of the banged wrappers (NB), and so did banging the DynamicS and DynamicU wrappers alone, in 17 cells (W). A box of the same kind moves with an INLINE definition's left-hand side: with orthotope's `mapT sh f = convertT sh (vMap f)` in place of `mapT sh f t = convertT sh (vMap f) t`, a join point of the summing worker at summed small boxed Dynamic `zipWithA` takes the freshly built boxed `Data.Vector.Vector` and the strides list, where the named form's takes the vector's fields and builds it inside, 32 bytes a call. In that build's dump (`OpsDynamic.dump-simpl`, `$wlvl354`): the join point, there `$j18`, is a non-recursive `join`, so no loop breaker, its parameters `ww15 :: [Int]`, `ww16 :: Int#` and `ww17 :: Data.Vector.Storable.Vector Double` and its body `case ww15 of ww18 { __DEFAULT -> case ww17 of { Data.Vector.Storable.Vector ipv5 ipv6 ipv7 -> jump $w$j18 ww18 ww16 ipv5 ipv6 ipv7`, a worker/wrapper wrapper; of the three jumps to it that follow, two sit in join point workers and pass a box built there, `jump $j18 ww11 (-# ww2 bx2) (Data.Vector.Storable.Vector @Double ww15 ipv7 ipv8)`, and one passes the case binder of a constant. The two box-passing jumps sit inside a fill's `runRW#`, each in that fill's loop-exit join point `$w$j19`, which a `joinrec` `$wfoldlM'_loop` jumps to, and the third, `jump $j18 wild 0# wild1`, inside neither. The tip's function, `$wlvl348` in its dump, is the same but for local names and that wrapper: its three jumps go to the worker, as `jump $w$j18 wild 0# ipv5 ipv6 ipv7` does, where all three in the saturated build go to the wrapper, the third passing no box (`jump $j18 wild 0# wild1`). Every simplifier run in `OpsDynamic`, `OpsRanked` and `OpsShaped` of both builds runs all four of its iterations (`SimplifierDone` 28 in their `dump-simpl-stats`, seven runs at `-O1`), against 17 to 20 in the benchmark's small modules; whether the cap cut any run short is not shown, since a run ends either after an iteration that changes nothing or after its fourth. Orthotope's Shaped `rerank` empty row (build SS) takes this route too, through a join point the simplifier makes after worker/wrapper, at a cost of 16 bytes a call (O28, reproduced small).

**Repro** (`~/r/horde-ad/dist-inlcat/cases/E14-saturation-boxes-join-point-arg`, variants `base`; `spec`, with `-fspecialise-aggressively -fexpose-overloaded-unfoldings` as orthotope builds; `it1` and `it2`, `spec` at `-fmax-simplifier-iterations=1` and `=2`): a Storable `zipWithA` with orthotope's `zipWithT` shape (a scalar case, two map cases, the general case) over a class of vector operations, under `HasCallStack`; a consumer summing every component of the result, as the summed reading does; and the row passed to a `call` that stores it and sums it at its site, so the row's function is used at two places, written partly applied, `uncurry (zipWithA (+))`, and saturated, `\ (a, b) -> zipWithA (+) a b`, as orthotope's rows were before and after saturation. A second model, `sumBoth` in `M`, has the shape the dump shows: the summing of a `T` made by one of two Storable fills, so a continuation strict in a list, an `Int` and the vector's fields, which worker/wrapper splits, reached from inside each fill's `runRW#`.

```haskell
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE BangPatterns #-}
module M where

import qualified Data.Vector.Storable as VS
import GHC.Stack (HasCallStack)

-- The vector operations as a class, as orthotope's generic arrays take them.
class Vec v where
  vLength :: v -> Int
  vIndex :: v -> Int -> Double
  vSingleton :: Double -> v
  vMap :: (Double -> Double) -> v -> v
  vZipWith :: (Double -> Double -> Double) -> v -> v -> v
  vSlice :: Int -> Int -> v -> v

instance Vec (VS.Vector Double) where
  {-# INLINE vLength #-}
  vLength = VS.length
  {-# INLINE vIndex #-}
  vIndex = VS.unsafeIndex
  {-# INLINE vSingleton #-}
  vSingleton = VS.singleton
  {-# INLINE vMap #-}
  vMap = VS.map
  {-# INLINE vZipWith #-}
  vZipWith = VS.zipWith
  {-# INLINE vSlice #-}
  vSlice = VS.slice

-- A strided view, its strides, offset and vector, and an array: its shape
-- and view (the shape of orthotope's generic arrays).
data T v = T [Int] !Int !v
data A v = A [Int] !(T v)

{-# INLINABLE toVectorT #-}
toVectorT :: Vec v => [Int] -> T v -> v
toVectorT sh (T _ o v) = vSlice o (product sh) v

{-# NOINLINE stridesFor #-}
stridesFor :: [Int] -> [Int]
stridesFor = scanr (*) 1 . drop 1

-- zipWithT's shape: a scalar case, two map cases and the general one.
{-# INLINE zipWithT #-}
zipWithT :: Vec v => [Int] -> (Double -> Double -> Double) -> T v -> T v -> T v
zipWithT sh f t@(T ss _ v) t'@(T _ _ v') =
  case (vLength v, vLength v') of
    (1, 1) | 0 `notElem` sh ->
      T ss 0 (vSingleton (f (vIndex v 0) (vIndex v' 0)))
    (1, _) | 0 `notElem` sh ->
      let x = vIndex v 0
      in T (stridesFor sh) 0 (vMap (x `f`) (toVectorT sh t'))
    (_, 1) | 0 `notElem` sh ->
      let y = vIndex v' 0
      in T (stridesFor sh) 0 (vMap (`f` y) (toVectorT sh t))
    _ -> T (stridesFor sh) 0 (vZipWith f (toVectorT sh t) (toVectorT sh t'))

{-# INLINE zipWithA #-}
zipWithA :: (HasCallStack, Vec v) => (Double -> Double -> Double) -> A v -> A v -> A v
zipWithA f (A sh t) (A _ t') = A sh (zipWithT sh f t t')

-- The summed reading's consumer: every component of the result summed.
{-# INLINE sumVec #-}
sumVec :: VS.Vector Double -> Double
sumVec v = go 0 0
  where
    !len = VS.length v
    go !i !acc | i >= len = acc
               | otherwise = go (i + 1) (acc + VS.unsafeIndex v i)

{-# INLINE summed #-}
summed :: A (VS.Vector Double) -> Double
summed (A sh (T st o v)) = fromIntegral (sum sh + sum st + o) + sumVec v

-- The second model: the summing continuation of two fills, a join point that
-- worker/wrapper splits (strict in a list, an Int and a vector's fields),
-- jumped to from inside each fill's runRW#.
sumBoth :: Bool -> [Int] -> Int -> VS.Vector Double -> Double
sumBoth b xs n v =
  case (if b then T xs n (VS.map (* 2) v)
        else T (drop 1 xs) (n - 1) (VS.zipWith (+) v v)) of
    T ys m w -> fromIntegral (sum ys + m) + sumVec w
```

```haskell
module C where

import GHC.Exts (inline)
import M
import qualified Data.Vector.Storable as VS

type AS = A (VS.Vector Double)

-- The benchmark's row: the operation stored, and summed at its site, so
-- the row's function is used at two places.
data Call = Call ((AS, AS) -> AS) (AS, AS) ((AS, AS) -> Double)

{-# INLINE call #-}
call :: ((AS, AS) -> AS) -> (AS, AS) -> Call
call f x = Call f x (\ y -> summed (inline f y))

-- The operation partly applied, and applied to all its arguments.
rowPart, rowSat :: (AS, AS) -> Call
rowPart x = call (uncurry (zipWithA (+))) x
rowSat x = call (\ z0 -> case z0 of (a, b) -> zipWithA (+) a b) x
```

Both forms compile to the same Core, `rowPart = rowSat`, under every variant. The only `Vector` boxes built are in the stored operation (`$wlvl1`, returning the array, e.g. `join { $w$j ww10 = jump $j (T ww1 0# (Vector ww10 ipv6 ipv7)) } in`); the summing function builds none. The second model builds no `Vector` box either: `M.dump-simpl` holds none, under every variant, and `$wsumBoth = \ b xs ww ww1 ww2 ww3 ->` reaches its join points with unboxed values, as `1# -> jump $w$j ww4`. Also tried, each giving `rowPart = rowSat`: the same without the class, without `HasCallStack`, and with the rows summed directly rather than through `call`.

A second repro (`~/r/horde-ad/dist-inlcat/cases/E14-split-summing`, variants `nocpr`, and `nocpr-it1` and `nocpr-it2` capped at 1 and 2 iterations by `-fmax-simplifier-iterations`, all `-fno-cpr-anal`, so that the producers return `T` boxed; `cpr`; `check` and `checkw`, `-dinline-check $j` and `$w$j`; `occ` and `vcc`, the occurrence analyses, by `-ddump-occur-anal`, `vcc` with `-dverbose-core2core` too, both with `-dsuppress-uniques -dsuppress-coercions -dsuppress-type-applications -dsuppress-module-prefixes` in place of the two suppression flags; `late` and `latecheck`, `-flate-dmd-anal`): two out-of-line producers, each with two Storable fills, under an INLINE summing given the caller's `k`, so that its join point keeps a free variable and stays local.

```haskell
{-# LANGUAGE BangPatterns #-}
module N (c3, c4) where

import qualified Data.Vector.Storable as VS

data T = T ![Int] !Int !(VS.Vector Double)

prodA, prodB :: Bool -> Int -> VS.Vector Double -> T
prodA b n v
  | b = T [n, 1] 0 (VS.map (* 2) v)
  | otherwise = T [1, n] 1 (VS.zipWith (+) v (VS.reverse v))
prodB b n v
  | b = T [n, 2] 0 (VS.map (* 3) v)
  | otherwise = T [2, n] 1 (VS.zipWith (-) v (VS.reverse v))

{-# INLINE sumT #-}
sumT :: Int -> T -> Double
sumT k (T ys m w) = fromIntegral (sum ys + m + k) + VS.sum w

c3, c4 :: Int -> Bool -> Bool -> Int -> VS.Vector Double -> Double
c3 k b1 b n v = sumT k (if b1 then prodA b n v else prodB b n v)
c4 k b1 b n v = sumT k (if b1 then prodA b n v else prodB b n v)
```

`N.dump-simpl`, whitespace collapsed: before the final run the summing is a split join point, `$w$j ys bx ww ww ww` (`N.dump-worker-wrapper`); the final run inlines each producer in its first iteration and in its second has a join point of `$j18`'s form, `$j ys bx w = case ys of ys1 { __DEFAULT -> case w of { Vector ipv ipv1 ipv2 -> jump $w$j ys1 bx ipv ipv1 ipv2`, each fill's loop-exit join point jumping to it with a box, `$w$j1 ww4 = jump $j (: lvl18 (: n [])) 1# (Vector ww4 ipv5 ipv2) } in`, at each cap tried. The occurrence analysis the next iteration receives gives it `$j [Occ=OnceL2!T[3]] :: [Int] -> Int# -> Vector Double -> Double` (`vcc`'s `N.dump-occur-anal`), the final Core shows it as `$j :: [Int] -> Int# -> Vector Double -> Double [LclId[JoinId(3)(Nothing)], Arity=3]` with no `Unf=`, and no later iteration considers it (`check`'s `build.log`). With CPR the jumps pass the vector's fields, `join { $w$j1 ww4 = jump $j (: lvl18 (: n [])) 1# ww4 ipv5 ipv1 } in`; with `-flate-dmd-anal` the late worker/wrapper splits the join point again and the following run inlines the new wrapper at every jump, and no box is left; so too in the saturated build rebuilt with the flag, on `OpsDynamic` alone or on the whole build, whose `OpsDynamic` Cores are the same: `$j18` becomes a worker taking the list, the offset and the vector's fields, every jump to it passes the fields, and the summed Storable bytes of `zipWithA` at the small scalar view and of `zipWithA.singleR` at the small size fall by 32 a call to the tip's, the Unboxed ones falling by 32 at the same cells, where jumps of the same shape built a primitive vector's box. The same model with each vector built from an out-of-line foreign pointer, no `runRW#` in it (`~/r/horde-ad/dist-inlcat/cases/E14-no-runrw`), or returned through `unsafeDupablePerformIO`, the jumps inside `runRW#` but in no loop (`~/r/horde-ad/dist-inlcat/cases/E14-runrw-direct`), gives the join point `Occ=Once2!T[3]`, and the next iteration takes every jump, `guidance IF_ARGS [20 0 20] 20 0`, `ANSWER = YES`. A first form of the model, one producer whose summing join point is never split (`~/r/horde-ad/dist-inlcat/cases/E14-final-run-join-box`), builds the box at the same jumps.

**Reproduces small:** in part, by the second repro: the wrapper-shaped join point and the boxed jumps from the fills' loop exits, at the default iterations and capped at 1 or 2, when the producers return `T` boxed; with CPR the jumps pass the vector's fields. A base-only form of the model, not a case here, builds the boxes at plain `-O`, CPR on, a `T` and a `Q` at each exit, `join { exit ww1 ww2 = jump $j (T ww2 (Q ww1 ww2)) } in`, 80 bytes a call against 32 without a box, on HEAD, 9.12.4 and 9.14.1, where 9.10.3 and 9.8.4 jump from the loop with the fields unboxed; why was not traced. The third jump, outside any `runRW#`, shares `$j18`'s occurrence information and so falls under the same rule, the recompile in the Rule paragraph keeping `$j18` `OnceL3` with that jump in place. The first repro's two models do not reproduce it. Not tried: orthotope's generic module itself, the benchmark's module with all its rows (CSE and floating across rows), and the wrapper modules' bangs that removed the box. The box that moves with `mapT`'s left-hand side is not reproduced small.

### E15. The first float-out lifts local functions out of a lambda that Call Arity's eta-expansion later removes; CSE then merges the copies, and float-in leaves the merged one above the case

**Rule.** The first float-out runs after the specialiser and before both the simplifier's main phases and Call Arity ([compiler/GHC/Core/Opt/Pipeline.hs#L209][g319], `CoreDoFloatOutwards` with `floatOutLambdas = Just 0`; Call Arity at [Pipeline.hs#L255][g320]). Its level assignment opens a new major level at every value lambda that is not one-shot ([compiler/GHC/Core/Opt/SetLevels.hs#L1545][g321], `lvlLamBndrs`) and sends a let binding to the level of its free variables ([SetLevels.hs#L1607][g322], `destLevel`), so a local function under a `\case` lambda that mentions only variables bound outside that lambda floats out of it, here also above the guard's `case`; a case alternative opens no level, so in the argument form, where the `\case` lambda is a left-hand-side argument, the same functions stay in their alternatives. Call Arity later eta-expands a top-level function that is not exported when every call of it gives that many arguments ([compiler/GHC/Core/Opt/CallArity.hs#L371][g323], Note [Analysing top-level binds]), so the lambda the functions were floated out of is gone and nothing is shared by the float. CSE turns a recursive binding whose right-hand side equals an earlier one into an alias of it ([compiler/GHC/Core/Opt/CSE.hs#L400][g228], `cseBind`, Note [CSE for recursive bindings]), so the three loops that inlining the INLINE `mapS` put into three alternatives become one; and float-in does not push a binding into a case's alternatives when more than one of them uses it and it is not dupable ([compiler/GHC/Core/Opt/FloatIn.hs#L819][g324], `sepBindsByDropPoint`, Note [Duplicating floats]), so the merged loop stays above the case and its closure is allocated on every call that passes the guard, in `Lit` and `Add` too. With `-fno-cse` each copy is used in one alternative and float-in sinks it there. None of the tree's patches bears on it.

**Seen.** The GHC !12121 comment (`docs/ghc-issue-floatin-duplicate-values-comment.md` in horde-ad), section "The case", 582 MB against 320 MB for the argument form, on 9.12.2, 9.14.1 and HEAD alike; the programs are appendix A's `fmap1s/Repro.hs` and its argument form (`docs/ghc-issue-floatin-duplicate-values-appendix-a-programs.md`, section "The case"). It is the single-module reduction of horde-ad's `interpretAst` case, E16.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/E15-float-out-before-eta-cse-merge`, variants `lam`, `Main.hs`; `lamnocse`, `Main.hs` with `-fno-cse`; `arg`, the argument form, by `-DARG`; `lamnoca`, `Main.hs` with `-fno-call-arity`; `run` holds 200000): the documents' program, with a CPP switch for the argument form and the count of calls taken from the command line so that `measure.sh N` can difference two counts.

```haskell
{-# LANGUAGE LambdaCase, CPP #-}
module Main (main) where
import System.Environment (getArgs)

data E = Lit Int | Add E E | I1 E [Int] | I2 E [Int] | I3 E [Int]

check :: Int -> Bool
{-# NOINLINE check #-}
check k = k > 0

ev :: Int -> Int -> Int
{-# NOINLINE ev #-}
ev k i = k + i

mapS :: (a -> b) -> [a] -> [b]
{-# INLINE mapS #-}
mapS f l =
  let go [] = []
      go (x : xs) = let y = f x; rest = go xs in y `seq` rest `seq` (y : rest)
  in go l

eval :: Int -> E -> Int
#if defined(ARG)
eval k t | check k = case t of
#else
eval k | check k = \case
#endif
  Lit n -> n
  Add a b -> eval k a + eval k b
  I1 a ix -> eval k a + sum (mapS (ev k) ix)
  I2 a ix -> eval k a * sum (mapS (ev k) ix)
  I3 a ix -> eval k a - sum (mapS (ev k) ix)
#if defined(ARG)
eval _ _ = 0
#else
eval _ = const 0
#endif

mk :: Int -> E
mk 0 = Lit 0
mk n = Add (mk (n - 1)) (if even n then Lit n else I1 (Lit 1) [1, 2])

main :: IO ()
main = do
  [n] <- map read <$> getArgs
  print (sum [eval k (mk 20) | k <- [1 .. n]])
```

`lam`, `Main.dump-float-out`, the first float-out: the three loops, identical, float out of `\ ds` and above the guard:

```
eval
  = \ k ->
      letrec {
        go
          = \ ds ->
              case ds of {
                [] -> [];
                : x xs ->
                  case ev k x of y { I# ipv ->
                  case go xs of rest { __DEFAULT -> : y rest }
                  }
              }; } in
      letrec {
```

```
              }; } in
      case check k of {
        False -> lvl;
        True ->
          \ ds ->
            case ds of {
```

`arg`, the same pass: no lambda between the loops and `k`, nothing floated:

```
eval
  = \ k t ->
      case check k of {
        False -> lvl;
        True ->
          case t of {
```

`lam`, `Main.dump-cse`, after Call Arity's eta-expansion and worker/wrapper: the second and third loops become aliases of the first:

```
          let { go = go } in
          let { go = go } in
          case eta of wild {
```

`lam`, `Main.dump-simpl`: one loop above the case, allocated on every call:

```
        True ->
          let { k = I# ww } in
          letrec {
            go
              = \ ds ->
                  case ds of {
                    [] -> [];
                    : x xs ->
                      case ev k x of y { I# ipv ->
                      case go xs of rest { __DEFAULT -> : y rest }
                      }
                  }; } in
          case eta of {
            Lit n -> n;
```

`lamnocse`, `Main.dump-simpl`: each copy in its alternative:

```
            I1 a ix ->
              case $weval ww a of { I# x1 ->
              let { k = I# ww } in
              letrec {
                go
```

`lamnoca`, `Main.dump-simpl`: without Call Arity the worker keeps arity 1 and returns the lambda:

```
$weval
  = \ ww ->
      case $wcheck ww of {
```

Bytes in the heap (the run's `+RTS -s` report, 200000 calls): `lam` 582,458,408, `lamnocse` 320,058,408, `arg` 320,058,408, `lamnoca` 608,058,408. `measure.sh 200000`, a call of `eval k (mk 20)`: `lam` 2912 bytes and 5250 instructions, `lamnocse` and `arg` 1600 bytes and 4689 instructions.

**Reproduces small:** yes, the documents' program, with their figures.

### E16. A defining module's SPECIALISE copy and an importer's specialisation of one INLINABLE function meet the first float-out in different forms: behind a guard that is not cheap the copy keeps its arity short and floats its self-call as work, and where the defining module raises the arity only the importer's template is eta-expanded

**Rule.** A value lambda behind an expensive expression does not join a binding's arity unless it is one-shot (E08; [compiler/GHC/Core/Opt/Arity.hs][g325], `findRhsArity` and `myExprIsCheap`), and a guard that calls a NOINLINE function is expensive, so a function written `f !env | Dict <- g ... = \case ...` has arity 1 in its value arguments before the `\case`. Call Arity can raise it only for a binding that is not exported, all of whose calls are then in the module it analyses ([compiler/GHC/Core/Opt/CallArity.hs#L371][g323], Note [Analysing top-level binds]). An importer's own specialisation, local to the importer, gets it (variant `imp`, arity 3, and 2 again with `-fno-call-arity`); the defining module's SPECIALISE copy, local too, does not (`def`, arity 2). That copy's calls at `P` go through `f = $sinterp (C:KnownS $WSP) env`, the partial application `interp env` of the source's `interp env <$> ix`, which `fmap`'s INLINE unfolding let-binds and calls once an element. Call Arity does not count such a binding as cheap, so, called more than once, it gets arity 0 (`is_thunk` in `callArityBind`, [compiler/GHC/Core/Opt/CallArity.hs#L569][g326], and `safe_arity`, [#L577][g327]), and the calls through it count as giving the copy two arguments. Written `(\x -> interp env x) <$> ix`, the copy gets arity 3; the importer's copy gets 3 because its calls at `P` go to a further specialisation (the second repro). At the short arity the recursive call `f env a` is a saturated call followed by an application, and full laziness floats the saturated part out of the term lambda because it is not a head normal form ([compiler/GHC/Core/Opt/SetLevels.hs#L701][g328], `lvlMFE`, `saves_work`, Note [Saving work]), where at full arity it would be a partial application, a value, and stay. The float shares the inner closure among the calls of one level, and is not what keeps the arity short here: with `-fno-full-laziness` the copy keeps arity 2 and allocates more (`defnofl`). The cure is the arity worker/wrapper GHC [#19230](https://gitlab.haskell.org/ghc/ghc/-/work_items/19230) proposes, written by hand: an INLINE wrapper does the guard and returns `\t -> winterp env t`, and the INLINABLE worker `winterp` has the full arity, so at a saturated call, the recursive ones in `defww` and `impww` included, the wrapper is inlined and the call reaches a function of full arity whose local functions sit in their alternatives.

The two copies also start from different forms where the defining module raises the arity. A SPECIALISE pragma's copy is made by the desugarer from the right-hand side as written ([compiler/GHC/HsToCore/Binds.hs#L1064][g329], `dsSpec_help`, `spec_rhs = mkLams spec_bndrs (mk_spec_body poly_rhs)`), and goes through the gentle simplifier and the specialiser into the first float-out (the specialisation appendix, "Where the specialiser sits in the pipeline"; E15, O09). An importer specialises the imported function's stable unfolding instead ([compiler/GHC/Core/Opt/Specialise.hs#L911][g330], `canSpecImport`), which for INLINABLE is the right-hand side as written, simplified at each pass with only the inlinings active throughout its own activation and never eta-expanded there ([compiler/GHC/Core/Opt/Simplify/Utils.hs#L1212][g331] and [#L1214][g332], `updModeForStableUnfoldings`; U10), but eta-expanded to the binding's arity when that rises (E06). So the two routes start from the same form unless the defining module raises the binding's arity: then the importer's template, eta-expanded to the new arity, takes the term among its leading arguments, with no lambda left behind the guard, and its local functions stay in their alternatives, while the SPECIALISE copy, if a guard in front of its lambda is not yet cheap at the gentle pass (E08), meets the first float-out with the lambda present and goes the way of E15. An always-active INLINE guard is inlined into both forms in the gentle pass, and their lambdas then join the arity, unless the guard has an `error` alternative, as horde-ad's `dictSpanFam` has: case-of-case being off in that pass (`sm_case_case = False` in `initGentleSimplMode`, [compiler/GHC/Driver/Config/Core/Opt/Simplify.hs#L84][g333]), the inlined guard stays the scrutinee of the outer `case`, and the arguments of its `error` call are not cheap (`exprIsCheapX`'s case for an application, [compiler/GHC/Core/Utils.hs#L1928][g334], `isCheapApp` returning `True` for `error` itself, [#L1967][g335]), so `arityType` adds work ([compiler/GHC/Core/Opt/Arity.hs#L1618][g336]) and the lambda stays, in both forms (the fourth repro). Once the guard is gone, what holds fmaprepro's binding in the defining module at its arity is the index sum's zero at the element type, `fromInteger @a $dNum (GHC.Internal.Bignum.Integer.IS 0#)`, a class-op selection applied to two value arguments and so not cheap (`isCheapApp`, [compiler/GHC/Core/Utils.hs#L1972][g301]). The first float-out floats it in front of the term lambda of `interp`, and in front of that of the specialisation at `P`, which the partial self-call `interp env`, floated beside the zero, calls once phase 2's SPEC rule has fired. Held at arity 2 by its own zero, that specialisation leaves the floated call saturated, so that it too is work in front of `interp`'s lambda. Without the zero (the fifth repro) the floated calls are undone as horde-ad's are (Reproduces small), and a floated call of the binding itself holds nothing, a recursive binding's arity being found from an optimistic start ([compiler/GHC/Core/Opt/Arity.hs#L916][g337], [#L1555][g338]). The direct self-calls, over-saturated, do not float there, whatever the types the alternatives bind (`floatOutOverSatApps = False`, [compiler/GHC/Core/Opt/Pipeline.hs#L212][g339]; `lvlApp`, [compiler/GHC/Core/Opt/SetLevels.hs#L403][g340]). With no `error` alternative the gentle pass eta-expands both forms before the first float-out, and they start alike again (the fourth repro's `impgne` and `defgne`).

**Seen.** The GHC !12121 comment (`docs/ghc-issue-floatin-duplicate-values-comment.md` in horde-ad), its opening paragraph: specialising `interpretAst` in its defining module with SPECIALISE pragmas allocated 10.5% more on an MNIST benchmark than letting each importer specialise it; `docs/ghc-issue-floatin-duplicate-values-appendix-d-session-notes.md`, section "G2G results (2026-10-01, post-3rd-compaction)", item "horde-ad per-pass dumps", and section "STATE AT FOURTH COMPACTION (2026-10-01 ~11:55 UTC)", item "VTO residual of G2 DIAGNOSED": the importer's copy right after Specialise starts with `\ @s @y $dKnownSpan env term ->`, from a stable unfolding AstInterpret's simplifier had eta-expanded, while the SPECIALISE copy keeps `\ (ds :: AstTensor ..)` behind guards built from `lemPlainOfSpan` and `dictSpanFam` not yet inlined. The same section's items on "item 4" and "chain1" (957 MB for the defining module's copy against 198 MB for the argument form, and 192 MB with the worker/wrapper written by hand), and the table of fixes in `docs/ghc-issue-floatin-duplicate-values-comment.md`, row "arity worker/wrapper ([#19230](https://gitlab.haskell.org/ghc/ghc/-/work_items/19230)), written by hand". The program is fmaprepro, of the comment's appendix A, a program built on horde-ad's interpreter. And horde-ad's `docs/pragmas-and-flags.md`, "What stays, and why", the helpers' row, whose `grad k MapAccum` cost on HEAD is `dictSpanFam`'s INLINE alone. Without the INLINE, worker/wrapper splits `dictSpanFam`, and its worker `$wdictSpanFam` (`Guidance=IF_ARGS [30 20] 380 40`) is called in `interpretAst`'s guard. `AstInterpret`'s own FullSpan, PlainSpan and PrimalSpan copies of `interpretAst`, which the interpreted mapAccum body calls once per element, then have arity 2, with 33 bindings between `{ Dict0 $dCTuple3 ->` and the term lambda, the saturated PlainSpan self-call among them. `grad k MapAccum` then allocates 4.89 times as much at 100 elements and 5.51 times as much at 1000 (19015 bytes per element against 3399, the 100 and 1000 rows differenced), `grad s MapAccum` 2.71 and 2.83 times, and every `cgrad` row the same.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/E16-noinline-guard-self-call-floated`, the guard `NOINLINE mkDict` as appendix A files it, variants `def`, fmaprepro's G2G, a SPECIALISE copy in `Lib`, by `-DDEF`; `defnofl`, `def` with `-fno-full-laziness`; `defarg`, appendix A's argument form, by `-DARG`; `defww`, its worker/wrapper form, by `-DWW`; `imp`, `imparg`, `impww`, the same three as fmaprepro's GD, each importer specialising; `impnoca`, `imp` with `-fno-call-arity`; all at fmaprepro's flags `-O -fexpose-overloaded-unfoldings -fspecialise-aggressively -fdicts-cheap -fkeep-auto-rules`; `run` holds 200000): appendix A's fmaprepro (`docs/ghc-issue-floatin-duplicate-values-appendix-a-programs.md`, section "Across modules"), its three `Lib` files and its run script's `sed` placeholders folded into one `Lib.hs` by CPP, and the count of calls taken from the command line.

```haskell
{-# LANGUAGE LambdaCase, BangPatterns, DataKinds, GADTs, KindSignatures, RankNTypes, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes, CPP #-}
module Lib (E(..), Sp(..), KnownS(..), SSp(..), interp) where

import Ox

data Sp = F | P
data SSp (s :: Sp) where
  SF :: SSp 'F
  SP :: SSp 'P
class KnownS (s :: Sp) where sing :: SSp s
instance KnownS 'F where sing = SF
instance KnownS 'P where sing = SP

data Dict where Dict :: Dict
mkDict :: SSp s -> Dict
{-# NOINLINE mkDict #-}
mkDict SF = Dict
mkDict SP = Dict

data E (s :: Sp) = Lit Int | Var | Add (E s) (E s)
  | I1 (E s) (IxS (E 'P)) | I2 (E s) (IxS (E 'P)) | I3 (E s) (IxS (E 'P))

sumL :: Num a => IxS a -> a
{-# INLINE sumL #-}
sumL (IxS (IxX (ListX l))) = sum l

-- DEF: appendix A's run.sh variant G2G (PHASE [1], the SPECIALISE line);
-- without it, variant GD.  ARG: Lib-arg.hs.  WW: Lib-ww.hs.
interp :: forall s a. (Num a, KnownS s) => a -> E s -> a
#if defined(WW)
{-# INLINE interp #-}
interp !env | Dict <- mkDict (sing @s) = \t -> winterp env t

-- The full-arity worker of the arity worker/wrapper split (GHC #19230):
-- recursive calls go through the inlined wrapper above.
winterp :: forall s a. (Num a, KnownS s) => a -> E s -> a
#if defined(DEF)
{-# INLINABLE [1] winterp #-}
{-# SPECIALISE interp :: KnownS s => Int -> E s -> Int #-}
#else
{-# INLINABLE winterp #-}
#endif
winterp !env = \case
#else
#if defined(DEF)
{-# INLINABLE [1] interp #-}
{-# SPECIALISE interp :: KnownS s => Int -> E s -> Int #-}
#else
{-# INLINABLE interp #-}
#endif
#if defined(ARG)
interp !env t | Dict <- mkDict (sing @s) = case t of
#else
interp !env | Dict <- mkDict (sing @s) = \case
#endif
#endif
  Lit n -> fromIntegral n
  Var -> env
  Add a b -> interp env a + interp env b
  I1 a ix -> interp env a + sumL (interp env <$> ix)
  I2 a ix -> interp env a * sumL (interp env <$> ix)
  I3 a ix -> interp env a - sumL (interp env <$> ix)
```

```haskell
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Ox (ListX(..), IxX(..), IxS(..)) where

newtype ListX i = ListX [i]

instance Functor ListX where
  {-# INLINE fmap #-}
  fmap f (ListX l) =
    let fmap' [] = []
        fmap' (x : xs) = let y = f x
                             rest = fmap' xs
                         in y `seq` rest `seq` (y : rest)
    in ListX (fmap' l)

newtype IxX i = IxX (ListX i) deriving Functor
newtype IxS i = IxS (IxX i) deriving Functor
```

```haskell
{-# LANGUAGE DataKinds #-}
import Lib
import Ox
import System.Environment (getArgs)
mk :: Int -> E 'F
mk 0 = Var
mk n = Add (mk (n - 1)) (if even n then Lit n else I1 (Lit 1) (IxS (IxX (ListX [Var, Lit 2]))))
go :: KnownS s => Int -> E s -> Int
{-# NOINLINE go #-}
go k e = interp k e
main :: IO ()
main = do
  [n] <- map read <$> getArgs
  print (sum [go k (mk 20) | k <- [1 .. n]])
```

`def`, `Lib.dump-simpl`: the SPECIALISE copy at arity 2 (`Lib.iface`), its self-call `lvl` and the `f` the index's `fmap` calls floated in front of the term lambda:

```
interp_$sinterp
  = \ @s $dKnownS env ->
      case env of env1 { I# ipv ->
      case $wmkDict (sing $dKnownS) of { (# #) ->
      let { f = interp_$sinterp (C:KnownS $WSP) env1 } in
```

```
      let { lvl = interp_$sinterp $dKnownS env1 } in
      \ ds ->
        case ds of {
```

```
  interp_$sinterp ::
    KnownS s => GHC.Internal.Types.Int -> E s -> GHC.Internal.Types.Int
  [HasNoCafRefs, TagSig: <TagFun[TagDunno]>,
   LambdaFormInfo: LFReEntrant 2, Arity: 2,
```

`defnofl`: nothing floated, and the same arity, the same `Lib.iface` lines:

```
interp_$sinterp
  = \ @s $dKnownS env ->
      case env of env1 { I# ipv ->
      case $wmkDict (sing $dKnownS) of { (# #) ->
      \ ds ->
        case ds of {
```

`defww`: the worker's specialisation has the full arity, the guard now inside the alternatives through the inlined wrapper:

```
$w$swinterp
  = \ @s $dKnownS ww eta ->
      case eta of {
```

```
  interp_$swinterp ::
    KnownS s => GHC.Internal.Types.Int -> E s -> GHC.Internal.Types.Int
  [TagSig: <TagFun[TagEPT]>, LambdaFormInfo: LFReEntrant 3, Arity: 3,
```

`imp`, `Main.iface`: the importer's copy at arity 3, and `impnoca`'s at 2:

```
  $sinterp ::
    Lib.KnownS s =>
    GHC.Internal.Types.Int -> Lib.E s -> GHC.Internal.Types.Int
  [TagSig: <TagFun[TagEPT]>, LambdaFormInfo: LFReEntrant 3, Arity: 3,
```

```
  $sinterp ::
    Lib.KnownS s =>
    GHC.Internal.Types.Int -> Lib.E s -> GHC.Internal.Types.Int
  [TagSig: <TagFun[TagDunno]>, LambdaFormInfo: LFReEntrant 2,
```

Bytes in the heap (the run's `+RTS -s` report, 200000 calls): `def` 956,858,408, `defnofl` 1,291,289,080, `defarg` 198,491,176, `defww` 192,091,192; `imp` 393,691,192, `impnoca` 739,258,424, `imparg` 198,491,192, `impww` 192,091,192. `measure.sh 100000`, a call of `go k (mk 20)`: `def` 4784 bytes and 9659 instructions, `defnofl` 6456 and 10102, `defarg` 992 and 4151, `defww` 960 and 4219; `imp` 1968 and 4776, `impnoca` 3696 and 8463, `imparg` 992 and 4311, `impww` 960 and 4219. `imp` against `imparg` has the shape of E15's float and merge, one `fmap'` above the case in the importer's copy, which, though eta-expanded in the end, met its first float-out with the lambda present (the third repro); its CSE was not dumped.

A second repro (`~/r/horde-ad/dist-inlcat/cases/E16-noinline-guard-call-arity`, variants `def`, `imp` and `defnofl`, the first repro's with `-ddump-call-arity` and, in place of the two suppression flags, `-dsuppress-uniques -dsuppress-module-prefixes -dsuppress-type-applications -dsuppress-coercions`; `deflam` and `deflamnofl`, `def` and `defnofl` with the element function written `\x -> interp env x`, by `-DLAM`): the first repro's program, `Lib.hs` gaining that switch in `interp`'s three index alternatives:

```haskell
#if defined(LAM)
  I1 a ix -> interp env a + sumL ((\x -> interp env x) <$> ix)
  I2 a ix -> interp env a * sumL ((\x -> interp env x) <$> ix)
  I3 a ix -> interp env a - sumL ((\x -> interp env x) <$> ix)
#else
  -- ... the three alternatives as in the first repro
#endif
```

In `def`'s Call Arity output the SPECIALISE copy is local and called with two arguments, `$sinterp [InlPrag=INLINABLE[1], Occ=LoopBreaker] :: forall (s :: Sp). KnownS s => Int -> E s -> Int [LclId, Arity=2, CallArity=2,`, its calls at `P` going through `f = $sinterp (C:KnownS $WSP) env } in letrec { fmap' [Occ=LoopBreaker] :: [E P] -> [Int]` (`defnofl`, whitespace collapsed), and the exported copy `interp_$sinterp` has `LFReEntrant 2, Arity: 2,`; with the lambda, `deflam` and `deflamnofl` give `CallArity=3,`; and the importer's copy in `imp`, `$sinterp [InlPrag=[~], Occ=LoopBreaker] :: forall (s :: Sp). KnownS s => Int -> E s -> Int [LclId, Arity=2, CallArity=3,`, calls at `P` a further specialisation, `case $sinterp_$sinterp env x of y { I# ipv ->`.

A third repro (`~/r/horde-ad/dist-inlcat/cases/E16-phase1-guard-routes-eta`, variants `imp`, appendix A's fmaprepro variant GD, each importer specialising; `def`, its variant G2G, the SPECIALISE pragma and `INLINABLE [1]`, by `-DDEF`; `imparg` and `defarg`, the argument form `interp !env t | ... = case t of`; `impnofl`, `imp` with `-fno-full-laziness`; `implib`, `imp` with `-fno-full-laziness` on `Lib` alone, by `-DLIBNOFL`; all at fmaprepro's flags `-O -fexpose-overloaded-unfoldings -fspecialise-aggressively -fdicts-cheap -fkeep-auto-rules`; `run` holds 200000): fmaprepro (`docs/ghc-issue-floatin-duplicate-values-appendix-a-programs.md`, section "Across modules") with its guard `mkDict` made `INLINE [1]` and `mkDict _ = Dict`, so that it is a call at the gentle pass and nothing once inlined, and the count of calls taken from the command line.

```haskell
{-# LANGUAGE LambdaCase, BangPatterns, DataKinds, GADTs, KindSignatures, RankNTypes, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes, CPP #-}
#if defined(LIBNOFL)
{-# OPTIONS_GHC -fno-full-laziness #-}
#endif
module Lib (E(..), Sp(..), KnownS(..), SSp(..), interp) where

import Ox

data Sp = F | P
data SSp (s :: Sp) where
  SF :: SSp 'F
  SP :: SSp 'P
class KnownS (s :: Sp) where sing :: SSp s
instance KnownS 'F where sing = SF
instance KnownS 'P where sing = SP

data Dict where Dict :: Dict
mkDict :: SSp s -> Dict
-- Inactive in the gentle pass that precedes the first specialisation and
-- float-out, inlined from phase 1 on.
{-# INLINE [1] mkDict #-}
mkDict _ = Dict

data E (s :: Sp) = Lit Int | Var | Add (E s) (E s)
  | I1 (E s) (IxS (E 'P)) | I2 (E s) (IxS (E 'P)) | I3 (E s) (IxS (E 'P))

sumL :: Num a => IxS a -> a
{-# INLINE sumL #-}
sumL (IxS (IxX (ListX l))) = sum l

-- DEF: a SPECIALISE copy made in this module, appendix A's variant G2G;
-- without it each importer specialises, variant GD.
interp :: forall s a. (Num a, KnownS s) => a -> E s -> a
#if defined(DEF)
{-# INLINABLE [1] interp #-}
{-# SPECIALISE interp :: KnownS s => Int -> E s -> Int #-}
#else
{-# INLINABLE interp #-}
#endif
#if defined(ARG)
interp !env t | Dict <- mkDict (sing @s) = case t of
#else
interp !env | Dict <- mkDict (sing @s) = \case
#endif
  Lit n -> fromIntegral n
  Var -> env
  Add a b -> interp env a + interp env b
  I1 a ix -> interp env a + sumL (interp env <$> ix)
  I2 a ix -> interp env a * sumL (interp env <$> ix)
  I3 a ix -> interp env a - sumL (interp env <$> ix)
```

`Main` and `Ox` are the first repro's.

Both routes' copies, right after Specialise, keep the guard as a call and the lambda. `imp`, `Main.dump-spec`:

```
$sinterp
  = \ @s $dKnownS env ->
      case env of env1 { __DEFAULT ->
      case mkDict (sing $dKnownS) of { Dict ->
      \ ds ->
```

`def`, `Lib.dump-spec`, the copy at `Int`:

```
$sinterp
  = \ @s $dKnownS env ->
      case env of env { I# ipv ->
      case mkDict (sing $dKnownS) of { Dict ->
      \ ds ->
```

`imp`, `Lib.dump-simpl`: the defining module's own `interp` has lost the guard but not the first float-out's floats, `let { f = interp_$sinterp $dNum env1 } in` and the index sum's zero, `let { lvl = fromInteger $dNum interp1 } in`, and stays at arity 3 (`Lib.iface`), so the late float-out, which floats over-saturated calls (`floatOutOverSatApps`, [compiler/GHC/Core/Opt/Pipeline.hs#L274][g341]), floats its direct self-call too; its INLINABLE unfolding keeps the phase-1 guard as a call and the lambda:

```
      let { lvl1 = interp $dNum $dKnownS env1 } in
      \ ds ->
```

```
  interp :: (GHC.Internal.Num.Num a, KnownS s) => a -> E s -> a
  [HasNoCafRefs, TagSig: <TagFun[TagDunno]>,
   LambdaFormInfo: LFReEntrant 3, Arity: 3,
```

```
                            case env of env1 { DEFAULT ->
                            case mkDict @s (sing @s $dKnownS) of wild { Dict ->
                            \ (ds['GHC.Internal.Types.Many] :: E s) ->
```

`impnofl`, `Lib.iface`: with no float-out, `interp` reaches arity 4 once the guard is gone, and its INLINABLE unfolding is eta-expanded to it (E06), the guard still a call in it:

```
  interp :: (GHC.Internal.Num.Num a, KnownS s) => a -> E s -> a
  [HasNoCafRefs, TagSig: <TagFun[TagDunno]>,
   LambdaFormInfo: LFReEntrant 4, Arity: 4,
```

```
                              (eta['GHC.Internal.Types.Many] :: E s) ->
                            case env of env1 { DEFAULT ->
                            case mkDict @s (sing @s $dKnownS) of wild { Dict ->
                            case eta of wild1 {
```

`implib`, `Main.dump-spec`: the importer's copy right after Specialise, from the eta-expanded unfolding, the form horde-ad's notes record for its importer:

```
$sinterp
  = \ @s $dKnownS env eta ->
      case env of env1 { __DEFAULT ->
      case mkDict (sing $dKnownS) of { Dict ->
      case eta of {
```

Bytes in the heap (the run's `+RTS -s` report, 200000 calls): `imp` 262,491,176, `def` 198,491,176, `imparg` and `defarg` 198,491,176, `impnofl` 953,689,080, `implib` 198,491,176: here the importer's route is the one that loses, the reverse of horde-ad's; `impnofl` turns full laziness off in both modules, so its figure separates nothing. With fmaprepro's own `NOINLINE` guard, in the first repro, the importer's route allocates 393,691,192 and the defining module's 956,858,408.

A fourth repro (`~/r/horde-ad/dist-inlcat/cases/E16-imported-guard-gentle-pass`, variants `impg` and `defg`, the third repro's `imp` and `def` with the guard `mkDictG` imported from `G`, horde-ad's form, by `-DGUARDIMP`; `impgne` and `defgne`, the same with no `error` alternative, by `-DNOERR`; `impgps`, `impg` with `-fpolymorphic-specialisation`; all at fmaprepro's flags and with `-ddump-float-out`; `run` holds 200000): the third repro's `Lib` with `interp` taking a `Show` constraint too and its guard written `GUARD`:

```haskell
-- ...
#if defined(GUARDIMP)
#define GUARD mkDictG (Proxy @a) (sing @s)
#else
#define GUARD mkDict (sing @s)
#endif
module Lib (E(..), Sp(..), KnownS(..), SSp(..), interp) where
-- ...
interp :: forall s a. (Num a, Show a, KnownS s) => a -> E s -> a
-- ...
interp !env | Dict <- GUARD = \case
-- ...
```

`mkDictG` comes from:

```haskell
{-# LANGUAGE CPP, LambdaCase, DataKinds, GADTs, KindSignatures, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes #-}
module G (Sp(..), SSp(..), KnownS(..), Dict(..), mkDictG) where

import Data.Proxy

data Sp = F | P | Q Sp
data SSp (s :: Sp) where
  SF :: SSp 'F
  SP :: SSp 'P
  SQ :: SSp s -> SSp ('Q s)
class KnownS (s :: Sp) where sing :: SSp s
instance KnownS 'F where sing = SF
instance KnownS 'P where sing = SP
instance KnownS s => KnownS ('Q s) where sing = SQ (sing @s)

data Dict where Dict :: Dict

mkDictG :: (Num a, Show a) => Proxy a -> SSp s -> Dict
{-# INLINE mkDictG #-}
mkDictG _ = \case
  SF -> Dict
  SP -> Dict
  SQ SF -> Dict
#if defined(NOERR)
  SQ _ -> Dict
#else
  SQ _ -> error "mkDictG: nested"
#endif
```

In `defg`'s specialiser output the SPECIALISE copy holds the guard inlined, its lambda behind it, `$sinterp = \ @s $dKnownS env -> case env of env { I# ipv -> case case sing $dKnownS of {` (whitespace collapsed), where `defgne`'s is eta-expanded, `$sinterp = \ @s $dKnownS env eta ->`; the defining module's own `interp` ends with `LambdaFormInfo: LFReEntrant 4, Arity: 4` in `impg` and `impgps`, and `LFReEntrant 5, Arity: 5` in `impgne`, the first float-out having floated `let { f = interp $dNum $dShow (C:KnownS $WSP) env } in` (`impg`). Bytes in the heap: `impg` 262,491,176, `impgne` and `defg` 198,491,176.

A fifth repro (`~/r/horde-ad/dist-inlcat/cases/E16-zero-free-sum-full-arity`, variants `imp` and `def`, the third repro's; `impnz` and `defnz`, the same with the index sum started from its first element, by `-DNOZERO`; `impargnz` and `defargnz`, their argument forms; `impsame` and `impsamenz`, `imp` and `impnz` with the index elements at the term's own span, by `-DSAMES`, so that no specialisation at `P` is made; all at fmaprepro's flags, all but the argument forms with `-dverbose-core2core -ddump-simpl-iterations`; `run` holds 200000): the third repro's `Lib` without its `LIBNOFL` switch and with two more:

```haskell
module Lib (E(..), Sp(..), KnownS(..), SSp(..), interp) where

import qualified Data.List as L
-- ...
#if defined(SAMES)
data E (s :: Sp) = Lit Int | Var | Add (E s) (E s)
  | I1 (E s) (IxS (E s)) | I2 (E s) (IxS (E s)) | I3 (E s) (IxS (E s))
#else
-- ... E as in the third repro
#endif
-- ...
#if defined(NOZERO)
sumL (IxS (IxX (ListX (x : xs)))) = L.foldl' (+) x xs
#else
sumL (IxS (IxX (ListX l))) = sum l
#endif
```

In `imp` the specialisation at `P`, `$sinterp [InlPrag=INLINABLE] :: forall a. Num a => a -> E P -> a`, has `Arity=2` after every pass, its phase 2 output binding `f = $sinterp @a $dNum env` and ending its prefix with `lvl = fromInteger @a $dNum lvl } in case env of env { __DEFAULT -> case lvl of { Dict -> \ (ds :: E P) ->`. In `impnz` the first float-out still floats `f = interp @P @a $dNum (Lib.C:KnownS @P Lib.$WSP) env` in front of `interp`'s guard and lambda, and no zero. In phase 2's first iteration the specialisation reads `$sinterp = \ (@a) ($dNum :: Num a) (env :: a) (eta :: E P) ->` and `interp`'s loops call it, `case $sinterp @a $dNum env x of y`, the simplifier's trace reading `PostInlineUnconditionally f $sinterp @a $dNum env`; the specialisation's own loops call it from the second iteration. `interp` keeps arity 3 behind `case mkDict @s (sing @s $dKnownS) of { Dict -> \ (ds :: E s) ->` until phase 1's first iteration, which has no guard and `Arity=4`, the unfolding eta-expanded with it (`LFReEntrant 4, Arity: 4` in `Lib.iface`); the importer's copy right after Specialise reads `$sinterp = \ (@(s :: Sp)) ($dKnownS :: KnownS s) (env [Occ=Once1] :: Int) (eta [Occ=Once1!] :: E s) ->`. In `def` and `defnz` the SPECIALISE copy meets the first float-out with `f = interp @P @Int GHC.Internal.Num.$fNumInt (Lib.C:KnownS @P Lib.$WSP) env` in front of its guard and lambda, and from phase 1 both copies at `Int`, the SPECIALISE copy and one the specialiser adds under the rule `SPEC interp @_ @Int`, have `Arity=3`, their loops calling `$sinterp @P (Lib.C:KnownS @P Lib.$WSP) env x`; at `Int` the zero is a top-level binding. `impsame` keeps `interp` at arity 3 with `f = interp @s @a $dNum $dKnownS env` and `lvl = fromInteger @a $dNum lvl` in front of its lambda; `impsamenz` reaches arity 4 in phase 1 with the same `f` floated by the first float-out and still bound after phase 2. Bytes in the heap: `imp` 262,491,176; `impnz`, `def`, `defnz`, `impargnz` and `defargnz` 198,491,176; `impsame` and `impsamenz` 214,491,176.

**Reproduces small:** in part: the guard that is not cheap, yes, the documents' program, with their figures (957, 394, 198 and 192 MB); the "self-reinforcing" reading of the notes, that the floated self-call is what blocks the eta-expansion, does not hold for this program: without full laziness the arity is the same. The two routes, in part: the importer's half, with full laziness off in `Lib` (`implib`) or the index sum's zero removed (the fifth repro); the defining module's half, and so horde-ad's direction, no. Tried: fmaprepro as filed (`NOINLINE mkDict`, the first repro), where neither route's copy is eta-expanded before the first float-out; and the guard `INLINE [1]`, first with `mkDict SF = Dict; mkDict SP = Dict`, then with `mkDict _ = Dict` (the third repro), where the defining module's `interp` still keeps arity 3, held by the index sum's zero as the Rule says (with `-fno-full-laziness` it reaches 4 and its unfolding is eta-expanded, variant `impnofl`), so its unfolding is not eta-expanded and both routes start alike. With full laziness off in `Lib` alone (`implib`) the importer's half of horde-ad's observation reproduces: its copy starts eta-expanded and allocates as the argument form does; but then `Lib`'s own SPECIALISE copy meets no float-out either, so the defining module's half, the copy that loses, needs a `Lib` whose own binding reaches full arity in spite of its first float-out. Without the zero (the fifth repro) `Lib` has one, by horde-ad's steps: the first float-out floats the partial self-call, phase 2's first iteration eta-expands the specialisation at `P` that it calls and inlines it, and `interp`, held by its guard where horde-ad's is held by a dictionary binding, reaches arity 4 in phase 1. But the SPECIALISE copy, at `Int`, reaches its full arity in phase 1 too, with the zero or without it, and allocates as the argument forms do, as the importer's copy does here: neither route loses. The session notes of the comment's appendix D record that an always active INLINE guard (their fmapdef) lets the gentle pass eta-expand both copies; so it does in the fourth repro, unless the guard has an `error` alternative, as horde-ad's `dictSpanFam` has, which keeps the lambda in both copies, the importer's route still the one that loses. In horde-ad's own `AstInterpret` (4b2ad4979 under HEAD, per-pass dumps of that module alone) the first float-out does float three copies of the partial self-call, `f = interpretAst @target @PlainSpan @(TKScalar Int) $dCTuple2 (C:KnownSpan @PlainSpan $WSPlainSpan) nt`, in front of the term lambda. The phase 2 simplifier then makes each a call of the `PlainSpan` specialisation, which reaches its full arity in that run's first iteration, and inlines them in its second. What then keeps `interpretAst` at arity 3 through phase 0 is the `KnownSpan (PrimalStepSpan s)` dictionary the desugarer binds in front of the term lambda: after the gentle pass `$WSPrimalStepSpan @s (knownSpan @s $dKnownSpan)` at type `SAstSpan (PrimalStepSpan s)`, cheap neither for `isCheapApp` nor for `-fdicts-cheap`, and the only binding in front of the lambda that is not cheap. The first final-phase simplifier inlines that wrapper (A25) and eta-expands to arity 4. That simplifier is `post-call-arity`, where Call Arity's `CallArity=4` also marks the new term binder one-shot, or, with `-fno-call-arity`, `post-worker-wrapper`, where the worker has neither call arity nor demand info and its new term binder no one-shot mark.

### E17. Inlining an entry point puts its loop-invariant work into the caller, where full laziness floats it out of the caller's loop; called out of line, the work is redone every iteration

**Rule.** Full laziness floats an expression that is not a head normal form out of a value lambda when its free variables allow it ([compiler/GHC/Core/Opt/SetLevels.hs#L701][g328], `lvlMFE`, `saves_work`), to the top level when it has no local free variables ([SetLevels.hs#L1592][g342], `destLevel`), but it floats only what the caller's own Core shows. A function called out of line keeps its work inside its body, so a part of that work that depends only on the arguments fixed across a caller's loop is redone at every call. Inlined, the same work becomes an expression of the caller, under the loop's lambda and free of the loop's variable, and is computed once. A function without a pragma and bigger than its call is inlined only where some argument or the context is interesting ([compiler/GHC/Core/Opt/Simplify/Inline.hs#L323][g40], `is_wf, some_benefit, small_enough`; A03), which an entry point applied to a function and an input rarely gives; INLINE takes the unfolding as written at any saturated call with something to gain (U03). The pragma-free alias `vjp2 = revMaybeDt` is not transparent when its constraint differs from the aliased function's: it grows to the INLINE body, as `none`'s guidance below shows, and is then a big function without a pragma. With the aliased function's own constraints the alias is transparent while they are classes, `vjp2 = revMaybeDt` after desugaring, but not with an equality among them: a given equality is replaced by its coercion and a wanted one is solved as a new `Eq#` (`solveEqualityDict`, [compiler/GHC/Tc/Solver/Dict.hs#L568][g343]; (EQC1) in Note [Solving equality classes], [#L494][g344]), so the alias desugars to a body rebuilding the evidence, and worker/wrapper gives it a wrapper's unfolding (second repro).

**Seen.** `docs/pragmas-and-flags.md` in horde-ad, section "What stays, and why", the first row of its table: `grad2`, `vjp2`, `jvp2` in `ADEngine` keep INLINE, since without it `pitfalls/S-fullpipe-hoisted` takes 67% longer, "full laziness no longer hoists the artifact out of the loop"; commit 0a8d839b3, "Drop 165 inlining and specialisation pragmas and -flate-dmd-anal" ("grad2, vjp2 and jvp2 keep theirs"). The benchmark is `bench/ConvVjpBench.hs`'s `S-fullpipe-hoisted-6x6`, `whnf (forceGrad . vjp f6 arrK) arrB6`, whose comment says the artifact does not depend on the cotangent, so full laziness floats its construction out of the timed loop.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/E17-inline-exposes-hoistable-work`, variants `inline`, `vjp2` INLINE by `-DINL`; `none`, without a pragma; `nonemono`, without a pragma and with `vjp`, `vjp2` and `revMaybeDt` monomorphic at `Double`, by `-DMONO`; `run` holds 100000): horde-ad's chain reduced to its pragmas, `vjp` INLINE over `vjp2 = revMaybeDt`, `revMaybeDt` INLINE over an expensive NOINLINE `build` of the artifact from the objective and the input, and the cotangent varying in a loop called out of line, as criterion's `whnf` is.

```haskell
{-# LANGUAGE BangPatterns, CPP #-}
module Lib (Art (..), build, revMaybeDt, vjp2, vjp) where

-- The artifact: what the derivative program would be, here two numbers.
data Art r = Art !r !r

-- Building the artifact is the expensive part, and depends on the objective
-- and the input, not on the cotangent.
build :: Floating r => (r -> r) -> r -> Art r
{-# NOINLINE build #-}
build f x = go (0 :: Int) 0
  where
    go !i !acc | i == 1000 = Art (f x) acc
               | otherwise = go (i + 1) (acc + f (x + fromIntegral i))

-- As horde-ad's revMaybeDt: build the artifact, then interpret it on the
-- cotangent; a body too big to inline without a pragma, as horde-ad's is.
#if defined(MONO)
revMaybeDt :: (Double -> Double) -> Double -> Double -> (Double, Double)
#else
revMaybeDt :: (Floating r, Ord r) => (r -> r) -> r -> r -> (r, r)
#endif
{-# INLINE revMaybeDt #-}
revMaybeDt f x dt = case build f x of
  Art p d -> (p, interp (0 :: Int) dt)
    where
      interp !i !acc
        | i == 8 = acc
        | acc > 1e6 = interp (i + 1) (acc / d - p)
        | acc < -1e6 = interp (i + 1) (acc * d + p)
        | even i = interp (i + 1) (acc * d + p * dt)
        | otherwise = interp (i + 1) (acc - d / (1 + p * p))

-- As horde-ad's vjp2 and vjp: vjp2 an alias, here with a constraint that
-- differs from revMaybeDt's, given INLINE by INL; MONO makes the
-- two monomorphic instead.
#if defined(MONO)
vjp2 :: (Double -> Double) -> Double -> Double -> (Double, Double)
#else
vjp2 :: RealFloat r => (r -> r) -> r -> r -> (r, r)
#endif
#if defined(INL)
{-# INLINE vjp2 #-}
#endif
vjp2 = revMaybeDt

#if defined(MONO)
vjp :: (Double -> Double) -> Double -> Double -> Double
#else
vjp :: RealFloat r => (r -> r) -> r -> r -> r
#endif
{-# INLINE vjp #-}
vjp f x dt = snd (vjp2 f x dt)
```

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where
import Lib
import System.Environment (getArgs)

g :: Double -> Double
g y = y * y + 1

-- As criterion's whnf: the function applied n times, called out of line.
loop :: (Double -> Double) -> Int -> Double
{-# NOINLINE loop #-}
loop h n = go 0 0
  where
    go !i !acc | i == n = acc
               | otherwise = go (i + 1) (acc + h (fromIntegral i))

main :: IO ()
main = do
  [n] <- map read <$> getArgs
  print (loop (negate . vjp g 3) n)
```

`inline`, `build.log` (`-dinline-check vjp2`), the decision in `Lib`, at `vjp`'s call, whitespace collapsed to one line:

```
Considering inlining: vjp2 arg infos [TrivArg, TrivArg, TrivArg, TrivArg] interesting continuation BoringCtxt some_benefit True is exp: True is work-free: True guidance ALWAYS_IF(arity=1,unsat_ok=False,boring_ok=False) case depth = 0 inline depth = 1 ANSWER = YES
```

`inline`, `Main.dump-simpl`: the artifact built once at the top level, the loop's function using it:

```
main3
  = case $wbuild $fFloatingDouble main5 main4 of { (# ww, ww1 #) ->
    Art ww ww1
```

```
main2
  = \ x ->
      case main3 of { Art p d ->
```

`none`, the same decision, and the worker called, the artifact built, for every element:

```
Considering inlining: vjp2 arg infos [TrivArg, TrivArg, TrivArg, TrivArg] interesting continuation BoringCtxt some_benefit False is exp: True is work-free: True guidance IF_ARGS [60 0 0 0] 140 0 case depth = 0 inline depth = 1 depth based penalty = 0 adjusted size = 90 ANSWER = NO
```

```
main2
  = \ x ->
      case $wvjp2 $fRealFloatDouble g main3 x of { (# _, ww1 #) ->
```

Bytes in the heap (the run's `+RTS -s` report, 100000 elements): `inline` 6,716,192, `none` 20,092,916,440, `nonemono` 6,716,192. `measure.sh 20000`, an element of the loop: `inline` 64 bytes and 238 instructions, `none` 200928 bytes and 313750 instructions.

A second repro (`~/r/horde-ad/dist-inlcat/cases/E17-alias-same-constraints`, variants `same`, with `-dinline-check vjp2`; `sameeq`, `same` with two equalities among the constraints, of horde-ad's two kinds, by `-DEQS`; `sameeqinl`, `sameeq` with `vjp2` INLINE; `sameeqh`, `sameeq` at horde-ad's flags `-fexpose-overloaded-unfoldings -fspecialise-aggressively -fpolymorphic-specialisation -fkeep-auto-rules -fdicts-cheap`; `sameds` and `sameeqds`, `same` and `sameeq` with `-ddump-ds`, the desugarer's output; `Main` and `run` are the first repro's): the first repro's `Lib` with one constraint and objective type for `revMaybeDt`, `vjp2` and `vjp`.

```haskell
{-# LANGUAGE BangPatterns, CPP, TypeFamilies #-}
module Lib (Art (..), build, revMaybeDt, vjp2, vjp, X, Value) where

type family X a
type instance X Double = Int
type family Value a
type instance Value Double = Double

-- ... Art and build as in the first repro

#if defined(EQS)
#define CTX (X r ~ X (Value r), Floating r, Ord r, t ~ r)
#define OBJ (r -> t)
#else
#define CTX (Floating r, Ord r)
#define OBJ (r -> r)
#endif

revMaybeDt :: CTX => OBJ -> r -> r -> (r, r)
{-# INLINE revMaybeDt #-}
-- ... its body as in the first repro

vjp2 :: CTX => OBJ -> r -> r -> (r, r)
#if defined(INL)
{-# INLINE vjp2 #-}
#endif
vjp2 = revMaybeDt

vjp :: CTX => OBJ -> r -> r -> r
{-# INLINE vjp #-}
vjp f x dt = snd (vjp2 f x dt)
```

With class constraints alone, `sameds` desugars `vjp2 = revMaybeDt` and `same`'s `Lib.iface` gives it `Unfolding: Core: <vanilla> revMaybeDt]`. With the equalities, `sameeqds` desugars ``vjp2 = \ @r @t $d~ $dFloating $dOrd $d~ -> case eq_sel $d~ of co { __DEFAULT -> case eq_sel $d~ of co { __DEFAULT -> revMaybeDt ((Eq# @~<Co:2>) `cast` <Co:5>) $dFloating $dOrd ((Eq# @~<Co:1>) `cast` <Co:5>)`` (whitespace collapsed), and `sameeq`'s interface gives it `Unfolding: Core: StableSystem <7,TrueFalse>`; it is still inlined into `vjp`, at `guidance IF_ARGS [30 0 0 30 0 0 0] 140 0` and `adjusted size = 0`, and every variant allocates 6,716,192 bytes, the artifact hoisted.

**Reproduces small:** yes, the mechanism; the size of horde-ad's +67% depends on how much of a call the artifact is, here nearly all of it. With the three monomorphic (`nonemono`), `vjp2`'s unfolding is `revMaybeDt` itself (`Unfolding: Core: <vanilla> revMaybeDt]` in `Lib.iface`), and that trivial unfolding is inlined at every call (A02; `build.log`: `guidance ALWAYS_IF(arity=0,unsat_ok=True,boring_ok=True)`, `ANSWER = YES`), so the artifact is hoisted without the pragma (`main3` as in `inline`; 6,716,192 bytes). horde-ad's `vjp2` and `revMaybeDt` carry the same five constraints, two of them equalities (`X src ~ X (Value src)` and `tgt ~ AstTensor AstMethodLet FullSpan ztgt`), the case of the second repro, where the alias is inlined all the same, its `Eq#` arguments counting as values; that horde-ad's bigger body defeats those discounts is not measured.

### E18. A strict-field constructor built from fields the tag inference does not prove evaluated becomes, under a lazy constructor, a thunk of its fields, as when they come from a worker returning through a nullary join point

**Rule.** After Core, the STG rewrite of tag inference upholds the invariant that a strict field holds an evaluated, tagged pointer. A constructor bound by a `let`, as the argument of a lazy constructor is, whose argument to a strict field is not known tagged is turned into an updatable closure that evaluates those arguments and then builds the constructor (`rewriteRhs`, the `StgRhsCon` case, [compiler/GHC/Stg/EnforceEpt/Rewrite.hs#L332][g345]: "we convert the RHS into a RhsClosure which will evaluate the arguments before allocating the constructor", marked `Updatable`); Core shows the constructor, the thunk appears only in STG. Its size is a thunk's header, two words (`thunkHdrSize`, [compiler/GHC/Runtime/Heap/Layout.hs#L366][g346]), plus one word a free variable: 40 bytes for three fields, against 32 for the constructor `T` itself and 24 for a thunk of the call holding its input alone. Fields returned in an unboxed tuple by a worker are known tagged only through the worker's tag signature: a saturated call's result gets the callee's `TagFun` return information, and `TagDunno` when there is none (`inferTagExpr`, the `StgApp` case, [compiler/GHC/Stg/EnforceEpt.hs#L403][g347]). Where the worker's signature records its components tagged, the client rebuilds the constructor directly, `T!`, with no thunk. A jump to a nullary join point is an application of arity 0, which `inferTagExpr` gives `TagDunno` before it looks up the join point's return information ([compiler/GHC/Stg/EnforceEpt.hs#L417][g348], before [#L426][g349]), though Note [TagInfo of functions] ([#L263][g350]) says that such information flows through. And one `TagDunno` alternative makes the whole result `TagDunno` (`combineAltInfo`, [compiler/GHC/Stg/EnforceEpt/Types.hs#L48][g351]); so a worker that returns through a nullary join point gets `TagFun[TagDunno]` whatever the join point returns.

**Seen.** Orthotope's benchmark, by ticky: boxed Shaped `convertE`'s `lvl3155` allocating "72 bytes a call at the tip, 88 in CV", CV's being "`Right` 16 and `T` 32, plus 40 bytes the Core does not show"; and CV's `-ddump-stg-final` of `OpsShaped`. That dump has `lvl3155` call `OpsShaped.$w$s$w$cconvert17 GHC.Internal.Prim.coercionToken# lvl391 ww ww1 ww3 ww4 ww5`, take `(#,,#) ww6 ww7 ww8`, and bind `lvl3155_sat :: ... = {ww6, ww7, ww8} \u [] case ww6 of ww6 { __DEFAULT -> case ww8 of ww8 { __DEFAULT -> Data.Array.Internal.T [ww6 ww7 ww8]; }; }` before returning `GHC.Internal.Data.Either.Right [lvl3155_sat]`. The worker's three tuple returns hand back case binders and a `let`-bound constructor, tagged inside it, but its signature does not record them: CV's `OpsShaped.dump-stg-tags` gives `(OpsShaped.$w$s$w$cconvert17, <TagFun[TagDunno]>)`, its loop `$wgo28`, `<TagFun[TagDunno]>` too, returning through a nullary join point, `$j15`, whose own signature is `<TagFun[TagTuple[TagEPT, TagEPT, TagEPT]]>`, by `1# -> $j15;` and `0# -> $j15;`. These are U11's 16 bytes: the strict default `convertE x = Right $! convert x` replaced the tip's 24-byte thunk of the call by this 40-byte one. And orthotope's `INLINE throughout:` comment heading `DynamicG` (at "Take the vector strict in the boxed and Unboxed vToList") records that under INLINE "rev allocates 32 bytes a call more forced at the small and empty sizes and 8 fewer summed, and rotate 48 fewer in both readings", reading the cost as this rule's: "inlined into a client, it gets a local worker there, which returns the strides, offset and vector untagged, and GHC builds the strict-field T over them as a thunk, which it forces at once"; that reading is not reproduced small.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/E18-tag-inference-thunk`, variant `base` with `-ddump-stg-final`; `run` is `lazy 100000`; `measure.sh N`): U11's two defaults written at a conversion whose worker returns a strict-field view's fields; `~/r/horde-ad/dist-inlcat/cases/E18-tag-inference-thunk/tried/` holds the other shapes tried.

```haskell
{-# LANGUAGE BangPatterns #-}
-- U11's conversion, cut down: a view with strict fields, as orthotope's T.
module Lib (module Lib) where

data V = V [Int] | VNone

-- Strides, offset, vector; the offset unpacked by -O.
data T = T ![Int] !Int !V

-- The conversion, out of line: its worker returns T's fields unboxed.
{-# NOINLINE convert #-}
convert :: [Int] -> T
convert xs = T (map (* 2) xs) (length xs) (V (reverse xs))

-- U11's two defaults, written at the instance: lazy and strict.
convertE :: [Int] -> Either String T
convertE xs = Right (convert xs)

convertES :: [Int] -> Either String T
convertES xs = Right $! convert xs
```

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import Lib
import System.Environment (getArgs)

-- Opaque, so that each iteration converts anew.
{-# OPAQUE pass #-}
pass :: Int -> a -> a
pass _ x = x

main :: IO ()
main = do
  [what, repss] <- getArgs
  let reps = read repss :: Int
      f = if what == "lazy" then convertE else convertES
      xs = [1, 2, 3] :: [Int]
      loop :: Int -> Int -> Int
      loop 0 !acc = acc
      loop r !acc = case f (pass r xs) of
        Right (T _ o _) -> loop (r - 1) (acc + o)
        Left _ -> acc
  print (loop reps 0)
```

`Lib.dump-stg-final`: the lazy default `let { convertE_sat = \u [] convert xs; } in Right [convertE_sat];`, the strict one `let { convertES_sat = T! [ww ww1 convertES_sat]; } in Right [convertES_sat];` (whitespace collapsed), the worker's signature in `Lib.iface` being `TagSig: <TagFun[TagTuple[TagEPT, TagEPT, TagDunno]]>`, its third component `V`'s lazy field after nested CPR. By `measure.sh 100000` (100000 and 200000 conversions differenced, twice, the same figures): lazy 243.2 instructions and 240.0 bytes a call, strict 212.8 and 216.0, the strict default here saving the 24-byte thunk where in CV it cost 16 bytes.

A second repro (`~/r/horde-ad/dist-inlcat/cases/E18-nullary-join-tag`, variants `nullary` and `arg`, `-DARG`, both with `-ddump-stg-final -ddump-stg-tags`; `run` is `lazy 100000`; `measure.sh N`): the first repro's conversion with its result built in a binding used at two tail positions, which the simplifier makes a join point, nullary as written or, with `ARG`, taking an argument.

```haskell
{-# LANGUAGE BangPatterns, CPP #-}
module Lib (module Lib) where

data V = V [Int] | VNone

data T = T ![Int] !Int !V

{-# NOINLINE convert #-}
convert :: [Int] -> T
#if defined(ARG)
convert xs = case xs of
  [] -> big 2
  y : ys | y > 0 -> T ys y (V xs)
         | y < -5 -> big 3
         | otherwise -> T xs 0 VNone
  where big k = T (map (* k) xs) (length xs) (V (reverse xs))
#else
convert xs = case xs of
  [] -> big
  y : ys | y > 0 -> T ys y (V xs)
         | y < -5 -> big
         | otherwise -> T xs 0 VNone
  where big = T (map (* 2) xs) (length xs) (V (reverse xs))
#endif

convertE :: [Int] -> Either String T
convertE xs = Right (convert xs)

convertES :: [Int] -> Either String T
convertES xs = Right $! convert xs
```

`Main` converts a three-element list in a loop, by `convertE` or `convertES` as its first argument says. The join point's signature is a tuple's in both variants, `(big, <TagFun[TagTuple[TagEPT, TagEPT, TagEPT]]>) = \j []` in `nullary` and `(big, <TagFun[TagTuple[TagEPT, TagEPT, TagEPT]]>) = \j [(k, <TagVal[TagDunno]>)]` in `arg`, but the worker reaches the nullary one by `[] -> big;` and gets `TagSig: <TagFun[TagDunno]>`, against `TagSig: <TagFun[TagTuple[TagEPT, TagEPT, TagEPT]]>` in `arg`; so the strict default builds a thunk, `convertES_sat = \u [] case ww of ww { __DEFAULT -> case ww2 of ww2 { __DEFAULT -> T [ww ww1 ww2]; }; };`, in `nullary`, and the constructor, `let { convertES_sat = T! [ww ww1 ww2]; } in Right [convertES_sat];`, in `arg` (whitespace collapsed). By `measure.sh 100000`, the strict default runs 183.1 instructions and 144.0 bytes a call in `nullary` against 135.8 and 104.0 in `arg`, the 40 bytes CV's.

**Reproduces small:** yes, by the second repro. The first repro's shapes did not, each read in `-ddump-stg-final` by hand (their notes in that directory, the dumps not kept): the defaults beside the conversion (above); a client module calling the imported worker, which evaluated the fields by a `case` outside the `let`; a conversion passing a field of its argument through (`T s o v` to `T (reverse s) (o + 1) v`), its worker's signature recording all three components tagged; fields chosen by branches and joined before the constructor; and the worker behind a given equality, called with a coercion token as CV's is. Each built `T` as a constructor, with no thunk.

### E19. Call Arity gives an unexported specialisation the arity of its one caller's call, so a wrapper naming its arguments moves an INLINABLE body's checks inside the lambdas, where a client runs them at every call instead of floating them to constants

**Rule.** Call Arity counts only exported binders as called from outside the module (`callArityTopLvl`, [compiler/GHC/Core/Opt/CallArity.hs#L441][g352], its `isExportedId` filter at [#L449][g308]). A specialisation that the specialiser makes in the defining module is a local binder, not exported, which importers reach only through its rule, so it gets the call arity of its one caller in the module, and `findRhsArity` makes that many of its lambdas one-shot (`useSiteCallCards`, [compiler/GHC/Core/Opt/Arity.hs#L986][g302], used at [#L928][g303]; `combineWithCallCards`, [#L960][g304]), so that an expensive `let` before them no longer cuts the arity (E08, E11). Demand analysis takes a binder free in a rule's right-hand side for a root of unknown use (`is_root`, [compiler/GHC/Core/Opt/DmdAnal.hs#L116][g353]), but `useSiteCallCards` keeps the longer of its two lists of cards (`zip_cards`, [compiler/GHC/Core/Opt/Arity.hs#L1010][g354]), so Call Arity's decides. The specialised right-hand side keeps every lambda of the template (`spec_rhs = mkLams spec_rhs_bndrs ...`, [compiler/GHC/Core/Opt/Specialise.hs#L1716][g355]), and an INLINABLE function whose arity is its dictionaries alone has its value lambdas after the `let`s that need only the dictionaries, here the checks on the padding and the shape. Called by a point-free wrapper, `pad v = A . G.pad @ps v . unA`, with one value argument, the specialisation `$spad` gets call arity 4, its three dictionaries and `v`; the checks stay `let`s before the array's lambda, and a client's further specialisation, its dictionaries known, floats them to top-level constants evaluated once. Called by a wrapper naming the array, `pad v a = A (G.pad @ps v (unA a))`, it gets 5, the array's lambda one-shot too, and the checks end up inside both lambdas, as loops whose exits jump to join points: the Simplifier run after Call Arity (`simplify "post-call-arity"`, [compiler/GHC/Core/Opt/Pipeline.hs#L257][g356]) eta-expands `$spad` to that arity (`tryEtaExpandRhs`, [compiler/GHC/Core/Opt/Simplify/Utils.hs#L2167][g357]), and its output has the checks' `let`s inside the new lambdas, where Call Arity's output has them before the lambdas (`~/r/horde-ad/dist-inlcat/cases/E19-eta-moves-checks`). A client's copy keeps the loops in its body, where they mention per-call join points, which SetLevels does not float (O13). With `-fno-call-arity` the named form compiles as the point-free one (variant `nca` of `~/r/horde-ad/dist-inlcat/cases/E19-call-arity-spec-checks`). The join point that tests the call stack, `case ip $dIP of wild1 { ...; FreezeCallStack ... }`, is reached only by a failing check.

**Seen.** Orthotope's eta pass over the wrapper modules, wrap, naming the wrappers' arguments, against the candidate "Inline the axis comparator and its tie-break into the sort", Shaped boxed `pad.none` at the strided view, 229 instructions a call more. In wrap's `OpsShaped.dump-simpl` the row calls `OpsShaped.$s$spad1`, which opens with `join { $j14 = case ip $dIP69 of wild1 { __DEFAULT -> lvl3612 wild1; FreezeCallStack ds37 -> lvl3613 wild1 } } in`, a join point only the overflow check's failure jumps to, and runs the checks as loops, `jump go48 lvl3496 ...`; the candidate's opens with `case lvl3612 ... of { False -> case lvl3610 of { I# v4 ->`, its checks top-level constants such as `lvl3612 = $spad_go lvl3497 $s$wsumA_sh2` (qualifiers dropped, whitespace collapsed). The interfaces of orthotope's Shaped give the library's `$spad` `Arity: 5` at the candidate, its last lambda one-shot, and `Arity: 6` at wrap, its last two.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/E19-call-arity-spec-checks`, variants `pf`, the wrapper point-free; `named`, naming the array, by `-DNAMED`; `nca`, `named` with `-fno-call-arity`; `pfca` and `namedca`, `Wrap`'s Core after Call Arity with the binders' IdInfo; `run` is `100000`; `measure.sh N`): orthotope's generic `pad` with its checks, INLINABLE, in `Lib`; the boxed instance and the INLINE wrapper in `Wrap`, under `-fpolymorphic-specialisation` as orthotope's Shaped is; and a client padding by nothing at a constant shape, its `padded` and `shapeP` returning top-level lists.

```haskell
{-# LANGUAGE BangPatterns, ScopedTypeVariables, AllowAmbiguousTypes #-}
module Lib (Vec (..), Padded (..), Shape (..), Arr (..), pad) where

import Data.Proxy (Proxy (..))
import GHC.Stack (HasCallStack)

class Vec v where
  vpad :: a -> [(Int, Int)] -> [Int] -> v a -> v a

class Padded ps where
  padded :: Proxy ps -> [(Int, Int)]

class Shape sh where
  shapeP :: Proxy sh -> [Int]

newtype Arr sh v a = A (v a)

{-# INLINE sumExtents #-}
sumExtents :: [Int] -> Int
sumExtents ss = foldr (\ s k !n -> if n > maxBound - s then -1 else k (n + s)) id ss 0

{-# INLINE sumOverflows #-}
sumOverflows :: [Int] -> Bool
sumOverflows ss = sumExtents ss < 0

validShape :: [Int] -> Bool
validShape = (>= 0) . foldr step 1
  where step _ (-1) = -1
        step n m | n < 0 || m /= 0 && n > maxBound `quot` m = -1
                 | otherwise = n * m

zipWithLong2 :: (a -> b -> b) -> [a] -> [b] -> [b]
zipWithLong2 f (a:as) (b:bs) = f a b : zipWithLong2 f as bs
zipWithLong2 _     _     bs  = bs

{-# INLINABLE pad #-}
pad :: forall ps sh v a . (HasCallStack, Vec v, Padded ps, Shape sh) =>
       a -> Arr sh v a -> Arr sh v a
pad v a@(A at) | or (zipWith (\ (l, h) s -> sumOverflows [l, s, h]) aps ash) =
                   error $ "pad: padding past maxBound " ++ show (aps, ash)
               | not (validShape sh) = error $ "pad: bad shape " ++ show sh
               | all (== (0, 0)) aps = a
               | otherwise = A (vpad v aps ash at)
  where ash = shapeP (Proxy :: Proxy sh)
        aps = padded (Proxy :: Proxy ps)
        sh = zipWithLong2 (\ (l, h) s -> l + s + h) aps ash
```

```haskell
{-# LANGUAGE CPP, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -fpolymorphic-specialisation #-}
module Wrap (Box (..), Array (..), pad) where

import qualified Lib as G
import GHC.Stack (HasCallStack)

newtype Box a = Box [a]

instance G.Vec Box where
  {-# NOINLINE vpad #-}
  vpad v aps _ (Box xs) = Box (replicate (sum (map fst aps)) v ++ xs)

newtype Array sh a = A { unA :: G.Arr sh Box a }

{-# INLINE pad #-}
pad :: forall ps sh a . (HasCallStack, G.Padded ps, G.Shape sh) =>
       a -> Array sh a -> Array sh a
#if defined(NAMED)
pad v a = A (G.pad @ps v (unA a))
#else
pad v = A . G.pad @ps v . unA
#endif
```

```haskell
{-# LANGUAGE BangPatterns, TypeApplications #-}
module Main (main) where

import qualified Lib as G
import Wrap
import System.Environment (getArgs)

data P0
data S33

{-# NOINLINE pads0 #-}
pads0 :: [(Int, Int)]
pads0 = [(0, 0), (0, 0)]

{-# NOINLINE sh33 #-}
sh33 :: [Int]
sh33 = [3, 3]

instance G.Padded P0 where padded _ = pads0
instance G.Shape S33 where shapeP _ = sh33

{-# NOINLINE row #-}
row :: Array S33 Double -> Array S33 Double
row a = pad @P0 0 a

{-# OPAQUE input #-}
input :: Int -> Array S33 Double
input i = A (G.A (Box [fromIntegral i]))

main :: IO ()
main = do
  [n] <- map read <$> getArgs
  let go :: Int -> Int -> Int
      go !i !acc | i == n = acc
                 | otherwise = case row (input i) of
                     A (G.A (Box xs)) -> go (i + 1) (acc + length xs)
  print (go 0 0)
```

`Wrap.dump-call-arity`: `$spad [InlPrag=INLINABLE] :: ... [LclId, Arity=3, CallArity=4,` in `pfca` and `CallArity=5,` in `namedca`. `Wrap.iface`: `pf` has `Arity: 4, Strictness: <L><MP(1C(1,L))><MP(1C(1,L))><L>, Inline:,` and `(eta['GHC.Internal.Types.Many] :: a)[OneShot] -> let {`; `named` has `Arity: 5, Strictness: <LS><1P(1C(1,L))><1P(1C(1,L))><L><L>,` and `(eta1['GHC.Internal.Types.Many] :: Lib.Arr sh Box a)[OneShot] -> let {`; `nca` has `Arity: 3, Strictness: <L><MP(1C(1,L))><MP(1C(1,L))>, Inline:,`. `Wrap.dump-simpl`, whitespace collapsed: `pf` has `pad = \ @k1 @k2 @ps @sh @a $dIP $dPadded $dShape eta -> let { f = $spad (C:IP ...` and `$spad = \ @k1 @k2 @ps @sh @a $dIP $dPadded $dShape eta -> let { aps = padded $dPadded Proxy } in let { lvl10 = $spad_go1 aps } in`, then `let { lvl12 = $spad_go aps ash } in`; `named` has `$spad = \ @k1 @k2 @ps @sh @a $dIP $dPadded $dShape eta eta1 -> let { ash = shapeP $dShape Proxy } in let { aps = padded $dPadded Proxy } in join { $j = $spad12 aps ash (case ip $dIP of wild1 { __DEFAULT -> PushCallStack $spad10 $spad3 wild1; FreezeCallStack ds1 -> wild1 }) } in`, and no `$spad_go`. `Main.dump-simpl`: `pf` and `nca` have `$s$spad_lvl12 = $spad_go pads0 sh33` and `pf` ``$s$spad = \ @a $dIP4 eta eta1 -> case $s$spad_lvl12 `cast` <Co:1> of {``; `named` has `$s$spad = \ @a $dIP4 eta eta1 -> join { $j = case ip $dIP4 of wild1 { __DEFAULT -> $s$spad4 wild1; FreezeCallStack ds1 -> $s$spad3 wild1 } } in`, its checks run by `jump go pads0 sh33`, and no `$s$spad_lvl12`.

`measure.sh 1000000`, twice alike:

```
pf: 186.2 instructions, 88.0 bytes a call
named: 395.2 instructions, 88.0 bytes a call
nca: 186.2 instructions, 88.0 bytes a call
```

**Reproduces small:** yes: the call arities, the checks floated to constants under the point-free wrapper and run at every call under the named one, 209 instructions a call more against orthotope's 229, no byte moving, and `-fno-call-arity` undoing it.

### E20. A function argument holding a Haskell2010 left section's `let` is too big to copy into an inlined function's branches, so whether an INLINE function saturates that call in its own template decides whether the argument is copied first; kept bound, it leaves a closure at the calls too deep to inline

**Rule.** Where an inlined function uses its function parameter in two branches, the argument's binding is copied into both only while its right-hand side is small, so whether an INLINE template saturates its call of that function decides what the argument holds when it is tested. `convertT sh g t` is such a function: it uses its function parameter `g` in two branches, so where `convertT` is inlined, `postInlineUnconditionally` copies the binding of `g` into both only if its right-hand side is small (E12; [compiler/GHC/Core/Opt/Simplify/Utils.hs#L1824][g358], the test `n_br == 1 || smallEnoughToInline uf_opts unfolding` at [#L1855][g359]; `smallEnoughToInline`, [compiler/GHC/Core/Opt/Simplify/Inline.hs#L62][g142]). Named, `mapT sh f t = convertT sh (vMap f) t` saturates `convertT` in `mapT`'s own INLINE template, where `f` is a variable, and `g := vMap ... f` is copied there; `zipWithT`'s template, inlining `mapT`, then copies its own argument for `f`, the left section ``(x `f`)``, as a lambda, the section's `let` left outside it. Reduced, `mapT sh f = convertT sh (vMap f)` names two arguments, and `convertT` stays unsaturated in its template. Inlined into `zipWithT`'s template, the reduced `mapT` has the section substituted for its once-used `f` before the section is simplified (`preInlineUnconditionally`, [compiler/GHC/Core/Opt/Simplify/Utils.hs#L1665][g360], on the path traced as `SimplBindr:inline-uncond3`, [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L1914][g361]; A16), so `g` is bound to `vMap ... (let { v2 = f x3 } in \ v3 -> v2 v3)`. That binding is not copied, where the right section's `g`, holding no `let`, is: it fails `postInlineUnconditionally`'s size test (`smallEnoughToInline`, [compiler/GHC/Core/Opt/Simplify/Utils.hs#L1855][g359]), `g` occurring once in each of two branches of `zipWithT`'s template, `g [Occ=Once2!]` with `Guidance=IF_ARGS [] 110 0`, and the template keeps `g` bound at `-funfolding-use-threshold=109` and not at 110 (`~/r/horde-ad/dist-inlcat/cases/E20-copy-size-test`: variant `libv`, `-O -dverbose-core2core -dsuppress-uniques`, for `g`'s occurrence and guidance, and `t109` and `t110` at those thresholds). The section holds the `let` because without `PostfixOperators` the renamer makes ``(x `f`)`` an application of `leftSection` (`rnSection`, [compiler/GHC/Rename/Expr.hs#L720][g362], the `postfix_ops` test at [#L725][g363], Note [Left and right sections] at [#L737][g364]), whose compulsory unfolding is `leftSection f x = f x` (`leftSectionId`, [compiler/GHC/Builtin/WiredIn/Ids.hs#L335][g365]); orthotope builds under `Haskell2010`, where GHC2021 and GHC2024 turn `PostfixOperators` on. At the client, with the instance known, the bound `g` grows into vector's map loop, is refused at its calls (A04) and is split by worker/wrapper, and its worker `$wg` is inlined at each call where its size plus the depth penalty, less the discounts, is within the threshold (A09); where a call is refused, `$wg` stays a local function holding the element read, a closure allocated at each entry and, its call a `case` scrutinee, no join point (O19).

**Seen.** `mapT sh f t = convertT sh (vMap f) t` against `mapT sh f = convertT sh (vMap f)`, Shaped boxed `rerank2` large, 16 bytes a row more in the reduced build, 6400 a call, in both readings. In the reduced build's `OpsShaped.dump-simpl` the per-row worker `$weta6` holds `let { $wg :: Int# -> Int# -> Array# Double -> (# Int#, Int#, Array# Double #) $wg = \ (ww12 :: Int#) (ww13 :: Int#) (ww14 :: Array# Double) -> runRW# ...`, writing `plusDouble ipv ipv3` with `ipv`, the element read, free, and called as `case $wg (+# ww7 bx2) (+# (+# (+# r6 r4) r5) 1#) ww9 of { (# ww12, ww13, ww14 #) -> (# wild11, -# ww6 bx2, Data.Vector.Vector @Double ww12 ww13 ww14 #) }` (qualifiers dropped, whitespace collapsed); `runRW#` occurs 18 times in `$weta6` and 6 times in the named build's, the other calls of `$wg` inlined. Rebuilt with `-dinline-check $wg` on `OpsShaped` alone, `$weta6`'s calls of its worker are refused at every call while its guidance is `IF_ARGS [0 0 0] 172 0`, and at every call deeper than 3 while it is `122`. Once it is `102`, those at depth 16 or less are inlined, the deepest at `adjusted size = 89`, and the two at depth 17, those left in the final Core, are refused over the threshold of 90: `guidance IF_ARGS [0 0 0] 102 0 case depth = 17 inline depth = 1 depth based penalty = 51 adjusted size = 93 ANSWER = NO`.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/E20-convert-arg-closure`, variants `named` (`-DNAMED`) and `reduced`; `named85` and `reduced85`, the same at `-funfolding-use-threshold=85`; `reduced-g`, `reduced` with `-dinline-check g`; `reduced85-wg`, `reduced85` with `-dinline-check $wg`; `named-trace` and `reduced-trace`, with `-dverbose-core2core`; `run` is `100000`; `measure.sh N`): orthotope's `Vector` class with its element constraint, `readRangeT` for ranks 1 to 3 with `range3T`, `convertT`, `mapT` and `zipWithT`, in `Lib` under `Haskell2010`; the boxed instance in `Inst`; and a row zipping a one-element view with a dense one at a run-time shape, so that `zipWithT` maps the left section over the second.

```haskell
{-# LANGUAGE Haskell2010, CPP, BangPatterns, TypeFamilies, FlexibleInstances #-}
module Lib (Vector (..), None, T (..), Range (..), readRangeT, convertT, mapT,
            zipWithT) where

import Data.Kind (Constraint, Type)

class Vector v where
  type VecElem v :: Type -> Constraint
  vLength :: VecElem v a => v a -> Int
  vUnsafeIndex :: VecElem v a => v a -> Int -> a
  vMap :: (VecElem v a, VecElem v b) => (a -> b) -> v a -> v b
  vUnsafeSlice :: VecElem v a => Int -> Int -> v a -> v a
  vEmpty :: VecElem v a => v a
  vSingleton :: VecElem v a => a -> v a
  vZipWith :: (VecElem v a, VecElem v b, VecElem v c) => (a -> b -> c) -> v a -> v b -> v c
  vUnsafeWithElem :: VecElem v a => v a -> Int -> (a -> r) -> r
  vUnsafeWithElem v i k = k (vUnsafeIndex v i)

class None a
instance None a

data T v a = T ![Int] !Int !(v a)

data Range = Range !Int !Int | NoRange

{-# INLINE readRangeT #-}
readRangeT :: [Int] -> T v a -> Range
readRangeT [n] (T [s] ao _) = range3T n s 1 1 1 1 ao
readRangeT [n1, n2] (T [s1, s2] ao _) = range3T n1 s1 n2 s2 1 1 ao
readRangeT [n1, n2, n3] (T [s1, s2, s3] ao _) = range3T n1 s1 n2 s2 n3 s3 ao
readRangeT _ _ = NoRange

{-# INLINE range3T #-}
range3T :: Int -> Int -> Int -> Int -> Int -> Int -> Int -> Range
range3T n1 !s1 n2 !s2 n3 !s3 ao
  | n1 == 0 || n2 == 0 || n3 == 0 = NoRange
  | s3 == 1 && s2 == n3 && s1 == n2 * n3 = Range ao (n1 * n2 * n3)
  | a1 <= 1 + lt a2 a1 r2 + lt a3 a1 r3 && a2 <= 1 + le a1 a2 r1 + lt a3 a2 r3
    && a3 <= 1 + le a1 a3 r1 + le a2 a3 r2 =
      Range (ao - neg s1 r1 - neg s2 r2 - neg s3 r3) (r1 + r2 + r3 + 1)
  | otherwise = NoRange
  where a1 = if n1 == 1 then 0 else abs s1
        a2 = if n2 == 1 then 0 else abs s2
        a3 = if n3 == 1 then 0 else abs s3
        r1 = (n1 - 1) * a1
        r2 = (n2 - 1) * a2
        r3 = (n3 - 1) * a3
        lt a b r = if a < b then r else 0
        le a b r = if a <= b then r else 0
        neg s r = if s < 0 then r else 0

{-# NOINLINE toVectorT #-}
toVectorT :: (Vector v, VecElem v a) => [Int] -> T v a -> v a
toVectorT _ (T _ _ v) = v

{-# INLINE convertT #-}
convertT :: (Vector v, VecElem v a, VecElem v b) => [Int] -> (v a -> v b) -> T v a -> T v b
convertT sh g t@(T ss o v) | Range lo n <- readRangeT sh t = T ss (o - lo) (g (vUnsafeSlice lo n v))
convertT sh _ _ | 0 `elem` sh = T (map (const 0) sh) 0 vEmpty
convertT sh g t = T (map (const 1) sh) 0 (g (toVectorT sh t))

{-# INLINE mapT #-}
mapT :: (Vector v, VecElem v a, VecElem v b) => [Int] -> (a -> b) -> T v a -> T v b
#if defined(NAMED)
mapT sh f t = convertT sh (vMap f) t
#else
mapT sh f = convertT sh (vMap f)
#endif

{-# INLINE zipWithT #-}
zipWithT :: (Vector v, VecElem v a, VecElem v b, VecElem v c) =>
            [Int] -> (a -> b -> c) -> T v a -> T v b -> T v c
zipWithT sh f t@(T ss _ v) t'@(T _ _ v') =
  case (vLength v, vLength v') of
    (1, 1) | 0 `notElem` sh -> T ss 0 $ vSingleton $ f (vUnsafeIndex v 0) (vUnsafeIndex v' 0)
    (1, _) | 0 `notElem` sh -> vUnsafeWithElem v 0 $ \ x -> mapT sh (x `f`) t'
    (_, 1) | 0 `notElem` sh -> vUnsafeWithElem v' 0 $ \ y -> mapT sh (`f` y) t
    _ -> T ss 0 (vZipWith f (toVectorT sh t) (toVectorT sh t'))
```

```haskell
{-# LANGUAGE TypeFamilies #-}
module Inst () where

import qualified Data.Vector as V
import Data.Vector.Fusion.Util (Box (..))
import Lib

instance Vector V.Vector where
  type VecElem V.Vector = None
  {-# INLINE vLength #-}
  vLength = V.length
  {-# INLINE vUnsafeIndex #-}
  vUnsafeIndex = V.unsafeIndex
  {-# INLINE vMap #-}
  vMap = fmap
  {-# INLINE vUnsafeSlice #-}
  vUnsafeSlice = V.unsafeSlice
  {-# INLINE vEmpty #-}
  vEmpty = V.empty
  {-# INLINE vSingleton #-}
  vSingleton = V.singleton
  {-# INLINE vZipWith #-}
  vZipWith = V.zipWith
  {-# INLINE vUnsafeWithElem #-}
  vUnsafeWithElem v i k = case V.unsafeIndexM v i of Box x -> k x
```

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import qualified Data.Vector as V
import Inst ()
import Lib
import System.Environment (getArgs)

{-# NOINLINE row #-}
row :: [Int] -> T V.Vector Double -> T V.Vector Double -> T V.Vector Double
row sh x y = zipWithT sh (+) x y

{-# OPAQUE inputs #-}
inputs :: Int -> ([Int], T V.Vector Double, T V.Vector Double)
inputs i = ([5], T [0] 0 (V.singleton (fromIntegral i)),
            T [1] 0 (V.fromList [1, 2, 3, 4, 5]))

main :: IO ()
main = do
  [n] <- map read <$> getArgs
  let go :: Int -> Double -> Double
      go !i !acc
        | i == n = acc
        | otherwise = case inputs i of
            (sh, x, y) -> case row sh x y of
              T _ _ v -> go (i + 1) (acc + V.unsafeIndex v 4)
  print (go 0 0)
```

`Lib.iface`: `reduced` gives `mapT` `Arity: 5,` and `Inline: (sat-args=2)`, its unfolding `StableUser <5,FalseFalse>`; `named` `Arity: 6,` and `Inline: (sat-args=3)`. In `zipWithT`'s unfolding, `reduced` binds `g :: v b -> v c NotJoinPoint [] = vMap @v $dVector @b @c irred1 irred2 (let { v2 :: b -> c NotJoinPoint [] = f x3 } in \ (v3['GHC.Internal.Types.Many] :: b) -> v2 v3) } in`, and `named` applies the lambda at each use, `(vMap @v $dVector @b @c irred1 irred2 (\ (v3['GHC.Internal.Types.Many] :: b) -> v2 v3) (vUnsafeSlice @v $dVector @b irred1`, binding no such `g`. `build.log`, whitespace collapsed: `named-trace` has `PostInlineUnconditionally g vMap $dVector irred irred eta` and `PostInlineUnconditionally f \ v -> v v`; `reduced-trace` has `inline-uncond3 f := let { v = f x } in \ v -> v v` and `PostInlineUnconditionally g vMap $dVector irred irred (\ v -> eta v y)`, the right section's, and no copy of a `g` holding a `let`; `reduced-g` has `Considering inlining: g arg infos [NonTrivArg] interesting continuation BoringCtxt some_benefit True is exp: True is work-free: True guidance IF_ARGS [0] 270 0 case depth = 2 inline depth = 2 depth based penalty = 0 adjusted size = 240 ANSWER = NO`; `reduced85-wg` has `$wg`'s deepest calls refused, `... guidance IF_ARGS [0 0 0] 102 0 case depth = 16 inline depth = 1 depth based penalty = 47 adjusted size = 89 ANSWER = NO`, and at depth 15 `adjusted size = 86`, sizes the default threshold of 90 lets through. `Main.dump-simpl`: `reduced` and `named85` have no `$wg`; `reduced85` has ``let { $wg = \ ww10 ww11 ww12 -> runRW# (\ s -> case newArray# ww11 uninitialised (s `cast` <Co:10>) of {``, writing ``case writeArray# ipv8 ww13 (plusDouble ipv9 ipv6) (eta `cast` <Co:10>) of s'#`` with `ipv6` free, and called as `case $wg (+# ipv bx2) (+# (+# (+# r1 r2) r3) 1#) ipv2 of { (# ww10, ww11, ww12 #) -> (# wild9, -# ww1 bx2, Vector ww10 ww11 ww12 #) }`, orthotope's shape.

`measure.sh 1000000`, twice alike:

```
named: 715.3 instructions, 512.0 bytes a call
reduced: 682.3 instructions, 512.0 bytes a call
named85: 715.3 instructions, 512.0 bytes a call
reduced85: 690.3 instructions, 528.0 bytes a call
```

**Reproduces small:** in part: the bound `g`, its growth and refusal at its calls, its worker, and the copy that the named form makes and the left section stops, yes; the closure and orthotope's 16 bytes only at `-funfolding-use-threshold=85`, the model's deepest calls of `$wg`, at depth 16 where orthotope's are at 17, passing at the default threshold. Also tried at the default threshold, none giving the closure: the model without the element constraint, with a static shape, with rank 1 alone, under the default language, where the two forms compile alike, and with `zipWithT`'s `(1, 1)` case added.

## 3. How INLINE, INLINABLE and no pragma change the code

Rules for what each pragma does to the code, each stated from our record's observations of the pragmas, mostly from orthotope's specialisation benchmark (O17's from horde-ad), or from those of the perf-checklist and orthotope that no other section answers, and reduced to its mechanism where its entry reproduces small.

### O01. An INLINE specialisation passed a variable as a loop's lazy accumulator is inlined only after worker/wrapper, and the loops it brings stay boxed

**Rule.** At a saturated call with trivial arguments in a boring context, such as a lazy argument of a function with no rules and no argument discount, an INLINE unfolding is inlined only if its body is tiny (A01); before demand analysis a local loop carries no strictness signature, so a value passed as its accumulator is such an argument however the loop forces it. A specialisation of an INLINE function keeps the pragma and the `ALWAYS_IF` unfolding (U12) and takes no dictionary, so where a function argument such as `rnf` was specialised before its call was saturated, the call left is the specialisation applied to the element, a variable: no benefit, no inlining. Worker/wrapper then makes the loop's accumulator strict, the call becomes a case scrutinee, and the simplifier after it ([compiler/GHC/Core/Opt/Pipeline.hs#L180][g366], `simplify "post-worker-wrapper"`) inlines the body. At -O no worker/wrapper runs after that pass (the second `dmd_cpr_ww` is under `-flate-dmd-anal`, [Pipeline.hs#L321][g367]), so the loops of the inlined body keep boxed arguments that worker/wrapper would have unboxed, join points included ([compiler/GHC/Core/Opt/WorkWrap.hs#L438][g368], in Note [Don't w/w join points for CPR]): an INLINE function is inlined from its stable unfolding (U03), and worker/wrapper processes right-hand sides (`tryWW`, [WorkWrap.hs#L543][g369]), so the specialisation's own right-hand side, called nowhere here, has its loops unboxed while its inlined copy has them boxed. Under INLINABLE the inner call is inlined, or called, before demand analysis, and its loops are unboxed. The specialisation at `Double` comes from a call at top level: the gentle simplifier expands the right-hand side of `forceNested = nf`, a partial application (`prepareRhs`, [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L788][g370]), and binds its dictionary argument's field, a call at `Double`, to a new top-level binder named after `forceNested` (`makeTrivial`, [#L853][g371]), which the specialiser meets with an empty stack of calls (`specImports`, [compiler/GHC/Core/Opt/Specialise.hs#L771][g372]); so the tree's patch to Specialise.hs, which concerns calls of a function already on that stack, does not bear here.

**Seen.** Orthotope's benchmark: with INLINE on orthotope's boxed arrays' `rnf`, forcing an array of arrays inlined the inner `rnf` into the outer loop, its strided path a recursive join point `go :: Int -> Int -> ()` with boxed counters, and Dynamic boxed `unravel` at the large dense view ran 81% more instructions (C4 against C3); taking those INLINEs away saved up to 32 bytes an element at large boxed `unravel`. The outer loop there is vector's: boxed `Vector`'s `rnf` is `liftRnfV rnf`, `liftRnfV elemRnf = foldl' (\_ -> elemRnf) ()` (vector 0.13.2.0, `Data.Vector`), the accumulator this case names. A client of orthotope as built at C4 (INLINE on the boxed arrays' `rnf`), `~/r/horde-ad/dist-inlcat/cases/O01-nested-inline-boxed-join/probe-orthotope/Client.hs` (`forceNested = rnf` at `Array (Array Double)`), has six boxed jumps in `forceNested` at -O and none at -O `-flate-dmd-anal` (`~/r/horde-ad/dist-inlcat/cases/O01-nested-inline-boxed-join/probe-orthotope/run.sh`, which needs that build of orthotope).

**Repro** (`~/r/horde-ad/dist-inlcat/cases/O01-nested-inline-boxed-join`, variants `inline`, by `-DINL`, `inlinable`, `inline-late` = `inline` with `-flate-dmd-anal`, `spec` and `v2c`, `inline` with `-ddump-spec` and with `-dverbose-core2core`, the specialiser's output and every pass, both with `-dsuppress-uniques -dsuppress-idinfo -dsuppress-coercions -dsuppress-module-prefixes` in place of the two suppression flags; `run` is `100 1000`): an array of 100 strided arrays of 100 Doubles forced 1000 times, the element method INLINE against INLINABLE.

```haskell
{-# LANGUAGE BangPatterns, CPP, MagicHash, UnboxedTuples #-}
module Lib (V (..), NF (..), mkV) where

import Data.Array (listArray)
import Data.Array.Base (unsafeAt)
import GHC.Arr (Array (..))
import GHC.Exts (Int (I#), build, indexArray#)

-- A view of an array: length, stride, offset, values.
data V a = V !Int !Int !Int !(Array Int a)

mkV :: Int -> Int -> [a] -> V a
mkV n s xs = V n s 0 (listArray (0, n * s - 1) xs)

class NF a where
  nf :: a -> ()

instance NF Double where
  nf !_ = ()

instance NF a => NF (V a) where
  nf (V n s o arr) = nfV n s o arr
#if defined(INL)
  {-# INLINE nf #-}
#else
  {-# INLINABLE nf #-}
#endif

-- Dense views by a left fold, as vector's rnf, foldl' (\_ -> rnf) (),
-- passes each element's nf as the accumulator; strided ones by foldr over
-- a fused list.
{-# INLINE nfV #-}
nfV :: NF a => Int -> Int -> Int -> Array Int a -> ()
nfV n s o arr
  | s == 1 = foldlV (\_ -> nf) () n o arr
  | otherwise = foldr (\x z -> nf x `seq` z) () (elemsV n s o arr)

-- The element bound before it is used, as vector's unsafeIndexM binds it.
{-# INLINE indexK #-}
indexK :: Array Int a -> Int -> (a -> r) -> r
indexK (Array _ _ _ arr#) (I# i) k = case indexArray# arr# i of (# x #) -> k x

{-# INLINE foldlV #-}
foldlV :: (b -> a -> b) -> b -> Int -> Int -> Array Int a -> b
foldlV f z n o arr = go z 0
  where go !acc !i | i >= n = acc
                   | otherwise = indexK arr (o + i) (\x -> go (f acc x) (i + 1))

{-# INLINE elemsV #-}
elemsV :: Int -> Int -> Int -> Array Int a -> [a]
elemsV n s o arr = build (\c nil ->
  let go !i !p | i < n = c (unsafeAt arr p) (go (i + 1) (p + s))
               | otherwise = nil
  in go 0 o)
```

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import Lib
import System.Environment (getArgs)

-- Opaque, so that each iteration forces the array anew.
{-# OPAQUE pass #-}
pass :: Int -> a -> a
pass _ x = x

-- Force an array of strided arrays.
{-# NOINLINE forceNested #-}
forceNested :: V (V Double) -> ()
forceNested = nf

main :: IO ()
main = do
  [k, reps] <- map read <$> getArgs
  let inner j = mkV k 2 [fromIntegral (j + i) | i <- [0 .. 2 * k - 1]]
      outer = mkV k 1 [inner j | j <- [0 .. k - 1]]
      loop :: Int -> ()
      loop 0 = ()
      loop r = forceNested (pass r outer) `seq` loop (r - 1)
  print (nf outer `seq` loop reps)
```

`inline`, `build.log` (`-dshow-passes -dinline-check $s$fNFV_$cnf`): the call in the dense outer loop, of the specialisation at `Double`, through every simplifier run before demand analysis, then in the first after worker/wrapper:

```
Considering inlining: $s$fNFV_$cnf
  arg infos [TrivArg]
  interesting continuation BoringCtxt
  some_benefit False
  is exp: True
  is work-free: True
  guidance ALWAYS_IF(arity=1,unsat_ok=False,boring_ok=False)
  case depth = 2
  inline depth = 1
  ANSWER = NO
Considering inlining: $s$fNFV_$cnf
  arg infos [TrivArg]
  interesting continuation CaseCtxt
  some_benefit True
  is exp: True
  is work-free: True
  guidance ALWAYS_IF(arity=1,unsat_ok=False,boring_ok=False)
  case depth = 2
  inline depth = 1
  ANSWER = YES
```

`inline`, `Main.dump-simpl`, the inner strided loop and the inner dense one inside the outer dense loop of the specialisation at `V Double`:

```
go i p
  = case i of { I# ipv ->
    case p of { I# ipv2 ->
    ...
    jump go (I# (+# ipv 1#)) (I# (+# ipv2 wild5))
...
jump go (case ipv2 of { D# ipv3 -> () }) (I# (+# ipv 1#))
```

and in the specialisation at `Double` itself, called nowhere:

```
joinrec {
  $wgo ww ww1
    = case <# ww bx of {
        __DEFAULT -> ();
        1# ->
          case indexArray# arr# ww1 of { (# ipv2 #) ->
          case ipv2 of { D# ipv -> jump $wgo (+# ww 1#) (+# ww1 wild1) }
```

`inlinable` and `inline-late` have no `I# (+#` in `Main.dump-simpl`. Bytes in the heap (the run's `+RTS -s` report) and, by `measure.sh 100 1000` (1000 and 2000 iterations differenced), a forced element: `inline` 323,802,656 bytes, 32.16 bytes and 38.03 instructions an element; `inlinable` 2,202,656 bytes, 0.00 and 36.38; `inline-late` 2,202,656 bytes, 0.00 and 36.41.

In `v2c`, the gentle simplifier's output, which the specialiser takes, binds the call at `Double` at top level, `forceNested :: V Double -> () forceNested = $fNFV_$cnf @Double (C:NF @Double $fNFDouble_$cnf)` beside `forceNested :: V (V Double) -> () forceNested = $fNFV_$cnf @(V Double) (C:NF @(V Double) forceNested)` (whitespace collapsed), and `spec`'s specialiser output has both `$s$fNFV_$cnf :: V Double -> ()` and `$s$fNFV_$cnf :: V (V Double) -> ()`. A control, `~/r/horde-ad/dist-inlcat/cases/O01-specialiser-route-eta` (variant `v2c`), writes `forceNested v = nf v`; everything is inlined in the gentle run there, and no `$fNFV_$cnf` reaches the specialiser.

**Reproduces small:** yes, given the inlining delayed past worker/wrapper. The other forms tried, the dense loop forcing each element by ``nf x `seq` go (i + 1)`` (a case context) or passing `nf (unsafeAt arr (o + i))` as its accumulator (a non-trivial argument, the element accessed inside it), had the inner method inlined before demand analysis and its loops unboxed. Orthotope's two-level strided walk (`offsetsT`'s `block` around `go`) changes neither result, the loops unboxed under those forms and boxed as above under this one, so the walk is left out.

### O02. A loop that may evaluate a lifted element, inlined into a larger function, reloads that function's live values at every return point, so the same loop Core compiles to different code inlined and out of line, and the instructions move either way

**Rule.** A loop that may evaluate a lifted element has a call continuation in every iteration, and at each call continuation the code generator reloads from the stack the variables live there ([compiler/GHC/Cmm/LayoutStack.hs#L139][g373], "insert reloads of live registers" in the description of `cmmLayoutStack`'s second pass). Inlined into a larger function, the loop's live set at that point includes the enclosing function's values that are live after the loop, so its return point reloads them every iteration though the loop never uses them; out of line, they stay in the caller's frame. With the linear register allocator, the default (graph colouring is set at no optimisation level: [compiler/GHC/Driver/DynFlags.hs#L1351][g374] is a comment), the registers the inlined loop's return point loads need not be those its header uses, and the allocator joins them with a block of moves on the back edge ([compiler/GHC/CmmToAsm/Reg/Linear/JoinToTargets.hs#L154][g375], `joinToTargets_again`, "assignments don't match, need fixup code"; the block's label carries the code generator's unique tag `n`, [compiler/GHC/Types/Unique.hs#L195][g376]). The header's registers are fixed by the first jump to it that the allocator processes, whose assignment it takes as its own (`joinToTargets_first`, [compiler/GHC/CmmToAsm/Reg/Linear/JoinToTargets.hs#L130][g377]; O18), so a value live at that predecessor alone can change the registers of the whole loop (O03). Neither shows in Core.

**Seen.** In orthotope's specialisation benchmark, a pragma moving instructions at equal bytes, found as the cause of large boxed forcing costs that allocation does not show. Forcing a large flat boxed array (boxed Dynamic `reshape` and its kin at the large dense view): with INLINE on the Dynamic and Ranked wrappers' `rnf` (build C4) the dense loop, vector-stream's `$wfoldlM'_loop` carrying `SPEC`, is inlined into `$s$fNFDataArray_$crnf5`; with `rnf` INLINABLE (C3) it is called as an out-of-line worker, `OpsDynamic.$w$s$w$crnf1`, whose loop has the same Core, and INLINABLE ran about one instruction an element more; the benchmark's harness reaches `rnf` through an `NFData` dictionary unknown at its call, and Shaped forcing moved the other way, about 600,000 instructions less a call at `mapA` and `rev`, as the repro does. Read in C3's and C4's binaries, the two loops, C3's from its return point at `0x183a100` and C4's from `0x1852628` in `$s$fNFDataArray_$crnf5`, run 20 and 19 instructions an element and are the same but for one register copy in C3, `mov %rsi,%rdi` at `0x183a11e`: both paths into the loop's header load the array into `%rsi`, while the header indexes through `%rdi`, the copy sitting on the entry edge too, which is the kind of fixup move the repro shows (the Cmm not read).

**Repro** (`~/r/horde-ad/dist-inlcat/cases/O02-same-core-different-code`, variants `inline`, by `-DINL`, `inlinable`, and the two with `-fregs-graph`, `inline-graph` and `inlinable-graph`; `run` is `100000 100`): a flat dense view of 100000 Doubles forced once an iteration, the method INLINE against INLINABLE. `Lib.hs` is O01's with `elemsV` walking orthotope's two levels, `block` over an odometer around `go`, which makes the method large enough that INLINABLE's specialisation stays out of line; with O01's one-level `elemsV` it was inlined too, and both variants ran 24.00 instructions an element. Two pairs more take orthotope's shape closer, each INLINE against INLINABLE: `vec-inline` and `vec-inlinable` (`-DVEC`) store the values in a boxed `Data.Vector` and force dense views by vector's own `foldl'`, as vector's `rnf` does, so the loop is vector-stream's `$wfoldlM'_loop` carrying `SPEC`; `harness-inline` and `harness-inlinable` (`-DVEC -DHARNESS`) also reach `nf` as an unknown function, `runNF` being OPAQUE, as the benchmark's harness reaches `rnf` through an unknown dictionary.

```haskell
{-# LANGUAGE BangPatterns, CPP, MagicHash, UnboxedTuples #-}
module Lib (V (..), NF (..), mkV) where

#if defined(VEC)
import qualified Data.Vector as Vec
import GHC.Exts (build)

-- With VEC, the values in a boxed vector, the dense views forced by
-- vector's own foldl', as vector's rnf forces them.
type Store = Vec.Vector

mkV :: Int -> Int -> [a] -> V a
mkV n s xs = V n s 0 (Vec.fromListN (n * s) xs)

unsafeAt :: Vec.Vector a -> Int -> a
unsafeAt = Vec.unsafeIndex
#else
import Data.Array (listArray)
import Data.Array.Base (unsafeAt)
import GHC.Arr (Array (..))
import GHC.Exts (Int (I#), build, indexArray#)

type Store = Array Int

mkV :: Int -> Int -> [a] -> V a
mkV n s xs = V n s 0 (listArray (0, n * s - 1) xs)
#endif

-- A view of an array: length, stride, offset, values.
data V a = V !Int !Int !Int !(Store a)

class NF a where
  nf :: a -> ()

instance NF Double where
  nf !_ = ()

instance NF a => NF (V a) where
  nf (V n s o arr) = nfV n s o arr
#if defined(INL)
  {-# INLINE nf #-}
#else
  {-# INLINABLE nf #-}
#endif

-- Dense views by a left fold, as vector's rnf, foldl' (\_ -> rnf) (),
-- passes each element's nf as the accumulator; strided ones by foldr over
-- a fused list.
{-# INLINE nfV #-}
nfV :: NF a => Int -> Int -> Int -> Store a -> ()
nfV n s o arr
#if defined(VEC)
  | s == 1 = Vec.foldl' (\_ -> nf) () (Vec.unsafeSlice o n arr)
#else
  | s == 1 = foldlV (\_ -> nf) () n o arr
#endif
  | otherwise = foldr (\x z -> nf x `seq` z) () (elemsV n s o arr)

#if !defined(VEC)
-- The element bound before it is used, as vector's unsafeIndexM binds it.
{-# INLINE indexK #-}
indexK :: Array Int a -> Int -> (a -> r) -> r
indexK (Array _ _ _ arr#) (I# i) k = case indexArray# arr# i of (# x #) -> k x

{-# INLINE foldlV #-}
foldlV :: (b -> a -> b) -> b -> Int -> Int -> Array Int a -> b
foldlV f z n o arr = go z 0
  where go !acc !i | i >= n = acc
                   | otherwise = indexK arr (o + i) (\x -> go (f acc x) (i + 1))
#endif

-- The odometer of the levels above the counter axis: offset, count left,
-- stride, extent.
data Odo = OdoLevel !Int !Int !Int !Int !Odo | OdoDone

stepOdo :: Odo -> Odo
stepOdo OdoDone = OdoDone
stepOdo (OdoLevel o c s d outer)
  | c > 1 = OdoLevel (o + s) (c - 1) s d outer
  | otherwise = case stepOdo outer of
      OdoDone -> OdoDone
      next@(OdoLevel o' _ _ _ _) -> OdoLevel o' d s d next

-- One row of n elements at stride s, walked as orthotope's offsetsT walks
-- a view: go along the row, block over an odometer of the levels above it,
-- here one level of one position.
{-# INLINE elemsV #-}
elemsV :: Int -> Int -> Int -> Store a -> [a]
elemsV n s o arr = build (\c nil ->
  let block p0 outer =
        let go !i !p | i < n = c (unsafeAt arr p) (go (i + 1) (p + s))
                     | otherwise = case stepOdo outer of
                         OdoDone -> nil
                         next@(OdoLevel p' _ _ _ _) -> block p' next
        in go 0 p0
  in block o (OdoLevel o 1 (n * s) 1 OdoDone))
```

```haskell
{-# LANGUAGE CPP #-}
module Main (main) where

import Lib
import System.Environment (getArgs)

-- Opaque, so that each iteration forces the array anew.
{-# OPAQUE pass #-}
pass :: Int -> a -> a
pass _ x = x

#if defined(HARNESS)
-- The benchmark harness's shape: the forcing reached as an unknown function.
{-# OPAQUE runNF #-}
runNF :: (V Double -> ()) -> V Double -> Int -> ()
runNF f flat reps = loop reps
  where loop 0 = ()
        loop r = case f (pass r flat) of () -> loop (r - 1)
#endif

main :: IO ()
main = do
  [k, reps] <- map read <$> getArgs
  let flat = mkV k 1 [fromIntegral i | i <- [0 .. k - 1]] :: V Double
#if defined(HARNESS)
  print (nf flat `seq` runNF nf flat reps)
#else
      loop :: Int -> ()
      loop 0 = ()
      loop r = case nf (pass r flat) of () -> loop (r - 1)
  print (nf flat `seq` loop reps)
#endif
```

The dense loop, `Main.dump-simpl`: `inline`, inside `main`'s iteration loop, and `inlinable`, in the specialisation `$s$w$cnf = \ ww ww1 ww2 ww3 ->` that the iteration loop calls (`inline` has no `$s$w$cnf`):

```
$wgo ww13
  = case >=# ww13 bx of {
      __DEFAULT ->
        case indexArray# arr# (+# bx2 ww13) of
        { (# ipv2 #) ->
        case ipv2 of { D# ipv3 ->
        jump $wgo (+# ww13 1#)
        }
        };
      1# -> jump $j1
    };
```

```
$wgo ww4
  = case >=# ww4 ww of {
      __DEFAULT ->
        case indexArray# ww3 (+# ww2 ww4) of { (# ipv1 #) ->
        case ipv1 of { D# ipv -> jump $wgo (+# ww4 1#) }
        };
      1# -> (##)
    };
```

`Main.dump-asm`, the loop's return point (the frame reloaded, the counter incremented) and, for `inline`, the block between it and the loop header; the rest of each iteration, the bound test and the load, the frame written and the tag tested, is 13 instructions in the four variants without `VEC`. `inline`, 26 instructions an element:

```
movq 48(%rbp),%rax
movq 40(%rbp),%rsi
movq 32(%rbp),%rcx
movq 8(%rbp),%rdx
movq 16(%rbp),%rdi
movq 24(%rbp),%r8
incq %r8
addq $32,%rbp
.Ln1j:
movq %rax,%rbx
movq %rcx,%rax
movq %rdx,%rcx
movq %rdi,%rdx
movq %r8,%rdi
```

`inlinable`, 19:

```
movq 8(%rbp),%r14
movq 16(%rbp),%rdi
movq 24(%rbp),%r8
movq 32(%rbp),%rax
incq %rax
addq $40,%rbp
```

`inline-graph`, 21: the moves gone, the two reloads of the enclosing loop's values, `40(%rbp)` and `48(%rbp)`, kept:

```
movq 48(%rbp),%rcx
movq 40(%rbp),%rdx
movq 32(%rbp),%r8
movq 8(%rbp),%rax
movq 16(%rbp),%rdi
movq 24(%rbp),%rbx
leaq 1(%rbx),%rsi
addq $32,%rbp
```

By `measure.sh 100000 100` (100 and 200 iterations differenced), instructions a forced element: `inline` 26.00, `inlinable` 19.00, `inline-graph` 21.00, `inlinable-graph` 19.00; no variant allocates in the loop.

With vector-stream's loop, `vec-inlinable`'s `Main.dump-simpl` holds the out-of-line worker `$w$s$w$cnf`, as orthotope's `$w$s$w$crnf1`, its loop stepping by `case ipv of { D# ipv1 -> jump $wfoldlM'_loop SPEC (+# ww6 1#) }`; `vec-inline` has no `$w$s$w$cnf`. Under the harness both call `case runNF $s$fNFV_$cnf (V ww 1# 0# (Vector 0# ww2 ipv5)) reps`, `harness-inline`'s `$s$fNFV_$cnf` holding the loop and `harness-inlinable`'s calling `$w$s$w$cnf`. By `measure.sh 100000 100 vec-inline vec-inlinable harness-inline harness-inlinable`, instructions a forced element: 25.00, 20.00, 23.00 and 20.00, no byte. `Main.dump-asm` of the harness pair, the dense loop's return point, where both rematerialise `SPEC` into a register the loop does not use, `harness-inline` then `harness-inlinable`:

```
movq 32(%rbp),%rax
movq 8(%rbp),%rsi
movq 16(%rbp),%rdx
movq 24(%rbp),%rcx
incq %rcx
addq $32,%rbp
leaq SPEC_closure+1(%rip),%rdi
```

```
movq 8(%rbp),%r14
movq 16(%rbp),%r9
movq 24(%rbp),%r8
movq 32(%rbp),%rax
incq %rax
addq $40,%rbp
leaq SPEC_closure+1(%rip),%rcx
```

and the frame written before each element is evaluated, four stores in both: the inlined copy rewrites the loop's bound (`%rax`, the operand of its `cmpq`) into the slot its return point reloads as `32(%rbp)` every iteration, and the worker, its frame a slot deeper, rewrites all four of its values, the array (`%r9`) among them; the worker saves the three register moves the inlined copy makes between its return point and its stores:

```
movq %rsi,-24(%rbp)
movq %rdx,-16(%rbp)
movq %rdi,-8(%rbp)
movq %rax,(%rbp)
addq $-32,%rbp
```

```
movq %r14,-32(%rbp)
movq %r9,-24(%rbp)
movq %r8,-16(%rbp)
movq %rax,-8(%rbp)
addq $-40,%rbp
```

A second repro (`~/r/horde-ad/dist-inlcat/cases/O02-small-fold-boxed`, variants `inline` and `inlinable` by `maximumT`'s pragma, `inline` by `-DINL`, both with `-ddump-asm`; `run` is `100000`; `measure.sh N`): a small fold, `maximumT`, generic in the vector, through a class as orthotope's generic arrays take it, and in the element; the boxed wrapper's `maximumA`, INLINABLE, fixing the vector to `Data.Vector.Vector` and leaving the element; and `Main` calling `maximumA` at `Double` on five elements once an iteration.

```haskell
{-# LANGUAGE BangPatterns, CPP #-}
-- Everything exported, as orthotope's Data.Array.Internal exports everything.
module Lib (module Lib) where

import qualified Data.Vector as V

-- A small fold: the vector operations as a class, as orthotope's generic
-- arrays take them, and maximumT generic in the vector and the element.
class Vec v where
  vMaximum :: Ord a => v a -> a

instance Vec V.Vector where
  {-# INLINE vMaximum #-}
  vMaximum = V.maximum

data A v a = A ![Int] !(v a)

#if defined(INL)
{-# INLINE maximumT #-}
#else
{-# INLINABLE maximumT #-}
#endif
maximumT :: (Vec v, Ord a) => A v a -> a
maximumT (A sh v)
  | product sh == 0 = error "maximumT: empty array"
  | otherwise = vMaximum v

-- The boxed wrapper module's maximumA: the vector fixed, the element not.
{-# INLINABLE maximumA #-}
maximumA :: Ord a => A V.Vector a -> a
maximumA = maximumT
```

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import Lib
import System.Environment (getArgs)
import qualified Data.Vector as V

-- Opaque, so that each iteration folds anew.
{-# OPAQUE pass #-}
pass :: Int -> a -> a
pass _ x = x

-- maximumA at Double, once an iteration.
main :: IO ()
main = do
  [repss] <- getArgs
  let reps = read repss :: Int
      v = A [5] (V.fromList [3, 1, 4, 1, 5 :: Double])
      loop :: Int -> Double -> Double
      loop 0 !acc = acc
      loop r !acc = loop (r - 1) (acc + maximumA (pass r v))
  print (loop reps 0)
```

`inlinable`, `Lib.dump-simpl`: the rule `"SPEC maximumT @Vector @_" forall @a $dVec. maximumT $dVec = maximumA_$smaximumT`, and the copy `maximumA_$smaximumT = \ @a $dOrd ds ->`, polymorphic in the element, its `Ord` an argument; `inline` has the same rule. `Main.dump-simpl`: `inline` has the fold's loop inside `main`'s loop `$wloop`, its exit `join { $j1 y = $wloop (-# wild 1#) (+## ww1 y) } in` and its step `join { $j2 ww5 = jump $wfoldlM'_loop SPEC ww5 (+# ww4 1#) } in`; `inlinable` calls `case $w$s$w$smaximumT ww2 ww4 ww5 ww6 of ww7 { __DEFAULT ->`, the client's specialisation at `Double`, which steps by `1# -> jump $w$wfoldlM'_loop SPEC y1 (+# ww5 1#)`: both compare by `<=##`, no dictionary passed. `Main.dump-asm`, the return point after a boxed element is evaluated, `inline` then `inlinable`:

```
movsd 48(%rbp),%xmm1
movq 56(%rbp),%rax
movq 40(%rbp),%rdx
movq 24(%rbp),%rcx
movq 32(%rbp),%rsi
movsd 16(%rbp),%xmm0
movq 8(%rbp),%rdi
movsd 7(%rbx),%xmm2
ucomisd %xmm0,%xmm2
```

```
movq 24(%rbp),%rsi
movq 32(%rbp),%rdi
movq 40(%rbp),%r8
movsd 16(%rbp),%xmm0
movq 8(%rbp),%rax
movsd 7(%rbx),%xmm1
ucomisd %xmm0,%xmm1
```

The inlined copy reloads two slots more, `48(%rbp)` and `56(%rbp)`; by the Core, the values live across the fold besides its own are `$wloop`'s accumulator and counter, which only the fold's exit `$j1` uses. By `measure.sh 100000`: 219.4 and 212.5 instructions a call of `maximumA`, both 16.0 bytes, INLINE's cost 6.9 instructions a call on five elements.

**Reproduces small:** in part: the forcing, yes: the same Core compiling to different code by where it is inlined, read in the assembly; not orthotope's direction, the out-of-line worker running more, vector's `SPEC` loop out of line and the forcing reached as an unknown function narrowing the gap from 7 instructions an element to 3, INLINE still the dearer. The small fold, yes, INLINE's cost 6.9 instructions a call on five elements, by the return point's reloads (second repro); orthotope's small folds cost by the call instead (O05).

### O03. A loop moved out of an INLINE body into an INLINABLE function arrives unboxed when inlined late: its specialisation is inlined from its optimised right-hand side

**Rule.** A binding without a stable unfolding gets its unfolding from its simplified right-hand side ([compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4859][g378], the last branch of `simplLetUnfolding`, `mkLetUnfolding ... VanillaSrc ... new_rhs`; U01), and a specialisation of an INLINABLE function has no stable unfolding (U12). Such a specialisation inlined after worker/wrapper is therefore inlined in the form worker/wrapper left it, its loops unboxed, while a loop written in an INLINE body arrives as written (O01). Its guidance shrinks as its right-hand side is optimised, so the same call refused early can be taken late. So moving a path out of an INLINE body into an INLINABLE function takes O01's boxing away from that path and leaves it on what stays in the body; it does not change code where the moved path is not taken.

**Seen.** Orthotope's benchmark: with orthotope's boxed arrays' `rnf` INLINE and its strided path moved into an INLINABLE `rnfStridedT`, boxed `unravel` kept INLINE's cost and large boxed forcing lost INLINE's gain, which was read as the cost lying elsewhere than that path and the gain needing the path inlined. The repro shows the first half: what the split leaves is the dense path's cost, and the rows `unravel` returns from the large dense view are contiguous, which `rnfViewT` forces by its dense branch, `Range lo n -> rnf (vUnsafeSlice lo n v)` (orthotope's `Data/Array/Internal.hs`). In the binaries of C6 and C7 (`rnfStridedT` split out), that branch carries the cost: forced boxed `unravel` at the large dense view allocates 3,392,768 bytes a call at C7 against C6's 192,768, 16 more an element, and C7's hot loop, in `$s$fNFDataArray_$crnf9`, is the dense branch's element loop, its counter boxed at every element (`movq $0x23408b0,-0x8(%r12)`, `I#`'s info table by `nm`) and unboxed at the loop's head. Large flat boxed forcing (`Dynamic/reshape/large/dense/boxed`): C7 inlines the dense loop into a method as C4 does (from `$s$fNFDataArray_$crnf7_info+0x8e0`), yet runs 20 instructions an element, with a register copy, `mov %rsi,%r8`, that C4's 19 do not make and that C6's out-of-line worker makes too (`mov %rsi,%rdi`; O02 reads the same pair at C3 and C4); so inlining the loop does not alone give INLINE's gain. The loop's Core is C4's and the array is one Cmm register; the copy is a linear-allocator fixup on the back edge (O02; block `.LnHND`, `movq %rsi,%r8`). The dense join point's registers are fixed at the first of its predecessors to be allocated, a return point of `readRangeT`'s inlined code, which in C7 reloads the vector's length just before the array, because the NoRange branch passes both to `$w$s$wrnfStridedT3`: the length is assigned `%rsi`, the array's first register, and the array `%r8`, while the loop's return point reloads the array into `%rsi`. In C4 the inlined NoRange branch first calls `go` on `sh` and `ds26` alone, so that return point reloads no length, and the array is in `%rsi` at the join point and in the loop. The second half does not reproduce: here INLINE has no forcing gain to lose (O02), and the split leaves flat forcing as INLINE's.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/O03-strided-path-split`, variants `inline`, by `-DINL`, `split` = `inline` with `-DSPLIT`, `inlinable`; `run` is `strided 100 1000`; `measure.sh MODE K N`): `Lib.hs` is O02's without its `VEC` branches, with `nfV` below (worker/wrapper splits `nfStrided` in `Lib`, its INLINABLE unfolding going to the worker `$wnfStrided`, U08); `Main` forces, by mode, a flat dense view of K Doubles, or K dense views of K Doubles (`dense`) or K strided ones (`strided`) in a dense outer view.

```haskell
{-# LANGUAGE BangPatterns, CPP, MagicHash, UnboxedTuples #-}
module Lib (V (..), NF (..), mkV) where

-- ... as O02's Lib without VEC, but for nfV, which reads:

nfV :: NF a => Int -> Int -> Int -> Array Int a -> ()
nfV n s o arr
  | s == 1 = foldlV (\_ -> nf) () n o arr
#if defined(SPLIT)
  | otherwise = nfStrided n s o arr

-- The strided path out of the INLINE body, as orthotope's rnfStridedT.
{-# INLINABLE nfStrided #-}
nfStrided :: NF a => Int -> Int -> Int -> Array Int a -> ()
nfStrided n s o arr = foldr (\x z -> nf x `seq` z) () (elemsV n s o arr)
#else
  | otherwise = foldr (\x z -> nf x `seq` z) () (elemsV n s o arr)
#endif
```

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import Lib
import System.Environment (getArgs)

-- Opaque, so that each iteration forces the array anew.
{-# OPAQUE pass #-}
pass :: Int -> a -> a
pass _ x = x

-- Force an array of arrays.
{-# NOINLINE forceNested #-}
forceNested :: V (V Double) -> ()
forceNested = nf

main :: IO ()
main = do
  [mode, ks, repss] <- getArgs
  let k = read ks :: Int
      reps = read repss :: Int
      flat = mkV k 1 [fromIntegral i | i <- [0 .. k - 1]] :: V Double
      -- Inner arrays dense (stride 1) or strided (stride 2).
      nested st = mkV k 1 [mkV k st [fromIntegral (j + i) | i <- [0 .. st * k - 1]]
                          | j <- [0 .. k - 1]]
      loopFlat, loopNested :: V (V Double) -> Int -> ()
      loopFlat _ 0 = ()
      loopFlat o r = case nf (pass r flat) of () -> loopFlat o (r - 1)
      loopNested _ 0 = ()
      loopNested o r = forceNested (pass r o) `seq` loopNested o (r - 1)
  print $ case mode of
    "flat" -> nf flat `seq` loopFlat (nested 1) reps
    "dense" -> let o = nested 1 in nf o `seq` loopNested o reps
    _ -> let o = nested 2 in nf o `seq` loopNested o reps
```

`split`, `build.log` (`-dshow-passes -dinline-check $s$wnfStrided`): the specialisation of `nfStrided`'s worker at `Double`, refused at size 284 before demand analysis, taken at 135 in the first simplifier after worker/wrapper:

```
Considering inlining: $s$wnfStrided
  arg infos [TrivArg, TrivArg, TrivArg, NonTrivArg]
  interesting continuation CaseCtxt
  some_benefit True
  is exp: True
  is work-free: True
  guidance IF_ARGS [0 0 0 20] 284 0
  case depth = 2
  inline depth = 5
  depth based penalty = 0
  adjusted size = 224
  ANSWER = NO
...
Considering inlining: $s$wnfStrided
  arg infos [TrivArg, ValueArg, TrivArg, NonTrivArg]
  interesting continuation CaseCtxt
  some_benefit True
  is exp: True
  is work-free: True
  guidance IF_ARGS [0 0 0 20] 135 0
  case depth = 2
  inline depth = 1
  depth based penalty = 0
  adjusted size = 75
  ANSWER = YES
```

`Main.dump-simpl`, the inner paths inside the outer dense loop of the specialisation at `V Double`: `inline` has `jump go (I# (+# ipv 1#)) (I# (+# ipv2 wild5))` on the strided path and `jump go (case ipv2 of { D# ipv3 -> () }) (I# (+# ipv 1#))` on the dense one; `split` has `jump $wgo1 (+# ww2 1#) (+# ww3 wild5)` on the strided path and the same dense one; `inlinable` has no `I# (+#`.

Instructions and bytes a forced element (`~/r/horde-ad/dist-inlcat/cases/O03-strided-path-split/measure.sh`, N and 2N iterations differenced):

```
mode (K, N)            inline         split          inlinable
flat (100000, 100)     26.00, 0.00    26.00, 0.00    19.00, 0.00
dense (100, 1000)      33.80, 16.00   33.80, 16.00   35.44, 0.00
strided (100, 1000)    36.76, 32.64   27.34, 0.48    28.34, 0.48
```

**Reproduces small:** in part. The split's mechanism and its effect on nested forcing, yes; the loss of a flat forcing gain, no, this repro having no such gain.

### O04. INLINE on a function called from a rarely taken branch makes its caller too big to inline, where both are exported or used more than once: the branch gains, every other call loses

**Rule.** An INLINE function is inlined at a saturated call with any benefit whatever its size (A05, [compiler/GHC/Core/Opt/Simplify/Inline.hs#L310][g5]), and its body is then counted in the size of the function that calls it. A function without a pragma is inlined only if its size less discounts is at most `unfoldingUseThreshold` ([compiler/GHC/Core/Opt/Simplify/Inline.hs#L338][g222]; 90, [compiler/GHC/Core/Unfold.hs#L103][g379]; A04). So INLINE on a function called from one branch of a small caller, here a comparator's tie branch, puts its body into the caller, the caller's size passes the threshold, and the caller's own callers, here a sort loop, call it out of line at every comparison; without the pragma the callee stays out of line, the caller stays small and is inlined into the loop, and the callee is called only when the branch is taken. Both bindings must be exported or have several uses: used once and not exported, each is inlined into its single caller whatever its pragma (A16 for a binding without INLINE), and the two forms compile the same.

**Seen.** Orthotope's benchmark: INLINE on orthotope's `runRank`, called only from `byStrideRank`'s tie branch at stride 1, gained 3 to 3.8% at `allSameA.tiers`, where ties at stride 1 occur, and cost 1 to 2.5% at about 150 cells sorting a view's axes into the same order; `Data.Array.Internal` exports every binding. In the Core of that build (C6), `runRank` is inlined into `$wbyStrideRank`, 160 terms, which `insertAxis` and `$wsortAxesT` call; in C8's, without the pragma, `byStrideRank` is inlined into both, and only the stride-1 tie calls `$wrunRank` out of line. The bytes are equal in both forms, as in orthotope.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/O04-comparator-inline`, variants `inline`, by `-DINL`, and `none`; `run` is `ties 100000`; `measure.sh MODE N`): an insertion sort of eight axes by orthotope's comparator, with `runRank` INLINE or without a pragma, on axes all of stride 1 (`ties`, `runRank` decides every comparison) or of distinct strides (`strides`, never called).

```haskell
{-# LANGUAGE BangPatterns, CPP #-}
-- Everything exported, as orthotope's Data.Array.Internal exports everything.
module Lib (module Lib) where

data Axis = Axis !Int !Int  -- stride, extent

-- Absolute stride descending; on a tie at stride 1 the extent runRank
-- prefers last; on any other tie the extent ascending (orthotope's
-- byStrideRank).
byStrideRank :: Axis -> Axis -> Ordering
byStrideRank (Axis s1 n1) (Axis s2 n2) = case compare s2 s1 of
  EQ | s1 == 1 -> runRank n2 n1
     | otherwise -> compare n1 n2
  o -> o

-- Which of two run lengths is preferred (orthotope's runRank).
#if defined(INL)
{-# INLINE runRank #-}
#endif
runRank :: Int -> Int -> Ordering
runRank !a !b = case compare ta tb of
  EQ | ta == 1 || ta == 3 -> compare a b
     | otherwise -> compare b a
  o -> o
  where
    !ta = tier a
    !tb = tier b
    tier :: Int -> Int
    tier n
      | n <= 2 = 4
      | n < 5 = 2
      | n <= 32 = 0
      | n <= 96 = 1
      | otherwise = 3

-- Insertion sort into byStrideRank's order (orthotope's insertAxis).
insertAxis :: Axis -> [Axis] -> [Axis]
insertAxis x (y : ys)
  | GT <- byStrideRank x y = let !r = insertAxis x ys in y : r
insertAxis x ys = x : ys

sortAxes :: [Axis] -> [Axis]
sortAxes = foldr insertAxis []
```

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import Lib
import System.Environment (getArgs)

-- Opaque, so that each iteration sorts anew.
{-# OPAQUE pass #-}
pass :: Int -> a -> a
pass _ x = x

-- A checksum of the order, so that the sort is forced.
check :: [Axis] -> Int
check = foldr (\(Axis s n) k !acc -> k (acc * 31 + s * 7 + n)) id `flip` 0

main :: IO ()
main = do
  [mode, repss] <- getArgs
  let reps = read repss :: Int
      -- ties: unit-stride axes of various extents, so runRank decides;
      -- strides: distinct strides, so it is never called.
      axes | mode == "ties" = [Axis 1 n | n <- [3, 40, 1, 7, 100, 2, 20, 64]]
           | otherwise = [Axis s 4 | s <- [3, 40, 1, 7, 100, 2, 20, 64]]
      loop :: Int -> Int -> Int
      loop 0 !acc = acc
      loop r !acc = loop (r - 1) (acc + check (sortAxes (pass r axes)))
  print (loop reps 0)
```

`build.log` (`-dinline-check $wbyStrideRank`), the comparator's worker at its call in `insertAxis`, `inline` then `none`:

```
Considering inlining: $wbyStrideRank
  arg infos [TrivArg, TrivArg, TrivArg, TrivArg]
  interesting continuation CaseCtxt
  some_benefit True
  is exp: True
  is work-free: True
  guidance IF_ARGS [60 0 0 0] 615 20
  case depth = 1
  inline depth = 1
  depth based penalty = 0
  adjusted size = 545
  ANSWER = NO
```

```
Considering inlining: $wbyStrideRank
  arg infos [TrivArg, TrivArg, TrivArg, TrivArg]
  interesting continuation CaseCtxt
  some_benefit True
  is exp: True
  is work-free: True
  guidance IF_ARGS [60 0 0 0] 122 20
  case depth = 1
  inline depth = 2
  depth based penalty = 0
  adjusted size = 52
  ANSWER = YES
```

`Lib.dump-simpl`, `insertAxis`: `inline` calls the comparator, `case $wbyStrideRank ww ww1 ww2 ww3 of { __DEFAULT -> : wild1 wild; GT -> case insertAxis wild1 ys of r { __DEFAULT -> : wild2 r } }`, and has no `$wrunRank`; `none` compares inline and calls `runRank` on the tie branch, `case $wrunRank ww3 ww1 of { __DEFAULT -> jump $j; GT -> jump $j1 }`.

Instructions a sort (`~/r/horde-ad/dist-inlcat/cases/O04-comparator-inline/measure.sh`, 100000 and 200000 sorts differenced): `ties`, `inline` 2171.5 and `none` 2296.3; `strides`, `inline` 2150.3 and `none` 1954.1; the bytes equal between the variants (496 a sort at `ties`, 640 at `strides`).

**Reproduces small:** yes, given the exports; with `Lib` exporting only `Axis` and `sortAxes`, both variants compiled to the same code and ran the same instructions.

### O05. INLINE added to a polymorphic list function with no other pragma gives each caller a copy at its own type, and makes a caller permuting two lists one worker, a few instructions a call fewer at no byte; on a small fold over boxed elements, INLINE costs a few a call

**Rule.** A function with no pragma whose body is past the inlining threshold is compiled once, polymorphic, and called (A04, U01); INLINE inlines it at every saturated call with any benefit (A05), where the copy is simplified at the caller's types and alongside the caller's other work. For orthotope's `permute`, a polymorphic list function every caller applies to `Int`s, the copy accesses its elements with a copy of the local `ix` at `Int` (`$wix`, its result cased as `I#`) where the polymorphic one evaluates an element of unknown type (`$wpoly_ix`, cased `__DEFAULT`), and a caller that permutes two lists becomes one worker, `$wtransposeT`, returning an unboxed triple, where without the pragma it makes two calls. The `Int` copy alone does not account for the instructions saved: SPECIALISE at `Int` gives it, and `transposeT` still calls it twice, saving nothing (`specint`); the saving comes with the single worker. On a small fold over a boxed vector, INLINE's cost in a small model is per element, by O02's mechanism (O02's second repro), and orthotope's per call (Seen). Under INLINABLE the module fixing the vector type specialises the fold on it alone, the element's `Ord` passed at run time (the specialisation appendix, "What a call is specialised on"), and a client can specialise that copy again at `Double`, as O02's second repro's does, only where the library's interface carries the copy's unfolding (`canSpecImport`, [compiler/GHC/Core/Opt/Specialise.hs#L911][g330]).

**Seen.** Orthotope's benchmark: INLINE on `permute`, which carries no pragma by P's rule for its type, saved Ranked `transpose` 47 instructions a call, no byte moving, as in the repro. Ranked `transpose` applies `permute` to the shape, and through `transposeT` to the strides, with the same index list.

And INLINE against INLINABLE on the small overloaded folds (`maximumT`, `minimumT`, `productT`, and the Unboxed instance's `vMaximum` and `vMinimum`), callers running up to 39% fewer instructions under INLINE at Storable, Unboxed and Shaped arrays and 6 to 36 more a call at boxed Dynamic and Ranked arrays. The cost is at boxed Dynamic and Ranked `maximumA`, `minimumA` and `productA`, 6 to 36 instructions a call, 1.2 to 2.9%, C5 against C3; and on an earlier tree (R1, `maximumT` INLINABLE) the client's specialisation of `maximumA` at `Double` called `Data.Array.Internal.Dynamic.$w$s$wmaximumT @Double`, passing `$fOrdDouble` at run time, a copy the library's `Dynamic` module had specialised on the vector type alone; R1 was built by this catalogue's compiler, with `maximumA` and `maximumT` INLINABLE, as O02's second repro's `inlinable` has them, and boxed `Dynamic` built `-fpolymorphic-specialisation`. C3's library interface (`Data/Array/Internal/Dynamic.hi`, by `ghc --show-iface`) gives the copy `$w$s$wmaximumT` no unfolding, its entry ending `Inline: [2]]`, so a client can only call it, with the dictionary, where the repro's copy carries `Unfolding: Core: <vanilla>` and its client specialises it. In the benchmark's Core (`OpsDynamic`, C3, INLINABLE, against C6, INLINE) INLINABLE leaves three out-of-line specialisations of `maximumT`'s worker, `$w$s$wmaximumT`, `1` and `2`, at Storable, Unboxed and boxed Doubles, the boxed one still taking a `DG.VecElem Data.Vector.Vector Double` dictionary, and INLINE leaves none. Differenced at two iteration counts in the C5 and C3 binaries, the boxed cost is by the call, the instructions an element equal in both builds: `maximumA` 12 a call more small, at Dynamic and at Ranked, and 9 to 14 large at Dynamic and 7 to 21 at Ranked, at 24.0 an element, and Dynamic `productA` 9 small and 5 to 9 large, at 19.0 (the large size by three runs of 1000 and 2000 calls, 2026-10-16); so not by the element, as in O02's second repro; at small Dynamic `maximumA` the 12 are in the local worker INLINE gives the row, `$wlvl322`, whose loop, run twice a call at [3, 3], stores and reloads one value more an iteration (C8 against C3). By callgrind of the C5 and C3 binaries at the large dense boxed view, 1000 and 2000 calls differenced (the scripts not kept), the element loops run equal instructions, 4799964 a call at `maximumA` and 3800002 at `productA`, and the rest of each operation's code 337 against 325 at Dynamic and Ranked `maximumA`, 9 register moves and two stores and two loads of the C stack more and one `lea` fewer, and 209 against 200 at Dynamic `productA` and 196 against 187 at Ranked, 6 register moves and two stores and two loads of the Haskell stack more and one `lea` fewer. The added instructions lie in the loops over the two-element shape, `maximumA`'s two (the product for `size a` and `maximumT`'s `l`) and `productA`'s one (`productT`'s `l`), each run twice a call. In C5's local workers (`OpsDynamic`'s `$wlvl322` and `$wlvl14`) each loop keeps the view offset, the vector's offset and length, the shape and the strides in registers. It saves them to the Haskell stack around the evaluation of each element of the shape and reloads them after the tail's; the `Array#` stays in its argument slot. At `maximumA` those stores and loads equal C3's: C3's row's loop carries the `Array#` too, and `$w$s$wmaximumT2`'s carries neither the vector's length nor the `Array#`, both of which it takes on the stack. So every added instruction is a register move or C-stack access after a reload. The linear allocator reloads each value into the register it first held in blocks allocated before the loops (`findPrefRealReg`, [compiler/GHC/CmmToAsm/Reg/Linear.hs#L877][g380]; inferred from the block order, the preferences not traced) and then permutes the values into the loop head's registers, through C-stack slots where they form a cycle (`handleComponent`, [compiler/GHC/CmmToAsm/Reg/Linear/JoinToTargets.hs#L334][g381]): view offset, strides and shape in both loops, and the vector's offset, the accumulator and the tail in the second. At `productA`, C3's `$w$s$wproductT2` takes the dictionary in a register and the vector's length on the stack. C5's worker takes no dictionary and gets the length in a register, so it stores and reloads the length at each element: those are the two Haskell-stack stores and loads.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/O05-permute-inline`, variants `inline`, by `-DINL`, and `none`, and `specint`, `none` with `SPECIALISE permute :: [Int] -> [Int] -> [Int]`, by `-DSPECINT`; `run` is `100000`; `measure.sh N`): `transposeT` on a view of rank 4, `permute` INLINE or without a pragma, `Lib` exporting every binding as `Data.Array.Internal` does (so that no binding is inlined for occurring once, A16).

```haskell
{-# LANGUAGE BangPatterns, CPP #-}
-- Everything exported, as orthotope's Data.Array.Internal exports everything.
module Lib (module Lib) where

-- A view: shape, strides, offset.
data T = T ![Int] ![Int] !Int

-- Orthotope's permute: strict in the result's spine and in every element
-- it selects.
#if defined(INL)
{-# INLINE permute #-}
#endif
#if defined(SPECINT)
-- The Int copy alone: transposeT still calls it twice.
{-# SPECIALISE permute :: [Int] -> [Int] -> [Int] #-}
#endif
permute :: [Int] -> [a] -> [a]
permute is xs = go is
  where go [] = []
        go (i : is') = let !y = ix xs i; !r = go is' in y : r
        ix (y : _) 0 = y
        ix (_ : ys) k = ix ys (k - 1)
        ix [] _ = error "permute: violated contract: index out of range"

-- Ranked transpose's shape: the permutation applied to the shape and,
-- through transposeT, to the strides.
transposeT :: [Int] -> T -> T
transposeT is (T sh ss o) = T (permute is sh) (permute is ss) o
```

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import Lib
import System.Environment (getArgs)

-- Opaque, so that each iteration transposes anew.
{-# OPAQUE pass #-}
pass :: Int -> a -> a
pass _ x = x

main :: IO ()
main = do
  [repss] <- getArgs
  let reps = read repss :: Int
      t = T [2, 3, 4, 5] [60, 20, 5, 1] 0
      is = [3, 1, 0, 2]
      loop :: Int -> Int -> Int
      loop 0 !acc = acc
      loop r !acc = case transposeT (pass r is) t of
        T (a : _) (b : _) o -> loop (r - 1) (acc + a + b + o)
        _ -> acc
  print (loop reps 0)
```

`inline`: in `Lib.dump-simpl`, `$wtransposeT` holds both of `permute`'s loops, each element accessed by `case i of { I# ww5 -> case $wix ww3 ww5 of y { I# ipv -> : y r } }`, and `Main`'s loop calls `case $wtransposeT (pass (I# wild) is7) t5 t11 0# of { (# ww3, ww4, ww5 #) ->`. `none`: `transposeT` is `case ds of { T sh ss bx -> T (permute is sh) (permute is ss) bx }`, inlined into `Main`'s loop as `case permute is8 t5 of wild1 { __DEFAULT -> case permute is8 t11 of wild2 { __DEFAULT ->`, and `permute` accesses an element by `case $wpoly_ix xs ww of y { __DEFAULT -> : y r }`.

By `measure.sh 100000` (100000 and 200000 transposes differenced): `inline` 811.0 instructions, `none` 835.0 and `specint` 843.0 a transpose, all 240 bytes.

**Reproduces small:** in part: `permute`, yes, the saving coming with the single worker. The small folds' cost by the call, no: O02's second repro gives a cost by the element instead, by O02's mechanism; the specialisation on the vector type alone, yes, in that repro; its client calling the copy with the `Ord` dictionary at run time, no: there the copy's unfolding is in the library's interface and the client specialises it at `Double`. Not tried: Storable and Unboxed elements, where orthotope's INLINE gained, and `minimumA` and `productA`.

### O06. A dictionary cast by an equality given is not specialised on, so under INLINABLE the callee runs overloaded, and INLINE on a non-recursive callee is the way round it

**Rule.** The specialiser keys a call on a dictionary argument only if `interestingDict` returns `True` for it (the specialisation appendix, "What a call is specialised on"). Equality evidence is a constructor of a class with no methods, whose only argument is a coercion, which is trivial, so `interestingDict` returns `False` for it ((ID6) of Note [Interesting dictionary arguments]). So a specialisation of a function with `t ~ u` in its context keeps the evidence as a parameter, the dictionary it passes on to a callee at `u` is cast with that parameter, the call cannot float to a specialisation of the callee, and the callee is called overloaded, its dictionary passed; the simplifier removes the reflexive cast later, but the specialiser does not run again. INLINE on a non-recursive callee replaces the call by the callee's body (U03), so no specialisation of the callee is needed, which is how it works round this. The uncommitted Specialise.hs patch does not touch `mkCallUDs'` or `interestingDict`. Filed as GHC [#27920](https://gitlab.haskell.org/ghc/ghc/-/work_items/27920), `docs/ghc-issue-equality-cast-dictionary.md` in horde-ad, with its workarounds (`-flate-specialise`, a SPECIALISE pragma for the callee, calling the callee at the given's own type).

**Seen.** Orthotope's `Convert` instances have `a ~ b` in their contexts (`Data/Array/Convert.hs`), and under INLINABLE on `fromStorable` a client's specialised `convert` called its worker with the Storable dictionary, 3.45 times the instructions of INLINE on a dense array of 200000 Doubles converted and summed; orthotope keeps INLINE there, with an `INLINE:` comment.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/O06-equality-cast-dictionary`, variant `base`, `-O -ddump-simpl -dsuppress-all -dsuppress-uniques -dno-typeable-binds`): the filed reproducer, unchanged.

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

`Repro.dump-simpl`: `outer` is specialised at `Double`, `sumTo` is not, and there is no `$s$wsumTo`:

```
$wsumTo $fNumDouble ww1 ($s$wouter @~<Co:1> ns eta1)
```

**Reproduces small:** yes, the filed reproducer. `sumTo` being recursive, INLINE does not work round it here; that it does on a non-recursive callee rests on orthotope's `fromStorable`, as the filed issue says.

### O07. List fusion needs the producer and the consumer inlined into one expression: a producer specialised under INLINABLE, a consumer called out of line, or a bang on the consumer's list builds the list

**Rule.** The rule `fold/build`, `foldr k z (build g) = g k z` ([libraries/ghc-internal/src/GHC/Internal/Base.hs#L1862][g382]), fires only where `foldr`'s list argument matches `build g`, as written or through a variable whose unfolding is expandable (`match` on a variable, [compiler/GHC/Core/Rules.hs#L1137][g161], Note [Expanding variables]; `expandUnfolding_maybe`, [compiler/GHC/Core.hs#L2007][g383], which expands a `CoreUnfolding` marked expandable and nothing else), so both the producer and the consumer have to be inlined at the one expression. INLINE inlines a producer at a saturated call with any benefit (A05); an INLINABLE producer past the size threshold (A04) is instead specialised at the client's types and called, and its specialisation returns a list, built cell by cell and then consumed: a producer that is overloaded and large, as orthotope's `toListT` is, fuses only under INLINE. On the consumer's side, orthotope's `genericUnsafeConcatN` consumes its list by one `foldr` so that a list a `build` produces is never built. Inlined into a client whose rows are a list comprehension, a `build`, through a method that passes the list straight on, `vUnsafeConcatN = genericUnsafeConcatN` or `vUnsafeConcatN a b = genericUnsafeConcatN a b`, the two fuse. A bang on the list, `vUnsafeConcatN a !b = genericUnsafeConcatN a b`, stays in the INLINE unfolding as a `case` on the list (U15), so at the client the `build` is the scrutinee of a `case` and `foldr`'s argument is the case binder, whose unfolding records only that it is evaluated: the rule cannot match the `build`, and the client builds the whole list, a cell and a slice for each row, before the fill walks it. Without a pragma the method is not inlined at all, its body far past the threshold (A04), so the client passes it the list built, and, the method carrying no pragma, it is not specialised either (the specialisation appendix, "Which imported functions are specialised") and runs with the `Unbox` dictionary as an argument.

**Seen.** `docs/perf-checklist.md` I3, the first of what only inlining gives: `toListT` meets its consumer only when inlined (F1), so INLINABLE would lose list fusion. And orthotope's `vUnsafeConcatN` in `Data/Array/Internal/DynamicU.hs`'s `instance Vector V.Vector` (at "Condense the account of unorderedRouteT's sort and merge" on `pr-mikolaj-toVectorListT`, INLINE and point-free): in a build of 2026-10-12 that removed INLINE widely, RankedU and ShapedU called the method out of line through DynamicU (7 and 11 calls of `$fVectorVector_$cvUnsafeConcatN`, OpsRanked a local specialised copy `$w$s$fVectorVector_$cvUnsafeConcatN`), behind Unboxed `concatOuter`, `ravel`, `rerank` and `rerank2` at the small and empty sizes, the one of that round's 186 instance-method changes that cost; V1, with the 52 `Vector` instance methods INLINABLE, cost up to 600 bytes a call at the same rows, which of the methods cost them was not measured; and banging every argument the demands give as strict in all four instances at once, this method's as `vUnsafeConcatN a !b = genericUnsafeConcatN a b`, cost the same Unboxed cells 128 to 600 bytes a call (NB; the `Vector` class's bangs alone, NBv, kept the cost), which method's bang carries the cost was not measured.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/O07-fusion-needs-inline`, variants `inline`, by `-DINL`, and `inlinable`, each with `-ddump-rule-firings`; `run` is `100000 100`; `measure.sh K N`): a sum by `foldl'` of a dense view of 100000 Doubles, the producer `toListV`, overloaded on the container class and with two routes as `toListT` has, INLINE against INLINABLE.

```haskell
{-# LANGUAGE BangPatterns, CPP #-}
module Lib (Vec (..), View (..), toListV, mkView) where

import Data.Array (Array, listArray)
import Data.Array.Base (unsafeAt)
import GHC.Exts (build)

-- A container class, as orthotope's Vector.
class Vec v where
  vlen :: v a -> Int
  vat :: v a -> Int -> a

instance Vec (Array Int) where
  vlen a = length a
  vat = unsafeAt

-- A view: length, stride, offset, values.
data View v a = View !Int !Int !Int !(v a)

mkView :: Int -> Int -> [a] -> View (Array Int) a
mkView n s xs = View n s 0 (listArray (0, n * s - 1) xs)

-- The elements as a good producer, a build, on two routes as orthotope's
-- toListT has them.
#if defined(INL)
{-# INLINE toListV #-}
#else
{-# INLINABLE toListV #-}
#endif
toListV :: Vec v => View v a -> [a]
toListV (View n s o v)
  | n == 0 = []
  | s == 1 = build (\cons nil ->
      let go !i | i >= n = nil
                | otherwise = cons (vat v (o + i)) (go (i + 1))
      in go 0)
  | otherwise = build (\cons nil ->
      let go !i !p | i >= n = nil
                   | otherwise = cons (vat v p) (go (i + 1) (p + s))
      in go 0 o)
```

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import Data.Array (Array)
import Data.List (foldl')
import Lib
import System.Environment (getArgs)

-- Opaque, so that each iteration sums anew.
{-# OPAQUE pass #-}
pass :: Int -> a -> a
pass _ x = x

-- A good consumer of the producer's list.
{-# NOINLINE total #-}
total :: View (Array Int) Double -> Double
total w = foldl' (+) 0 (toListV w)

main :: IO ()
main = do
  [ks, repss] <- getArgs
  let k = read ks :: Int
      reps = read repss :: Int
      w = mkView k 1 [fromIntegral i | i <- [0 .. k - 1]]
      loop :: Int -> Double -> Double
      loop 0 !acc = acc
      loop r !acc = loop (r - 1) (acc + total (pass r w))
  print (loop reps 0)
```

`inline`: `Main.dump-rule-firings` has `Rule fired: fold/build (GHC.Internal.Base)` three times (`inlinable` once, outside `total`), and `Main.dump-simpl` has no `toListV`. `inlinable`: `Main.dump-rule-firings` has `Rule fired: SPEC/Main toListV @(Array Int) @_ (Main)`, and `total`'s worker folds the list the specialisation returns:

```
$wtotal = \ ww ww1 ww2 ww3 -> $wgo1 ($w$s$wtoListV ww ww1 ww2 ww3) 0.0##
```

By `measure.sh 100000 100` (100 and 200 sums differenced), an element: `inline` 23.00 instructions and 0.00 bytes, `inlinable` 103.92 instructions and 96.00 bytes.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/O07-vunsafeconcatn-out-of-line`, variants `pointfree`, `named` (`-DNAMED`), `banged` (`-DBANGED`) and `nopragma` (`-DNOPRAGMA`, with `-dinline-check` on the method); `post` counts the `fold/build` firings in each variant's `Main.dump-rule-firings` into `~/r/horde-ad/dist-inlcat/cases/O07-vunsafeconcatn-out-of-line/out/head/VARIANT/rules.txt`; `measure.sh N` gives instructions and bytes a call of `ravel` from N and 2N iterations): the class with its one method, `genericUnsafeConcatN` as orthotope has it, the Unboxed instance in the four forms, and a client ravelling 25 rows of 8 Doubles.

```haskell
{-# LANGUAGE BangPatterns, CPP, TypeFamilies #-}
module Lib (Vector (..), genericUnsafeConcatN) where

import Control.Exception (assert)
import Data.Kind (Constraint, Type)
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Generic.Mutable as VGM
import qualified Data.Vector.Unboxed as V

-- orthotope's Vector class, its one method here.
class Vector (v :: Type -> Type) where
  type VecElem v :: Type -> Constraint
  vUnsafeConcatN :: (VecElem v a) => Int -> [v a] -> v a

-- orthotope's concatenation into one buffer, by one foldr.
{-# INLINE genericUnsafeConcatN #-}
genericUnsafeConcatN :: (VG.Vector w a) => Int -> [w a] -> w a
genericUnsafeConcatN n vs = VG.create $ do
  out <- VGM.unsafeNew n
  let step x k = \ !i -> do
        let !m = VG.length x
        assert (i + m <= n) $ VG.unsafeCopy (VGM.unsafeSlice i m out) x
        k (i + m)
  foldr step (\ !i -> assert (i == n) $ return ()) vs 0
  return out

-- DynamicU's instance, its method as the base, named, banged or without
-- a pragma.
instance Vector V.Vector where
  type VecElem V.Vector = V.Unbox
#if defined(NAMED)
  {-# INLINE vUnsafeConcatN #-}
  vUnsafeConcatN a b = genericUnsafeConcatN a b
#elif defined(BANGED)
  {-# INLINE vUnsafeConcatN #-}
  vUnsafeConcatN a !b = genericUnsafeConcatN a b
#elif defined(NOPRAGMA)
  vUnsafeConcatN = genericUnsafeConcatN
#else
  {-# INLINE vUnsafeConcatN #-}
  vUnsafeConcatN = genericUnsafeConcatN
#endif
```

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import qualified Data.Vector.Unboxed as V
import Lib
import System.Environment (getArgs)

-- Opaque, so that each iteration concatenates anew.
{-# OPAQUE pass #-}
pass :: Int -> V.Vector Double -> V.Vector Double
pass _ x = x

-- A ravel of 25 rows of 8: the rows a list a build produces.
ravel :: V.Vector Double -> V.Vector Double
ravel v = vUnsafeConcatN 200 [V.unsafeSlice (8 * i) 8 v | i <- [0 .. 24]]

main :: IO ()
main = do
  [ns] <- getArgs
  let n = read ns :: Int
      v = V.generate 200 fromIntegral
      go :: Int -> Double -> Double
      go 0 !acc = acc
      go k !acc = go (k - 1) (acc + V.unsafeIndex (ravel (pass k v)) 199)
  print (go n 0)
```

The counts: `fold/build in Main: 2` at `pointfree` and `named`, `fold/build in Main: 1` at `banged` and `nopragma`. `banged`'s `Main.dump-simpl`, whitespace collapsed: the rows built as list cells by a local `go2`, each holding the slice `(Vector (+# bx (*# 8# x)) 8# bx2)`, and the list forced before the fill:

```
case go2 0# of b { __DEFAULT -> runRW#
```

which `pointfree` and `named` do not build. `nopragma`'s: the method called with the dictionary and the list:

```
case ($fVectorVector_$cvUnsafeConcatN ($fUnboxDouble `cast` <Co:4>) lvl19 (let { v1 = pass (I# wild) v } in letrec { go2
```

and its `build.log`: `guidance IF_ARGS [30 0 0] 401 0`, `adjusted size = 321`, `ANSWER = NO`. `banged`'s `Lib.iface` keeps `Inline: (sat-args=2),`, the bang in the unfolding. `measure.sh 1000000`:

```
pointfree: 1421.2 instructions, 1632.0 bytes a call
named: 1421.2 instructions, 1632.0 bytes a call
banged: 4749.3 instructions, 4672.0 bytes a call
nopragma: 9521.1 instructions, 6360.0 bytes a call
```

The bang costs 3040 bytes a call, 121.6 a row of the 25.

**Reproduces small:** in part: the producer specialised under INLINABLE, and the consumer's bang and its call out of line, each building the list, yes. Orthotope's specialised out-of-line copy in the build of 2026-10-12 was not reproduced.

### O08. A specialisation keys on types and dictionaries, never on a value argument: a property of the arguments at a call, such as a known function or two arguments that are one array, reaches only an inlined copy

**Rule.** The specialiser makes a copy for a call's type and dictionary arguments and leaves every value argument a parameter of the copy (the specialisation appendix, "What a call is specialised on"), so a client calling an INLINABLE function at one type gets one copy for every such call, and no property of its value arguments at a call site reaches it; inlined, the body meets the call's own arguments. So the specialisation of an INLINABLE higher-order function, past the size threshold and so called (A04), applies its function argument as an unknown function: demand analysis cannot establish that the function is strict, and a lazy accumulator stays lazy, a thunk an element. INLINE puts the body at the call (A05), where the argument is the known function and the loop is compiled with it. Under INLINE the call must still be saturated by the definition's left-hand side (E01): written point-free, `total = reduceV (+) 0` leaves `reduceV` unapplied to its view, and it is specialised as INLINABLE is, with the same cost. Likewise for two arguments that are one variable: called as `compare a a`, the inlined `foldPartsT` takes the strides, the offset and the vector of `x` and `y` from the same fields, and `offset y - offset x` folds to 0 (`IntSubOp`'s `equalArgs >> retLit zeroi` in `primOpRules`, [compiler/GHC/Core/Opt/ConstantFold.hs#L423][g384]), so the element loop compares each part at one offset, and its inner loop accesses one vector's fields; the specialisation, called with those fields twice, computes the second offset at each element, `+# ww12 d`, and keeps the fields of two vectors. Eta-expanding the INLINABLE `compareT` changes none of this: the client's Core is the same but for names. Called with two distinct arrays, the advantage can reverse: in the benchmark's summed cell, where the caller keeps the second comparison's shape lists live across the inlined loop and every general register is taken at the loop head, the inlined loop spills more than the specialisation's (Seen); in its forced cell, where each comparison runs in a closure of its own, the two run the same instructions. Which values cause the client copy's one extra spill was not traced.

**Seen.** `docs/perf-checklist.md` I3, the third of what only inlining gives: INLINABLE `reduce`, `rerank`, `rerank2` and `traverseA` in orthotope were specialised but not inlined, leaving a thunk an element in `reduce` and 1.6 times the time on `rerank2`; the point-free form is E01's. And orthotope's `compareT`, INLINE over an INLINE `foldPartsT` (`Data/Array/Internal.hs` at "Give each binding the pragma its kind calls for", its `INLINE:` comment): made INLINABLE, as `equalT` is, point-free or eta-expanded, it ran `compare a a` on a transposed [400, 500] view of Doubles at 1.12 to 1.17 times INLINE's instructions in a probe of 2026-10-10 (against "Let a client specialise fillStrided", with a NOINLINE function perturbing each call), about 5 an element more at Storable and Unboxed elements and 17 boxed; the Core of the INLINABLE forms was not read. The probe compared an array with itself because the benchmark's row then did, `Call "compare" (\ a -> compare a a) t` from "Add a benchmark timing every operation of the array modules" until "Time each operation at a small size and on every arm"; the `INLINE:` comment rests on that probe alone. In the benchmark itself, which has compared a view with its normalised copy since "Time each operation at a small size and on every arm", INLINABLE was measured at "Build the boxed and Unboxed singletons without vector's stream loop". It allocates INLINE's bytes in every `Dynamic/compare` cell. In instructions it is the cheaper only in the summed table at the large size, by 2 to 5 an element at most views. In the forced table it runs INLINE's instructions at the large size, except 2 more an element on the dense boxed view, and at the small and empty sizes it runs 31 to 126 more a call in both tables (1.01 to 1.18 times). Built through `tools/align-as.py`, it took 0.867 and 0.905 of INLINE's time on the large strided summed cells at Storable and Unboxed, below INLINE in each of 8 rounds, and 0.985 to 0.993 on the three forced cells timed, within the rounds' spread, its cycles on the large Storable one 1.085 times INLINE's. Unaligned, the forced Storable cell took 1.13 times, which aligning removed, so a placement effect. Forced, each comparison runs in a closure of its own, a component of the unboxed tuple the cell returns let-bound by CorePrep (`cpeArg`, [compiler/GHC/CoreToStg/Prep.hs#L1524][g385]): ten values are live in its loop and one general register is spare. Summed, both comparisons are inlined into one function, the second a join point the first's loops jump to. That keeps both arrays' shape lists live through the first comparison's loops, and the first result through the second's, so all eleven general registers are taken at each loop head. On each back edge the allocator's fixup block reloads three values the loop does not use, and the loop body stores them again. Each summed loop makes 2 more C-stack loads and 1 more store an element than the forced one, on the strided Storable cell. A base-only model, one loop over an array of Ints that uses four fields of an eight-field strict record whose other four are used only after it, stores two of those four and reloads them on every element, its header keeping its first entry's assignment (O02): 17 instructions an element on HEAD, 9.14.1 and 9.12.4, against 13 with `-fregs-graph` on HEAD; with the unused fields last in the record, the loop moves two of the fields it reads through the stack instead. It is posted as a comment on GHC [#27742](https://gitlab.haskell.org/ghc/ghc/-/work_items/27742), `docs/ghc-issue-unread-values-reload-27742-comment.md` in horde-ad. A client copy of `compareT`, called through an INLINE `compare` as DynamicG's `Ord` forwards, over the `foldPartsT` of orthotope built at "Condense the account of unorderedRouteT's sort and merge" (its `foldPartsT` that of "Give each binding the pragma its kind calls for"), on the probe's view (`~/r/horde-ad/dist-inlcat/cases/O08-comparet-orthotope`, `measure.sh 20`), puts INLINE ahead only at `compare a a`, by 1 instruction an element at Storable and Unboxed elements and by 17 boxed, and INLINABLE ahead on two arrays and on one array passed twice, by 3 at Storable and Unboxed elements and 7 boxed with equal strides, and by 3, and 4 boxed, on the benchmark row's arguments, a view against its normalised copy; bytes are equal throughout. At Storable elements the inlined copy's loop, read in that client's assembly, runs 39 instructions a part, one part an element on this view, against the specialisation's 36: one more value spilled to the C stack and reloaded each part, and a back edge through an out-of-line block. At boxed elements and `compare a a` that client's own code runs 102.00 instructions an element specialised against 85.00 inlined (`~/r/horde-ad/dist-inlcat/cases/O08-boxed-compare-spills`, its boxed variants with assembly dumps; `measure-cg.sh 2`, callgrind with the case's count of stack traffic by kind): 15 stores to the C stack against 5, 12 loads from it against 4, 14 stores to the Haskell stack against 13, 9 `add` against 8 and 9 register moves against 12, the other kinds equal. At the head of the specialisation's per-part loop 16 values are live against the 11 general registers the code generator allocates on x86-64, the inlined copy's 12: both pass the vectors' fields to the inner loop as join-point parameters while the originals stay live, four distinct values in the specialisation (`jump $wloop ww2 ww3 ww11 ww12 0#`), one vector's two fields twice in the inlined copy (`jump $wloop ww4 ww6 ww4 ww6 0#`), and the specialisation's enclosing loop carries 10 values against 7. The linear allocator keeps 5 of the specialisation's in C-stack slots at the loop head and 1 of the inlined copy's, stored and reloaded on every element's path back to it, its fixup blocks breaking register cycles through further slots (`joinToTargets_again`, [compiler/GHC/CmmToAsm/Reg/Linear/JoinToTargets.hs#L144][g386]; `handleComponent`, [#L334][g381]). And horde-ad's `OpsConcrete`: its INLINEs, whose functions were inlined at every call site, were removed, and those on its higher-order operations restored, so that the function a caller at a known element type passes is inlined into the vector loop (commits 0a8d839b3 and 7080e577d).

**Repro** (`~/r/horde-ad/dist-inlcat/cases/O08-known-function-argument`, variants `inline`, `inlinable`, and `inline-pointfree` = `inline` with `-DPOINTFREE`; `run` is `100000 100`; `measure.sh K N`): a sum by `reduceV (+) 0` of a dense view of 100000 Doubles, `reduceV` overloaded on the container class, with a lazy accumulator and four routes as a library fold might have.

```haskell
{-# LANGUAGE BangPatterns, CPP #-}
module Lib (Vec (..), View (..), reduceV, mkView) where

import Data.Array (Array, listArray)
import Data.Array.Base (unsafeAt)

-- A container class, as orthotope's Vector.
class Vec v where
  vat :: v a -> Int -> a

instance Vec (Array Int) where
  vat = unsafeAt

-- A view: length, stride, offset, values.
data View v a = View !Int !Int !Int !(v a)

mkView :: Int -> Int -> [a] -> View (Array Int) a
mkView n s xs = View n s 0 (listArray (0, n * s - 1) xs)

-- A left fold of the view's elements with a function argument and a lazy
-- accumulator, as orthotope's reduce.
#if defined(INL)
{-# INLINE reduceV #-}
#else
{-# INLINABLE reduceV #-}
#endif
reduceV :: Vec v => (a -> a -> a) -> a -> View v a -> a
reduceV f z (View n s o v)
  | n == 1 = f z (vat v o)
  | s == 0 = let x = vat v o
                 go acc !i | i >= n = acc
                           | otherwise = go (f acc x) (i + 1)
             in go z 0
  | s == 1 = let go acc !i | i >= n = acc
                           | otherwise = go (f acc (vat v (o + i))) (i + 1)
             in go z 0
  | otherwise = let go acc !i !p | i >= n = acc
                                 | otherwise = go (f acc (vat v p)) (i + 1) (p + s)
                in go z 0 o
```

```haskell
{-# LANGUAGE BangPatterns, CPP #-}
module Main (main) where

import Data.Array (Array)
import Lib
import System.Environment (getArgs)

-- Opaque, so that each iteration sums anew.
{-# OPAQUE pass #-}
pass :: Int -> a -> a
pass _ x = x

{-# NOINLINE total #-}
total :: View (Array Int) Double -> Double
#if defined(POINTFREE)
total = reduceV (+) 0
#else
total w = reduceV (+) 0 w
#endif

main :: IO ()
main = do
  [ks, repss] <- getArgs
  let k = read ks :: Int
      reps = read repss :: Int
      w = mkView k 1 [fromIntegral i | i <- [0 .. k - 1]]
      loop :: Int -> Double -> Double
      loop 0 !acc = acc
      loop r !acc = loop (r - 1) (acc + total (pass r w))
  print (loop reps 0)
```

`Main.dump-simpl`. `inline`: no `reduceV`; `total`'s worker accumulates unboxed, `case ipv of { D# y -> jump $wgo (+## ww4 y) (+# ww5 1#) (+# ww6 wild1) }`. `inlinable`: `$wtotal = \ ww ww1 ww2 ww3 -> $w$s$wreduceV plusDouble lvl ww ww1 ww2 ww3`, the specialisation still polymorphic in the element, `$w$s$wreduceV = \ @a f z ww ww1 ww2 ww4 ->`, and its loop `jump $wgo (f acc (case indexArray# ww4 ww6 of { (# ipv #) -> ipv })) (+# ww5 1#) (+# ww6 wild1);`. `inline-pointfree`: `total = $sreduceV plusDouble total1`.

By `measure.sh 100000 100` (100 and 200 sums differenced), an element: `inline` 23.00 instructions and 0.00 bytes; `inlinable` and `inline-pointfree` each 884.56 instructions and 145.10 bytes.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/O08-comparet-inlinable`, variants `inline` (`-DINL`), `inlinable` and `inlinableEta` (`-DETA`) at Storable elements, `inlineTwo` and `inlinableTwo` (`-DTWO`) comparing two arrays, and `inlineBoxed` and `inlinableBoxed` (`-DBOXED`) at boxed elements; `measure.sh N` gives instructions and bytes a call from N and 2N iterations): orthotope's `T`, a two-constructor `Route`, its odometer `offsetsT`, `routePartsT`, `foldPartsT` and `compareT`, at rank 2, and the Dynamic arrays' INLINE `compare` forwarding to `compareT`, called on a transposed [40, 50] view of 2000 Doubles.

```haskell
{-# LANGUAGE BangPatterns, CPP, ScopedTypeVariables #-}
module Lib (T (..), compareT) where

import qualified Data.Vector.Generic as G

-- orthotope's array, its route and its fold over parts, at rank 2.
data T v a = T ![Int] !Int !(v a)

data Axis = Axis !Int !Int  -- stride and extent

data Route = RSlice !Int !Int | RFill !Axis [Axis] !Int
  -- RFill: the innermost axis, the axes outside it innermost first, offset

{-# INLINE routeT #-}
routeT :: [Int] -> T v a -> Route
routeT [m, n] (T [s, t] o _)
  | t == 1 && s == n = RSlice o (m * n)
  | otherwise = RFill (Axis t n) [Axis s m] o
routeT _ _ = error "routeT: rank 2 only"

-- orthotope's odometer, its walk and its step, as at "Give each binding the
-- pragma its kind calls for".
data Odometer = OdoLevel !Int !Int !Axis !Odometer | OdoDone

stepOdometer :: Odometer -> Odometer
stepOdometer OdoDone = OdoDone
stepOdometer (OdoLevel o c axis@(Axis s d) outer)
  | c > 1 = OdoLevel (o + s) (c - 1) axis outer
  | otherwise = case stepOdometer outer of
      OdoDone -> OdoDone
      next@(OdoLevel o' _ _ _) -> OdoLevel o' d axis next

{-# INLINE offsetsT #-}
offsetsT :: forall b. Axis -> [Axis] -> Int -> (Int -> b -> b) -> b -> b
offsetsT (Axis sk dk) above !start step nil =
  let block :: Int -> Odometer -> b
      block o outer =
        let go :: Int -> Int -> b
            go !i !p
              | i < dk = step p (go (i + 1) (p + sk))
              | otherwise = case stepOdometer outer of
                  OdoDone -> nil
                  next@(OdoLevel oNext _ _ _) -> block oNext next
        in  go 0 o
  in  block start
            (foldr (\axis@(Axis _ d) outer -> OdoLevel start d axis outer)
                   OdoDone above)

-- The parts a route reads, by the step and nil of a right fold.
{-# INLINE routePartsT #-}
routePartsT :: Route -> (Int -> Int -> b -> b) -> b -> b
routePartsT route step nil = case route of
  RSlice o l -> step o l nil
  RFill axis outer o -> offsetsT axis outer o (\p rest -> step p 1 rest) nil

{-# INLINE foldPartsT #-}
foldPartsT :: G.Vector v a
           => (r -> r -> r) -> r -> (v a -> v a -> Int -> Int -> Int -> r)
           -> [Int] -> T v a -> T v a -> r
foldPartsT c e goWith s x@(T sx ox vx) y@(T sy oy vy)
  | l == 0 = e
  | sx == sy = routePartsT (routeT s x) (\p n rest -> go p (p + d) n `c` rest) e
  | otherwise = case (routeT s x, routeT s y) of
      (RSlice ox' _, RSlice oy' _) -> go ox' oy' l
      (rx, RSlice oy' _) ->
        routePartsT rx (\p n rest !q -> go p q n `c` rest (q + n)) (\ !_ -> e) oy'
      (RSlice ox' _, ry) ->
        routePartsT ry (\p n rest !q -> go q p n `c` rest (q + n)) (\ !_ -> e) ox'
      _ -> error "foldPartsT: two views not modelled"
  where
    !l = product s
    !d = oy - ox
    go = goWith vx vy

#if defined(INL)
{-# INLINE compareT #-}
#else
{-# INLINABLE compareT #-}
#endif
compareT :: (G.Vector v a, Ord a) => [Int] -> T v a -> T v a -> Ordering
#if defined(ETA)
compareT s x y = foldPartsT (<>) EQ cmpWith s x y
#else
compareT = foldPartsT (<>) EQ cmpWith
#endif
  where cmpWith u w !ox !oy !k = loop u w 0
          where loop !u' !w' !i
                  | i >= k = EQ
                  | otherwise =
                      case compare (G.unsafeIndex u' (ox + i))
                                   (G.unsafeIndex w' (oy + i)) of
                        EQ -> loop u' w' (i + 1)
                        o -> o
```

```haskell
{-# LANGUAGE BangPatterns, CPP #-}
module Main (main) where

#if defined(BOXED)
import qualified Data.Vector as V
#elif defined(UNBOXED)
import qualified Data.Vector.Unboxed as V
#else
import qualified Data.Vector.Storable as V
#endif
import Lib
import System.Environment (getArgs)

-- The Dynamic arrays: a shape and a view, compared as DynamicG's Ord does.
data A = A [Int] (T V.Vector Double)

instance Eq A where
  a == b = compare a b == EQ

instance Ord A where
  {-# INLINE compare #-}
  compare (A s v) (A s' v') = compare s s' <> compareT s v v'

-- Opaque, so that each iteration compares anew and nothing about the array
-- is known at the call.
{-# OPAQUE pass #-}
pass :: Int -> A -> A
pass _ x = x

main :: IO ()
main = do
  [ns] <- getArgs
  let n = read ns :: Int
      -- A transposed [40, 50] view of a [50, 40] array, compared with itself
      -- as the probe's compare a a, or with a copy (TWO).
      v = V.generate 2000 fromIntegral :: V.Vector Double
      x = A [40, 50] (T [1, 40] 0 v)
      y = A [40, 50] (T [1, 40] 0 (V.map id v))
      go :: Int -> Int -> Int
      go 0 !acc = acc
#if defined(TWO)
      go k !acc =
        let a = pass k x
            b = pass k y
        in go (k - 1) (acc + fromEnum (compare a b))
#else
      go k !acc = let a = pass k x in go (k - 1) (acc + fromEnum (compare a a))
#endif
  print (go n 0)
```

`Main.dump-simpl`, whitespace collapsed. `inline`, `compare a a` inlined into the client's loop: the part compared at one offset, read at the same index in both vectors, and its loop given one vector's fields twice:

```
case readDoubleOffAddr# ww8 (+# ww7 ww12) realWorld# of
case readDoubleOffAddr# ww10 (+# ww7 ww12) realWorld# of
jump $wloop ww3 ww4 ww3 ww4 0#
```

`inlinable` (and `inlinableEta`): the client calls the specialisation with the same fields twice, and inside it the offsets differ by a parameter and the loop takes two vectors:

```
case $w$s$wcompareT s ww2 ww3 ww6 ww7 ww2 ww3 ww6 ww7 of
let { d = -# ww5 ww1 } in
let { ipv1 = +# ww12 d } in
jump $wloop ww2 ww3 ww6 ww7 0#
```

`inlineBoxed` accesses both arrays at one index likewise, `case indexArray# ww9 (+# ww8 (+# ww7 ww12)) of` and `case indexArray# ww11 (+# ww10 (+# ww7 ww12)) of`; `inlineTwo` enters its loop with two vectors' fields, `jump $wloop ww3 ww4 ww6 ww7 0#`. `measure.sh 20000`, a call being 2000 elements:

```
inline: 64631.1 instructions, 1680.0 bytes a call
inlinable: 74804.2 instructions, 1680.0 bytes a call
inlinableEta: 74804.2 instructions, 1680.0 bytes a call
inlineTwo: 80791.9 instructions, 1680.0 bytes a call
inlinableTwo: 74840.9 instructions, 1680.0 bytes a call
inlineBoxed: 156554.3 instructions, 1680.0 bytes a call
inlinableBoxed: 212804.5 instructions, 1680.0 bytes a call
```

INLINABLE costs about 5.1 instructions an element more at `compare a a` at Storable elements and 28.1 boxed, at equal bytes; with two arrays INLINE costs about 3.0 an element more.

**Reproduces small:** in part: the known function, yes, given a body past the threshold: with two routes the INLINABLE specialisation was inlined, at adjusted size 88 against 90 (`-dinline-check`), the known function argument earning a discount of 60 (guidance `IF_ARGS [60 0 0 30 0 20] 228 0`); with three it was inlined too, but its accumulator stayed a lazy box, 30.32 instructions and 16.00 bytes an element. The equal arguments, yes: the cost's direction and its independence of eta-expansion, at orthotope's size at Storable elements, about 5 instructions an element and 1.16 times INLINE's instructions against its 1.12 to 1.17, and above it boxed, 28 an element against 17; the mechanism found is the probe's `compare a a`, which a client comparing two arrays does not have. Another form of the model, its odometer a fixed two-level loop, with the shape and views known constants at the call, ran INLINE at 0.90 times INLINABLE's instructions by constant folding the route; with them opaque, at 1.08 times on two arrays and 1.03 times on `compare a a`, so the figure depends on the walk's form.

### O09. A client's specialisation of an INLINABLE function meets float-out before the simplifier, and a loop that would be a join point floats out as a closure

**Rule.** The specialiser runs just before the first float-out (the specialisation appendix, "Where the specialiser sits in the pipeline"), which runs with `floatOutLambdas = Just 0`. Its copy of an imported function carrying a pragma is that function's unfolding template ([compiler/GHC/Core/Opt/Specialise.hs#L911][g330], `canSpecImport`), for INLINABLE the stable unfolding, the right-hand side as written (U04), here instantiated and not yet simplified, so a local loop in it is not yet a join point and float-out may float it out of the function that would have tail-called it; once floated, the loop is a closure allocated on every call, and the function that calls it captures it. Under INLINE the body is inlined at the call and simplified there, where the loop becomes a join point. Filed as GHC [#27894](https://gitlab.haskell.org/ghc/ghc/-/work_items/27894), `docs/ghc-issue-specialise-float-out-join-point.md` in horde-ad, with its workarounds (`-fno-full-laziness`, `-fliberate-case`, `-fstg-lift-lams`, or a loop bound that mentions a variable of the enclosing function). The issue also lists rewritings that are not workarounds. Writing `go` with its `State#` lambda explicit changes nothing while the bangs stay outside the lambda or the arguments are `seq`ed at its head; forcing `op` and `b` only in the recursive branch leaves `go` lazy in them, since the base case does not force them, and the worker the demand gives ([compiler/GHC/Core/Opt/WorkWrap/Utils.hs#L624][g203], `canUnboxArg`) takes them boxed, so the floated loop allocates two `I#` an iteration. ``lazy outPos `seq` return ()`` as the base case leaves `go` a join point of `$wrun`, but `$wrun` then takes the position boxed, to pass the box to `lazy`, and the outer level boxes the position it passes down at every iteration; ``outPos `seq` return ()`` in its place leaves the loop floated: `outPos` is banged, so inside `go` the `seq` on it is a `case` on an evaluated variable, which `Lib`'s simplification of the stable unfolding (U10) drops (`rebuildCase`'s case for a plain `seq`, [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L3307][g387]), leaving `go` with no free variable of `run`; `lazy` is NOINLINE ([libraries/ghc-internal/src/GHC/Internal/Magic.hs#L86][g388]) and removed only by CorePrep (`cpe_app`, [compiler/GHC/CoreToStg/Prep.hs#L1074][g389]), so `case lazy outPos` stays in the template, and in the importer the floated `lazy o` goes only as far as `run`'s lambda, keeping `go` inside `run`, where it becomes a join point.

**Seen.** `docs/perf-checklist.md` I3, the fourth of what only inlining gives: with orthotope's strided fill INLINABLE, a specialised copy met float-out before simplification, and a loop became a heap closure of 56 to 64 bytes a call, with 8 more in the closure capturing it. The variants that are not workarounds are in `docs/ghc-issue-specialise-float-out-join-point.md` in horde-ad, section "Workarounds", its last paragraph (commit 3828310cb, "Add the filed texts of GHC [#27893](https://gitlab.haskell.org/ghc/ghc/-/work_items/27893) and GHC [#27894](https://gitlab.haskell.org/ghc/ghc/-/work_items/27894)"): the explicit `State#` lambda leaves 7.25 MB and gives 137 MB "with the arguments evaluated inside the lambda instead", the `seq` leaves 7.25 MB, and `lazy outPos` keeps `go` in `run` but gives 12.85 MB.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/O09-specialise-float-out-join-point`, variants `inlinable`, the filed reproducer; `nofl`, `inlinable` with `-fno-full-laziness`; `inline`, `fill` INLINE by `-DINL`; and the issue's rewritings that are not workarounds: `state`, `go` with its `State#` lambda explicit and its bangs outside it, by `-DSTATE`; `stateseq`, the arguments `seq`ed at the head of that lambda, by `-DSTATESEQ`; `statein`, `op` and `b` forced inside it in the recursive branch only, by `-DSTATEIN`; `seqout`, ``outPos `seq` return ()`` as the base case, by `-DSEQOUT`; `lazyout`, ``lazy outPos `seq` return ()``, by `-DLAZYOUT`; `run` is empty): the filed reproducer, `Repro.hs` saved as `Main.hs` and CPP switches added for the pragma and the rewritings. The issue gives the `State#` forms as `go !k !op !b = IO $ \s -> ...` and in words; `statein` is the form found to give its 137 MB, `stateseq` a form that does not.

```haskell
{-# LANGUAGE BangPatterns, CPP, MagicHash, UnboxedTuples #-}
module Lib (Store (..), Nest (..), fill) where

#if defined(STATE) || defined(STATESEQ) || defined(STATEIN)
import GHC.IO (IO (..), unIO)
#endif
#if defined(LAZYOUT)
import GHC.Exts (lazy)
#endif

class Store f where
  wr :: f -> Int -> Int -> IO ()

-- An odometer: the innermost level writes n elements, each outer level
-- runs the nest below it cnt times, blk elements apart.
data Nest = Fused | Level !Int !Int Nest

fill :: Store f => f -> Int -> Nest -> IO ()
fill out n nest0 = run nest0 0 0
  where
    level :: (Int -> Int -> IO ()) -> Int -> Int -> Int -> Int -> IO ()
    level body cnt blk !outPos !base =
      let go :: Int -> Int -> Int -> IO ()
#if defined(STATE)
          -- The State# lambda explicit, the bangs outside it.
          go !k !op !b = IO $ \s ->
            if k <= 0 then (# s, () #)
            else case unIO (body op b) s of
                   (# s1, _ #) -> unIO (go (k - 1) (op + blk) (b + 1)) s1
#elif defined(STATESEQ)
          -- The State# lambda explicit, the arguments evaluated inside it.
          go k op b = IO $ \s -> k `seq` op `seq` b `seq`
            if k <= 0 then (# s, () #)
            else case unIO (body op b) s of
                   (# s1, _ #) -> unIO (go (k - 1) (op + blk) (b + 1)) s1
#elif defined(STATEIN)
          -- The State# lambda explicit, op and b evaluated inside its
          -- recursive branch only.
          go k op b = IO $ \s ->
            if k <= 0 then (# s, () #)
            else case op of
              !op' -> case b of
                !b' -> case unIO (body op' b') s of
                  (# s1, _ #) -> unIO (go (k - 1) (op' + blk) (b' + 1)) s1
#else
          go !k !op !b
#if defined(SEQOUT)
            | k <= 0    = outPos `seq` return ()
#elif defined(LAZYOUT)
            | k <= 0    = lazy outPos `seq` return ()
#else
            | k <= 0    = return ()
#endif
            | otherwise = body op b >> go (k - 1) (op + blk) (b + 1)
#endif
      in  go cnt outPos base
    {-# INLINE level #-}
    run :: Nest -> Int -> Int -> IO ()
    run Fused !o !b = level (wr out) n 1 o b
    run (Level cnt blk inner) !o !b = level (run inner) cnt blk o b
#if defined(INL)
{-# INLINE fill #-}
#else
{-# INLINABLE fill #-}
#endif
```

```haskell
module Main (main) where
import Control.Monad (forM_)
import Foreign
import Lib

newtype P = P (Ptr Int)
instance Store P where
  wr (P p) i x = pokeElemOff p i x

main :: IO ()
main =
  allocaArray 64 $ \a -> do
    forM_ [1 .. 100000 :: Int] $ \i -> fill (P a) 8 (Level (i `rem` 8 + 1) 8 Fused)
    xs <- peekArray 64 a
    print (sum xs)
```

`inlinable`, `Main.dump-simpl`: the inner level's loop `$wgo` is a `letrec` closure outside `$wrun`:

```
$s$wfill
  = \ out n nest0 eta ->
      letrec {
        $wgo
          = \ ww ww1 ww2 eta1 ->
```

Bytes in the heap (the run's `+RTS -s` report): `inlinable` 7,252,176, `nofl` 5,652,192, `inline` 3,252,192; `state`, `stateseq` and `seqout` 7,252,176, each with the loop floated as in `inlinable` (`$s$wfill = \ out n nest0 eta -> letrec { $wgo`); `statein` 136,852,176; `lazyout` 12,852,176.

`statein`, `Main.dump-simpl`: the floated loop takes `op` and `b2` boxed and boxes both at every iteration:

```
$s$wfill
  = \ out n nest0 eta ->
      letrec {
        $wgo
          = \ ww op b2 s ->
              case <=# ww 0# of {
                __DEFAULT ->
                  case op of { I# ipv2 ->
                  case b2 of { I# ipv3 ->
```

```
                  $wgo (-# ww 1#) (I# (+# ipv2 1#)) (I# (+# ipv3 1#)) s2
```

`lazyout`, `Main.dump-simpl`: the innermost loop a join point of `$wrun`, and the outer level's loop passing `$wrun` its position boxed:

```
                Fused ->
                  case o of o1 { I# ipv ->
                  case lazy o1 of { I# _ ->
                  case n of { I# ww2 ->
                  joinrec {
                    $wgo ww3 ww4 ww5 eta2
```

```
                            case $wrun inner op1 ww2 eta2 of ww3 { __DEFAULT ->
                            jump $wgo (-# ww1 1#) (I# (+# ipv3 bx1)) (+# ww2 1#) ww3
```

What tells `seqout` from `lazyout` is in `Lib`'s stored template (`Lib.iface`): `seqout`'s base case holds no `seq`, `GHC.Internal.Types.True -> (\ (s['GHC.Internal.Types.Many] :: GHC.Internal.Prim.State# GHC.Internal.Prim.RealWorld) -> (# s, GHC.Internal.Tuple.() #))`, and no `lazy`, where `lazyout`'s keeps `GHC.Internal.Types.True -> case GHC.Internal.Magic.lazy @GHC.Internal.Types.Int o1 of wild2 { GHC.Internal.Types.I# ipv5 ->`. In the importer's first float-out (`Main.dump-float-out`) `seqout`'s `go` leaves `run`, ``$s$wfill = \ out n nest0 eta -> let { body = ($cwr `cast` <Co:12>) out } in letrec { go = \ k op b2 ->``, and `lazyout`'s `lazy o` floats only to `run`'s lambda, ``$s$wfill = \ out n nest0 eta -> let { body = ($cwr `cast` <Co:12>) out } in letrec { run = \ ds o b -> let { lvl = lazy o } in let { lvl = lazy o } in case ds of {`` (whitespace collapsed).

**Reproduces small:** yes, the filed reproducer, with the same figures as filed, its rewritings that are not workarounds included.

### O10. An INLINE body whose callers are all INLINABLE and too big to inline is copied once per caller and type, into their specialisations, not at every call site

**Rule.** An INLINE function is inlined into the stable unfoldings of its callers as they are simplified in their own module (U10), so an INLINABLE caller's unfolding carries the INLINE body. A client calls such a caller at a type: the specialiser copies the caller's unfolding once for that type ([compiler/GHC/Core/Opt/Specialise.hs#L911][g330], `canSpecImport`), the INLINE body with it, and a caller past the size threshold (A04) is then called at each site as that specialisation. So the INLINE body is copied once per caller and type; INLINE on the callers too puts a copy at every call site. The layer can be INLINE throughout at the cost of one copy per specialisation.

**Seen.** `docs/perf-checklist.md` I3, the Read: an INLINE body whose callers are all INLINABLE is copied once per type, into their specialised copies, not at every call site, so such a layer can be INLINE throughout.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/O10-inline-under-inlinable-once-per-type`, variants `inlinable` and `outer-inline` = with `-DOUTER_INLINE`): an INLINE `inner`, its strided loop marked by the literal `7919`, called only by `outerA` and `outerB`, INLINABLE or INLINE; `Main` calls `outerA` at three sites and `outerB` at two at `Double`, and `outerA` at one at `Int`.

```haskell
{-# LANGUAGE BangPatterns, CPP #-}
module Lib (Vec (..), View (..), outerA, outerB, mkView) where

import Data.Array (Array, listArray)
import Data.Array.Base (unsafeAt)

-- A container class, as orthotope's Vector.
class Vec v where
  vat :: v a -> Int -> a

instance Vec (Array Int) where
  vat = unsafeAt

-- A view: length, stride, offset, values.
data View v a = View !Int !Int !Int !(v a)

mkView :: Int -> Int -> [a] -> View (Array Int) a
mkView n s xs = View n s 0 (listArray (0, n * s - 1) xs)

-- The INLINE layer, on four routes; its strided loop is marked by the
-- literal 7919.
{-# INLINE inner #-}
inner :: (Vec v, Num a) => View v a -> a
inner (View n s o v)
  | n == 1 = vat v o
  | s == 0 = fromIntegral n * vat v o
  | s == 1 = let go !acc !i | i >= n = acc
                            | otherwise = go (acc + vat v (o + i)) (i + 1)
             in go 0 0
  | otherwise = let go !acc !i !p | i >= n = acc
                                  | otherwise = go (acc + 7919 * vat v p) (i + 1) (p + s)
                in go 0 0 o

-- Its only callers, INLINABLE (or INLINE, to compare).
#if defined(OUTER_INLINE)
{-# INLINE outerA #-}
{-# INLINE outerB #-}
#else
{-# INLINABLE outerA #-}
{-# INLINABLE outerB #-}
#endif
outerA :: (Vec v, Num a) => View v a -> a
outerA w = inner w + 1

outerB :: (Vec v, Num a) => View v a -> a
outerB w = inner w * 2
```

```haskell
module Main (main) where

import Data.Array (Array)
import Lib

type D = View (Array Int) Double
type I = View (Array Int) Int

-- Six call sites: outerA three times and outerB twice at Double, outerA
-- once at Int.
{-# NOINLINE f1 #-}
f1, f2, f3, f4, f5 :: D -> Double
f1 w = outerA w
{-# NOINLINE f2 #-}
f2 w = outerA w - 1
{-# NOINLINE f3 #-}
f3 w = outerA w * 3
{-# NOINLINE f4 #-}
f4 w = outerB w
{-# NOINLINE f5 #-}
f5 w = outerB w + 5
{-# NOINLINE f6 #-}
f6 :: I -> Int
f6 w = outerA w

main :: IO ()
main = do
  let d = mkView 10 1 [1 .. 10] :: D
      i = mkView 10 1 [1 .. 10] :: I
  print (f1 d, f2 d, f3 d, f4 d, f5 d, f6 i)
```

`Lib.iface`, `inlinable`: `outerA`'s `StableUser` unfolding holds `inner`'s routes, `(case w of wild { View bx bx1 bx2 v1 -> let { n :: GHC.Internal.Types.Int NotJoinPoint [] = GHC.Internal.Types.I# bx } in` and on. `Main.dump-simpl`. `inlinable`: three specialisations, `$w$souterA1` and `$w$souterB` at `Double` and `$w$souterA` at `Int`, and every site calls one, `f1 = $souterA1`, `$wf2 = \ ww ww1 ww2 ww3 -> case $w$souterA1 ww ww1 ww2 ww3 of ww4 { __DEFAULT -> -## ww4 1.0## }`, `$wf3 = \ ww ww1 ww2 ww3 -> case $w$souterA1 ww ww1 ww2 ww3 of ww4 { __DEFAULT -> *## ww4 3.0## }`, `f4 = $souterB`, `$wf5 = \ ww ww1 ww2 ww3 -> case $w$souterB ww ww1 ww2 ww3 of ww4 { __DEFAULT -> +## ww4 5.0## }`, `f6 = $souterA`. `outer-inline`: no `$souter`. Copies of the marked loop, `grep -c` on `Main.dump-simpl`: `7919.0##` 2 under `inlinable` and 5 under `outer-inline`; `7919#` 1 under both.

**Reproduces small:** yes, given callers past the threshold. With `inner` a single loop, the INLINABLE `outerA` and `outerB` were small enough to be inlined at every site, and both variants had the five and one copies.

### O11. A function whose right-hand side is small only once optimised is split by worker/wrapper under INLINABLE, its unfolding the source form, and called out of line where its dictionary comes at run time; under INLINE or without a pragma its body is inlined, as `natT`'s is

**Rule.** A family's cost follows from single-binding rules, summed over its bindings and their call sites: INLINE taken whatever the size (A05) or on a binding with no value argument (A06), a function argument made known (O08), list fusion (O07), one copy per specialisation (O10), and a caller grown past the threshold by an INLINE callee (O04). For `natT` the rule is worker/wrapper's, which leaves a function small enough unsplit with an always-inline unfolding (U07) and splits a larger INLINABLE one, moving its unfolding to the worker (U08). Without a pragma, the size judged is that of the optimised right-hand side, which for `natT`, its error branch floated out, is small enough; an INLINABLE unfolding is the right-hand side as written, which keeps its size, so `natT` is split, the INLINABLE unfolding moving to the worker `$wnatT`. The wrapper, whose unfolding is `ALWAYS_IF(arity=2,unsat_ok=True,boring_ok=False)`, is inlined at each call here, the call stack it is passed counting as a value argument, and calls the worker. Where the call gives the `KnownNat` dictionary of a literal, the client's specialiser rewrites the worker's call to the literal (its rule `SPEC/Main $wnatT @7` below), so nothing is lost; where the dictionary comes at run time, as in a copy specialised on the vector type alone, every call runs `$wnatT`, where INLINE or no pragma gives the body inlined. Two families' costs follow rules of their own, each a single binding's. A copy is never keyed on an implicit-parameter dictionary, `HasCallStack` among them (`interestingDict`, [compiler/GHC/Core/Opt/Specialise.hs#L3086][g390], its `isIPClass` case at [#L3101][g391]; (ID4) in Note [Interesting dictionary arguments], [#L3203][g392]), so the copy takes its call stack as a value parameter (`mk_spec_arg`'s `UnspecArg`, [#L3059][g393]), and an expression in it that pushes onto that stack, such as `listP`'s call in Shaped `transpose`, has the parameter free, which float-out cannot float it past (`lvlMFE`, [compiler/GHC/Core/Opt/SetLevels.hs#L588][g394]; `destLevel`, [#L1584][g395]): it runs at every call, where inlined into a client whose stack is a constant it floats to top level (third repro). And the evidence for an associated constraint family such as `VecElem VS.Vector a`, which reduces to `Storable a`, is, in a wrapper polymorphic in the element, a cast of a lambda-bound dictionary, for which `interestingDict` returns `False` (its `Cast` case, [compiler/GHC/Core/Opt/Specialise.hs#L3096][g396], then the trivial variable's, [#L3117][g397]), so the wrapper's call of an INLINABLE generic function is specialised on the vector type alone. The rule this specialisation makes also fires inside the wrapper's own stable unfolding, where rules stay on (`updModeForStableUnfoldings`, [compiler/GHC/Core/Opt/Simplify/Utils.hs#L1207][g260]; `simplStableUnfolding`, [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4890][g398]), so every client reaches the copy. Under INLINABLE the copy exports only its worker/wrapper wrapper as its unfolding (U12), and a client at a known element runs the element-generic worker; under INLINE the copy keeps the generic function's INLINE unfolding, and the client inlines it with the element known (fourth repro).

**Seen.** Orthotope's benchmark (the comments of the pragma commit, "Give each binding the pragma its kind calls for"): families of INLINEs on orthotope under P's second half, each removed together against the rest, cost bytes a call, the generic modules' functions up to 1160 (`append`), their view operations up to 136 (`broadcast`), `Data.Array.Internal`'s up to 1960 (the conversions), the wrappers' `concatOuter` and `ravel` 16 to 160, `natT` 16 at Shaped `iota`, and the `convertE` methods 16 to 40 at a consumed conversion. The benchmark's `Ops*.dump-simpl` of a build with INLINE removed widely and `natT` made INLINABLE hold 17 occurrences of `Data.Array.Internal.Shape.$wnatT` and 10 of `natT`, where B0's, `natT` INLINE, hold none of `$wnatT`; X4 (whose `natT` is INLINABLE) costs only at Shaped `iota`, 16 bytes a call; and the Core of N0EU against N0ERU, two builds of the first pragma pass, of 2026-10-13, keeping and releasing its small-array pragma exceptions, gives each family's mechanism: boxed views normalised through copies of `toVectorT` generic in the element, a Storable `vUnsafeFillStrided` building an `irred` dictionary every call, Shaped `append` specialised as `$sappend @'[500] @400 @400 @Double` running `$wnatT @m`, `$wnatT @n` and `sizeP` every call, and Shaped `transpose` rebuilding its permutation by `$w$slistP` every call. The boxed copies' fill stays unspecialised by design: in N0ERU's `$s$wtoVectorT3`, fixed to the boxed vector and general in the element, `$wgenericUnsafeFillStrided` is called at `$fVectorVectora @a`, a call that appears only after the specialiser, when the simplifier inlines the boxed instance's INLINE method `vUnsafeFillStrided = genericUnsafeFillStrided 5`; the specialiser leaves the method alone, its one dictionary, `None a` (`type VecElem V.Vector = None`), being of a class without methods ((ID6) of Note [Interesting dictionary arguments]). And the polymorphic specialisation that the instance's module made has no rule in its interface: its wrapper was inlined into its one caller, which left the rule the only reference to it, and Tidy dropped the rule (the specialisation appendix, "Auto rules and their copies are dropped unless kept"). In a model, `-fkeep-auto-rules` on the instance's module, or `toVectorT` INLINE, gives the client the specialised fill.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/O11-inline-family-natT`, variants `inline`, by `-DINL`, `none` and `inlinable`, by `-DINLB`, the last two with `-dinline-check natT`; `run` is `1000000`; `measure.sh N`): orthotope's `natT`, a function of a `HasCallStack` and a `KnownNat` dictionary and no value argument, INLINE, without a pragma, or INLINABLE as at X4, used in the shape a Shaped `iota` builds at size 7 (`mk`), and in `iotaT`'s shape, a shape and the values it counts, called by `mkP`, kept polymorphic by OPAQUE so that its dictionary comes at run time, as in `$sappend`; a second argument to `Main` times `mkP`.

```haskell
{-# LANGUAGE BangPatterns, CPP, DataKinds, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes #-}
-- Everything exported, as orthotope's modules export their functions.
module Lib (module Lib) where

import Data.Proxy (Proxy (..))
import GHC.Stack (HasCallStack)
import GHC.TypeLits (KnownNat, natVal)

-- Orthotope's natT: a type-level number as an Int; fails past maxBound.
#if defined(INL)
{-# INLINE natT #-}
#elif defined(INLB)
{-# INLINABLE natT #-}
#endif
natT :: forall n . (HasCallStack, KnownNat n) => Int
natT | n > toInteger (maxBound :: Int) =
         error $ "Shape: a number past maxBound: " ++ show n
     | otherwise = fromInteger n
  where n = natVal (Proxy :: Proxy n)

-- A shaped array's shape, as Shaped iota makes it: the extent in a list.
data Arr = Arr ![Int]

{-# INLINE iotaShape #-}
iotaShape :: forall n . KnownNat n => Arr
iotaShape = Arr [natT @n]

-- A shaped array's shape and values, as Shaped iota makes them through
-- iotaT n = fromVectorT [n] (vGenerate' n fromIntegral).
data V = V ![Int] ![Double]

{-# INLINE iotaT #-}
iotaT :: Int -> Double -> V
iotaT n d = V [n] (go 0)
  where go i | i >= n = []
             | otherwise = let !x = fromIntegral i + d in x : go (i + 1)

{-# INLINE iotaV #-}
iotaV :: forall n . KnownNat n => Double -> V
iotaV d = iotaT (natT @n) d

-- A client of iotaV with the type's dictionary passed at run time, as in
-- a specialisation keyed on the vector type alone, and a loop timing it.
{-# OPAQUE mkP #-}
mkP :: forall n . KnownNat n => Int -> V
mkP r = iotaV @n (fromIntegral r)

runP :: Int -> Double
runP = go 0
  where go !acc 0 = acc
        go !acc r = case mkP @7 r of
          V (n : _) (x : _) -> go (acc + fromIntegral n + x) (r - 1)
          _ -> acc
```

```haskell
{-# LANGUAGE BangPatterns, DataKinds, TypeApplications #-}
module Main (main) where

import Lib
import System.Environment (getArgs)

-- Opaque, so that each iteration builds anew.
{-# OPAQUE pass #-}
pass :: Int -> a -> a
pass _ x = x

{-# NOINLINE mk #-}
mk :: Int -> Arr
mk r = pass r (iotaShape @7)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [repss] -> do
      let reps = read repss :: Int
          loop :: Int -> Int -> Int
          loop 0 !acc = acc
          loop r !acc = case mk r of Arr (x : _) -> loop (r - 1) (acc + x); _ -> acc
      print (loop reps 0)
    -- A second argument times iota with the dictionary passed at run time.
    repss : _ -> print (runP (read repss))
    [] -> pure ()
```

`none`, `build.log`: both decisions are `Lib`'s own, made before `Main` is compiled, `natT` refused at its size as written and taken at a smaller guidance once its error message has floated out; `Main` makes none, `natT`'s body reaching it inside `iotaShape`'s unfolding:

```
Considering inlining: natT
  arg infos [ValueArg, TrivArg]
  interesting continuation BoringCtxt
  some_benefit True
  is exp: True
  is work-free: True
  guidance IF_ARGS [30 30] 680 0
  case depth = 0
  inline depth = 1
  depth based penalty = 0
  adjusted size = 620
  ANSWER = NO
...
Considering inlining: natT
  arg infos [ValueArg, TrivArg]
  interesting continuation BoringCtxt
  some_benefit True
  is exp: True
  is work-free: True
  guidance IF_ARGS [0 30] 110 10
  case depth = 0
  inline depth = 1
  depth based penalty = 0
  adjusted size = 80
  ANSWER = YES
```

At the known size all three variants' `Main.dump-simpl` make the shape a static constant, `lvl = I# 7#`, `lvl1 = : lvl []`, `lvl2 = Arr lvl1`, and all three allocate 56,336 bytes in all (the run's `+RTS -s` report); under `inlinable` through the client's specialisation of the worker:

```
"SPEC/Main $wnatT @7" [2]
    forall $dIP $dKnownNat1. $wnatT $dIP $dKnownNat1 = 7#
```

`inlinable`, `build.log`: `natT`'s INLINABLE unfolding refused at its source size, `guidance IF_ARGS [30 30] 590 10` with `adjusted size = 530` and `ANSWER = NO`, and its wrapper taken, `guidance ALWAYS_IF(arity=2,unsat_ok=True,boring_ok=False)`, `ANSWER = YES`. `Lib.dump-simpl` holds the worker under `inlinable` alone (`none` and `inline` have no `$wnatT`):

```
$wnatT
  = \ @n2 $dIP $dKnownNat1 ->
      case integerFromNatural ((natSing $dKnownNat1) `cast` <Co:2>)
      of x1 {
        __DEFAULT -> integerToInt# x1;
```

and `mkP` calls it, `inlinable`:

```
mkP
  = \ @n2 $dKnownNat1 r ->
      case $wnatT (C:IP n1) $dKnownNat1 of ww { __DEFAULT ->
```

where `inline` (and `none`, but for the type variable's name) has the body:

```
mkP
  = \ @n $dKnownNat1 r ->
      case integerFromNatural ((natSing $dKnownNat1) `cast` <Co:2>)
      of x1 {
```

By `measure.sh 1000000` (1000000 and 2000000 calls of `mkP` differenced), run twice with the same figures: `inline` and `none` 214.3 instructions a call, `inlinable` 231.3, all three 232.0 bytes.

A second repro (`~/r/horde-ad/dist-inlcat/cases/O11-natT-orthotope`, variants `x4` and `c1`, `Main` compiled against orthotope as built at X4 (`natT` INLINABLE) and at build C1 (`natT` INLINE), and `c1nocse`, `c1` with `-fno-cse`; `run` is `7 1`; `measure.sh N`): the benchmark's Shaped `iota` row at the Storable family, the size given at run time.

```haskell
{-# LANGUAGE BangPatterns, DataKinds, ScopedTypeVariables #-}
-- The specialisation benchmark's Shaped iota row (bench/shaped-ops.inc at
-- X4), at the Storable family, compiled against an installed
-- orthotope: X4 (natT INLINABLE) or C1 (natT INLINE).
module Main (main) where

import Data.Proxy (Proxy)
import GHC.TypeLits (SomeNat (..), someNatVal)
import qualified Data.Array.ShapedS as ARR
import qualified Data.Vector.Storable as VS
import System.Environment (getArgs)

-- Opaque, so that each iteration builds anew.
{-# OPAQUE pass #-}
pass :: Int -> a -> a
pass _ x = x

{-# NOINLINE iota #-}
iota :: Int -> VS.Vector Double
iota k = case someNatVal (toInteger k) of
    Just (SomeNat p) -> ARR.toVector (ARR.iota `sizedBy` p)
    Nothing -> error "iota: negative size"
  where
    sizedBy :: ARR.Array '[m] Double -> Proxy m -> ARR.Array '[m] Double
    sizedBy a _ = a

main :: IO ()
main = do
  [ks, repss] <- getArgs
  let k = read ks :: Int
      reps = read repss :: Int
      loop :: Int -> Double -> Double
      loop 0 !acc = acc
      loop r !acc = loop (r - 1) (acc + VS.last (iota (pass r k)))
  print (loop reps 0)
```

Shaped `iota` builds its shape twice, by `natT @n` for `iotaT` and by `valueOf @n` in the Shape instance's INLINE `shapeP` (orthotope's `Data/Array/Internal/Shape.hs` at X4), both unfoldings applying `integerToInt#` to `integerFromNatural` of `natSing`. With `natT` INLINE the two are one case scrutinee, and CSE merges them (`cseCase`, [compiler/GHC/Core/Opt/CSE.hs#L724][g399]; Note [CSE for case expressions], [#L144][g400]): `c1`'s `Main.dump-stg-final` has one `case integerFromNatural $dKnownNat of x1 {` and no `$wnatT`, its `I#` reused. With `natT` INLINABLE, `$wnatT` computes its own copy out of line, `__DEFAULT -> $wnatT n6 $dKnownNat;`, and the client calls `integerFromNatural $dKnownNat` again. By `measure.sh 100000`: `x4` 464.0 bytes a call, `c1` 448.0, `c1nocse` 464.0, the 16 bytes being the second call's `IS` Integer.

A third repro (`~/r/horde-ad/dist-inlcat/cases/O11-listP-per-call`, variants `inline` and `inlinable` by `transpose`'s pragma, `inline` by `-DINL`; `run` is `1000000`; `measure.sh N`): orthotope's `Shape` class, `listP` and a `transpose` of a list by a type-level permutation, called by a client at `'[2, 0, 1]` in a loop; orthotope's `transpose` is `(HasCallStack, Permutation is, ..., Shape is, ...) =>` and binds `is = listP (Proxy :: Proxy is)`, `listP` being INLINABLE with `HasCallStack`.

```haskell
{-# LANGUAGE CPP, DataKinds, KindSignatures, PolyKinds, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes, FlexibleInstances, FlexibleContexts #-}
-- Orthotope's Shape class, listP and Shaped transpose, cut down.
module Lib (module Lib) where

import Data.Proxy (Proxy (..))
import GHC.Stack (HasCallStack)
import GHC.TypeLits (KnownNat, Nat, natVal)

class Shape (s :: [Nat]) where
  natsP :: Proxy s -> [Integer]

instance Shape '[] where
  {-# INLINE natsP #-}
  natsP _ = []

instance (Shape s, KnownNat n) => Shape (n ': s) where
  {-# INLINE natsP #-}
  natsP = const ns
    where ns = natVal (Proxy :: Proxy n) : natsP (Proxy :: Proxy s)

-- A type-level list's numbers as Ints, each checked.
{-# INLINABLE listP #-}
listP :: (HasCallStack, Shape s) => Proxy s -> [Int]
listP p = map toInt (natsP p)
  where toInt n | n > toInteger (maxBound :: Int) =
                    error $ "Shape: a number past maxBound in " ++ show (natsP p)
                | otherwise = fromInteger n

-- Permute a list by a type-level permutation, INLINE (orthotope's) or
-- INLINABLE (its family removed).
#ifdef INL
{-# INLINE transpose #-}
#else
{-# INLINABLE transpose #-}
#endif
transpose :: forall is a . (HasCallStack, Shape is) => [a] -> [a]
transpose xs = [ xs !! i | i <- is ]
  where is = listP (Proxy :: Proxy is)
```

```haskell
{-# LANGUAGE BangPatterns, DataKinds, TypeApplications #-}
module Main (main) where

import System.Environment (getArgs)
import Lib

-- Opaque, so that each iteration transposes anew.
{-# OPAQUE pass #-}
pass :: Int -> a -> a
pass _ x = x

main :: IO ()
main = do
  [ns] <- getArgs
  let reps = read ns :: Int
      xs = [10, 20, 30] :: [Int]
      loop :: Int -> Int -> Int
      loop 0 !acc = acc
      loop r !acc = case transpose @'[2, 0, 1] (pass r xs) of
        y : _ -> loop (r - 1) (acc + y)
        [] -> acc
  print (loop reps 0)
```

`Main.dump-simpl`, INLINE: the permutation is a top-level constant, `lvl7 = $w$slistP (C:IP lvl6)`, `lvl6` the client's call stack pushed with `listP`'s location. INLINABLE: the copy `$stranspose = \ @a $dIP4 eta -> ...` ends in `go1 ($w$slistP (C:IP (case ip $dIP4 of wild1 { __DEFAULT -> PushCallStack $stranspose2 $stranspose1 wild1; ...` and no top-level binding calls `$w$slistP`. By `measure.sh 1000000`, twice alike: INLINE 204.1 instructions and 144.0 bytes a call, INLINABLE 343.8 instructions and 352.0 bytes.

A fourth repro (`~/r/horde-ad/dist-inlcat/cases/O11-element-generic-copy`, variants `inline`, both INLINE, by `-DGEN_INL -DWRAP_INL`, `geninlinable`, the generic `revT` INLINABLE and the wrapper INLINE, by `-DWRAP_INL`, and `inlinable`, both INLINABLE; `run` is `100000`; `measure.sh N`): orthotope's `Vector` class cut to three methods with its associated constraint, `type VecElem v :: Type -> Constraint` as orthotope's has it, a generic reversal `revT` and a Storable wrapper `rev = revT`, reversing 1000 Doubles in a loop.

```haskell
{-# LANGUAGE CPP, TypeFamilies, ConstraintKinds, FlexibleContexts #-}
-- Orthotope's Vector class with its associated element constraint, a generic
-- function and a Storable wrapper, cut down.
module Lib (module Lib) where

import Data.Kind (Constraint, Type)
import qualified Data.Vector.Storable as VS

class Vector v where
  type VecElem v :: Type -> Constraint
  vGenerate :: VecElem v a => Int -> (Int -> a) -> v a
  vIndex :: VecElem v a => v a -> Int -> a
  vLength :: VecElem v a => v a -> Int

instance Vector VS.Vector where
  type VecElem VS.Vector = VS.Storable
  {-# INLINE vGenerate #-}
  vGenerate = VS.generate
  {-# INLINE vIndex #-}
  vIndex = VS.unsafeIndex
  {-# INLINE vLength #-}
  vLength = VS.length

-- The generic module's function, INLINE (orthotope's) or INLINABLE.
#ifdef GEN_INL
{-# INLINE revT #-}
#else
{-# INLINABLE revT #-}
#endif
revT :: (Vector v, VecElem v a) => v a -> v a
revT v
  | n < 2 = v
  | n < 8 = vGenerate n (\ i -> vIndex v (n - 1 - i))
  | even n = vGenerate n (\ i -> if even i then vIndex v (n - 1 - i)
                                  else vIndex v (n - 1 - i))
  | otherwise = vGenerate n (\ i -> if i == 0 then vIndex v (n - 1)
                                     else vIndex v (n - 1 - i))
  where n = vLength v

-- The Storable wrapper, INLINE (orthotope's thin wrappers) or INLINABLE.
#ifdef WRAP_INL
{-# INLINE rev #-}
#else
{-# INLINABLE rev #-}
#endif
rev :: VS.Storable a => VS.Vector a -> VS.Vector a
rev = revT
```

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import qualified Data.Vector.Storable as VS
import System.Environment (getArgs)
import Lib

-- Opaque, so that each iteration reverses anew.
{-# OPAQUE pass #-}
pass :: Int -> a -> a
pass _ x = x

main :: IO ()
main = do
  [ns] <- getArgs
  let reps = read ns :: Int
      v = VS.generate 1000 fromIntegral :: VS.Vector Double
      loop :: Int -> Double -> Double
      loop 0 !acc = acc
      loop r !acc = loop (r - 1) (acc + VS.head (pass r (rev (pass r v))))
  print (loop reps 0)
```

`Lib.iface`: `rev`'s unfolding is ``rev_$srevT `cast` ...`` in every variant (`StableUser <1,FalseTrue>` with the wrapper INLINE, `<0,TrueTrue>` with it INLINABLE); the copy's is `Inline: (sat-args=1), Unfolding: Core: StableUser <2,FalseFalse>`, `revT`'s body, under INLINE `revT`, and under INLINABLE its worker/wrapper wrapper, `case $w$srevT @a irred ww ww1 ww2 of wild1 ...`. `Lib.dump-simpl`, in every variant: `"SPEC revT @Vector @_" forall @a $dVector. revT $dVector = rev_$srevT`, and under INLINABLE `revT` its worker `$w$srevT = \ @a irred ww ww1 ww2 -> ...`. `Main.dump-simpl` of `geninlinable` and of `inlinable`: ``case $w$srevT ($fStorableDouble `cast` <Co:4>) ww2 ww3 ww4 of``; of `inline`: no call of a copy. By `measure.sh 20000`: `inline` 10543.2 instructions and 8080.0 bytes a call, `geninlinable` and `inlinable` 198561.4 instructions and 128080.0 bytes.

**Reproduces small:** in part: `natT`'s half, yes: made INLINABLE it is split and called as `$wnatT` where its dictionary comes at run time, 17 instructions a call more, no byte. The 16 bytes orthotope measured at Shaped `iota`, yes, by the second repro, a client of the libraries built at X4 and at build C1 (`natT` INLINE), not by the first, where at a known size the client's specialisation of the worker leaves the shape a constant. `listP`'s permutation rebuilt every call, yes (third repro). Copies generic in the element, yes, the copy keyed on the vector type and the client sent to it (fourth repro); the `irred` dictionary built every call, no, the one there being a cast of `$fStorableDouble` that allocates nothing; the boxed views, not tried.

### O12. A sum returned in different constructors by a function called out of line is built on the heap, where a product is returned unboxed; only inlining lets the caller take it apart unbuilt

**Rule.** Worker/wrapper returns a result unboxed only when its CPR signature names one constructor (`canUnboxResult`, [compiler/GHC/Core/Opt/WorkWrap/Utils.hs#L642][g401], its first guard `asConCpr cpr`). CPR analysis joins the results of a function's branches with `lubCpr`, which gives `TopCpr`, no constructor, as soon as two branches return different constructors ([compiler/GHC/Types/Cpr.hs#L55][g402], the last equation at [#L64][g403]). So a function returning a product, one constructor, gets `CPR: 1` and a worker returning an unboxed tuple, the wrapper rebuilding the product where it is inlined and case-of-known-constructor removing it at a caller that takes it apart; a function returning a sum whose branches return different constructors gets no CPR, and its worker returns the constructor boxed, allocated at every out-of-line call whatever the caller does with it. Inlined, the function puts each constructor application into the caller's `case`, and case-of-known-constructor takes it apart unbuilt (A21's mechanism, through the inlined body).

**Seen.** `docs/perf-checklist.md` A3: with orthotope's `unorderedRouteT` and `cellsRouteT` out of line, their workers returned a boxed `Route` at 18 and 45 client call sites (2026-10-11); with `readRangeT`, `sameRangeT` and `range3T` out of line, a boxed `Range` at 262 call sites (2026-10-12); and A3's statement that "GHC HEAD 10.1.20260918 returns no sum unboxed ... where worker/wrapper passes and returns a product unboxed". A3's other observation, a value built once in one binding and taken apart at several places through a join point whatever the pragmas (orthotope's `equalT`), is O16's.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/O12-sum-returned-built`, variants `noinline` and `inline`, `inline` adding `-DINL`; `post` runs each variant's Main at 1000000 and 2000000 iterations and writes the bytes a call, differenced, to `~/r/horde-ad/dist-inlcat/cases/O12-sum-returned-built/out/head/VARIANT/bytes.txt`): a three-constructor sum and a product, each returned by a function NOINLINE or INLINE and taken apart by a loop in `Main`.

```haskell
{-# LANGUAGE CPP #-}
module Lib (Route (..), Axes (..), routeOf, axesOf) where

-- A sum: which walk a view takes, built here and taken apart by callers.
data Route = Dense !Int | Strided !Int !Int | Runs !Int !Int !Int

-- A product of the same kind.
data Axes = Axes !Int !Int

#if defined(INL)
{-# INLINE routeOf #-}
{-# INLINE axesOf #-}
#else
{-# NOINLINE routeOf #-}
{-# NOINLINE axesOf #-}
#endif
routeOf :: Int -> Int -> Int -> Route
routeOf n s k
  | s == 1 = Dense (n * k)
  | k == 1 = Strided n s
  | otherwise = Runs n s k

axesOf :: Int -> Int -> Axes
axesOf n s
  | s == 1 = Axes n 1
  | otherwise = Axes (n * s) s
```

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import Lib
import System.Environment (getArgs)

-- Opaque, so that each iteration calls anew.
{-# OPAQUE pass #-}
pass :: Int -> Int -> Int
pass _ x = x

main :: IO ()
main = do
  [mode, ns] <- getArgs
  let n = read ns :: Int
      loopR, loopA :: Int -> Int -> Int
      loopR 0 !acc = acc
      loopR r !acc = let k = pass r r in
        case routeOf (k `rem` 7) (k `rem` 3) (k `rem` 5) of
          Dense a -> loopR (r - 1) (acc + a)
          Strided a b -> loopR (r - 1) (acc + a * b)
          Runs a b c -> loopR (r - 1) (acc + a + b + c)
      loopA 0 !acc = acc
      loopA r !acc = let k = pass r r in
        case axesOf (k `rem` 7) (k `rem` 3) of
          Axes a b -> loopA (r - 1) (acc + a * b)
  print (if mode == "route" then loopR n 0 else loopA n 0)
```

`noinline`, the interface: `axesOf` has `Strictness: <1!P(L)><1!P(1L)>, CPR: 1, Inline: [final],` and `routeOf` `Strictness: <1!P(L)><1!P(1L)><1!P(L)>, Inline: [final],`, no CPR. `Lib.dump-simpl`, whitespace collapsed: the product's worker returns an unboxed pair, the sum's worker the boxed constructors:

```
$waxesOf = \ ww ww1 -> case ww1 of wild { __DEFAULT -> (# *# ww wild, wild #); 1# -> (# ww, 1# #) }
__DEFAULT -> Runs ww wild wild1; 1# -> Strided ww wild }; 1# -> Dense (*# ww ww2)
```

`inline`: `Main.dump-simpl` has no `Dense` and no `Runs` (`noinline`'s has both, in the loop's `case`). Bytes a call (from that file), 16 of them in every variant being the loop's own boxed counter passed to `pass`:

```
noinline   route: 41 bytes a call   axes: 16 bytes a call
inline     route: 16 bytes a call   axes: 16 bytes a call
```

The 25 bytes a call more at `noinline` `route` are the `Route` built: 16, 24 or 32 bytes by constructor, 25.6 on average over the residues the loop takes, `post` truncating to whole bytes.

**Reproduces small:** yes, the sum built out of line and the product not.

### O13. A check written into an INLINE body is computed at every call once its loops fuse into the caller, and once as a floated constant where they stay a call (orthotope's `isPermutation`)

**Rule.** A closed expression inside a function, such as a check of a literal argument, is floated to top level by full laziness and evaluated once. An INLINE body's check, inlined into a caller whose argument is a literal, is closed there only while it stays an expression: where base's `all` and `elem` are inlined into it, the check fuses with its enumeration into join-point loops, and case-of-case puts the rest of the call, the code after the guard, into a join point `$j` that the loops jump to on success; the loops then mention that per-call join point and are not closed: SetLevels floats no expression that mentions a join point (`lvlMFE`'s `hasFreeJoin` test, [compiler/GHC/Core/Opt/SetLevels.hs#L620][g404], Note [Free join points] at [#L943][g405]) and a join point only to top level (Note [Floating join point bindings], [compiler/GHC/Core/Opt/SetLevels.hs#L871][g406], decided by `wantToFloat` at its uses, [#L1267][g407] and [#L1313][g408]), so the check runs in every call. Where `all` is not inlined, as in a module built `-funfolding-creation-threshold=30`, which, importing base, recomputes base's guidance against that threshold (U06), the check stays a call `all1 $fFoldableList ...` on closed arguments, floated out and evaluated once. Written as a separate function, the check is a call however its body is compiled: here, a pragma-free one becomes its cast worker `isPerm1` by cast worker/wrapper (U17), which the INLINE body's stable unfolding calls (U10), and the client floats `isPerm1` of the literal out as a constant, with or without NOINLINE, which is orthotope's remedy.

**Seen.** Orthotope's commit "Check transpose's permutation out of line": Dynamic's and Ranked's `transpose` "checked that their argument is a permutation by a test written into their bodies, so the test was compiled into each caller with them, and whether a literal permutation was checked once or on every call depended on how the library was built: once at -funfolding-creation-threshold=30, on every call at the default thresholds with Dynamic's transpose INLINE"; with the test the NOINLINE `isPermutation`, Ranked `transpose` allocated 40 bytes a call less at the small and empty sizes with its result forced. The same, as `isPermutation`'s `NOINLINE:` comment in `Data/Array/Internal.hs` (checkout at "Condense the account of unorderedRouteT's sort and merge"). And an empty array allocated at every call: orthotope's Dynamic Storable `concatOuter` at the empty size, the row `concatOuter [a, b]` over two empty arrays, in C8's row worker `$wlvl624` (`OpsDynamic.dump-simpl`) builds each input's empty vector as `runRW# ... (\ (s1 :: State# RealWorld) -> case newAlignedPinnedByteArray# @RealWorld 0# 8# s1 of { (# _, ipv10 #) -> jump $j33 0# (mutableByteArrayContents# @RealWorld ipv10) (PlainPtr ipv10) })` (qualifiers dropped, whitespace collapsed), jumping to a join point of the loop over the inputs. The jump is inside the `runRW#` by the simplifier's `runRW#` rule, the one step that moves a continuation into `runRW#`'s lambda (`simplOutId`, [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L2389][g409]): in a model (`~/r/horde-ad/dist-inlcat/cases/O13-runrw-rule-jump`) the branch is `1# -> jump $j (runRW# (\ s -> join {` up to worker/wrapper, which gives `$j` the wrapper `$j arg = case arg of wild { Vector ww ww ww -> jump $w$j ww ww ww }`, and after the next Simplifier, the wrapper inlined at the jump, `1# -> runRW# (\ s -> join { $w$j unbx = case <# unbx 0# of {`, the jump inside. In R4 (the thin wrappers INLINABLE) the row worker `$wlvl338` scrutinises at the same branch the top-level `$s$fVectorVector_$cvConcat3`, `0# -> case OpsDynamic.$s$fVectorVector_$cvConcat3 of { Data.Vector.Storable.Vector ipv2 ipv3 ipv10 -> jump $j18 ipv2 ipv3 ipv10 };`, the empty vector built once. C8's module binds the same constant. Of the dumped trees only R4 makes DynamicG's `toVector` INLINABLE, as it does `shapeL` and the Storable `vUnsafeConcatN`, and the change that matters is `toVector`'s: in a model of the path over arrays with a shape list (`~/r/horde-ad/dist-inlcat/cases/O13-concat-shapes`) `toVector` INLINABLE alone gives R4's form, `0# -> case lvl34 of { Vector ipv7 ipv8 ipv9 -> jump $j2 ipv7 ipv8 ipv9`, and `shapeL` or `vUnsafeConcatN` INLINABLE alone leaves C8's copy (without the shape list, `~/r/horde-ad/dist-inlcat/cases/O13-concat-toggles`, every combination leaves it). Under INLINE, `toVector`'s unfolding, `StableUser <2,FalseFalse>`, is refused at `map`'s call `toVector $fVecVector`, given its dictionary alone (`guidance ALWAYS_IF(arity=2,unsat_ok=False,boring_ok=False)`, `ANSWER = NO`; E01); under INLINABLE it is `StableSystem <2,TrueFalse>` (U07) and inlined at that call in the gentle run (`unsat_ok=True`, `ANSWER = YES`; A02), so `toVectorT`'s `vConcat []` sits in a lambda at the first float-out, which levels it to top level. Orthotope's interfaces split the same way, R4's `DynamicG.hi` giving `toVector` `StableSystem <3,TrueFalse>` and C8's `StableUser <3,FalseFalse>`. The model allocates 64 bytes a call fewer with `toVector` INLINABLE, 72,853,640 bytes at 100000 calls against 79,252,616. LRV (U15's LN with more methods of the boxed and Unboxed instances banged and the Storable `vSingleton` written as one write into a new vector), within 2% of C8's form there, runs 2257 instructions a call forced against R4's 2073 and allocates three pinned arrays a call to R4's one.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/O13-literal-check-inlined`, variants `body`, the check written into `transposeL` by `-DBODY`, and `body30`, the same at `-funfolding-creation-threshold=30`; and with the check the function `isPerm`: `default`, `noinline` with `-DNOINL` on `isPerm`, and `t30` at threshold 30; `run` is `1000`): orthotope's check in an INLINE cut-down transpose that a loop in `Main` applies to a literal permutation.

```haskell
{-# LANGUAGE CPP #-}
module Lib (isPerm, transposeL) where

-- Whether the list holds each of 0 to its length less 1 (orthotope's
-- isPermutation).
#if defined(NOINL)
{-# NOINLINE isPerm #-}
#endif
isPerm :: [Int] -> Bool
isPerm is = all (`elem` is) [0 .. length is - 1]

-- A transpose that checks its permutation first (orthotope's generic
-- transpose, cut down).
{-# INLINE transposeL #-}
transposeL :: [Int] -> [Int] -> [Int]
transposeL is sh
#if defined(BODY)
  | not (all (`elem` is) [0 .. length is - 1]) =
#else
  | not (isPerm is) =
#endif
      error ("transposeL: not a permutation: " ++ show is)
  | otherwise = map (sh !!) is
```

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import Lib
import System.Environment (getArgs)

-- Opaque, so that each iteration transposes anew.
{-# OPAQUE pass #-}
pass :: Int -> a -> a
pass _ x = x

main :: IO ()
main = do
  [ns] <- getArgs
  let n = read ns :: Int
      sh = [2, 3, 4, 5]
      loop :: Int -> Int -> Int
      loop 0 !acc = acc
      loop r !acc = case transposeL [3, 1, 0, 2] (pass r sh) of
        (a : _) -> loop (r - 1) (acc + a)
        [] -> acc
  print (loop n 0)
```

`body`, `Main.dump-simpl`: inside `$wloop`, whitespace collapsed, the check's loops, whose success jumps to `$j`, the rest of the iteration, and no `all1`:

```
joinrec { go2 x1 = join { $j1 = case ==# x1 y of { __DEFAULT -> jump go2 (+# x1 1#); 1# -> jump $j } } in
jump go2 0#; 1# -> jump $j
```

`body30`: the check a top-level constant that the loop scrutinises:

```
lvl7 = all1 $fFoldableList lvl6
lvl9 = lvl7 lvl8
case lvl9 `cast` <Co:1> of { False -> case lvl5 of {}; True ->
```

With the check the function `isPerm`, `transposeL`'s interface unfolding (`default`) begins ``case (isPerm1 is) `cast` GHC.Internal.Data.Semigroup.Internal.N:All of wild {``, and all three of `default`, `noinline` and `t30` bind the check once at top level, `lvl6 = isPerm1 is5`.

**Reproduces small:** yes, the check computed at every call at the default thresholds and once at 30; and that a separate function, NOINLINE or not, makes it a constant.

### O14. An INLINE method that unfolds two or more calls of its class's methods at the next rank of a type-level list costs simplifier ticks growing exponentially with the rank, against a limit fixed by the program's size

**Rule.** The simplifier's tick limit is set afresh for each of its iterations, from the program as it stands at the iteration's start: `(size + 100) * 40 * f / 100` ticks, where `size` is `coreBindsSize` of the bindings and `f` is `-fsimpl-tick-factor`, 100 by default (`computeMaxTicks`, [compiler/GHC/Core/Opt/Simplify/Monad.hs#L112][g410]; `initSmpl`, [#L95][g411], starting the count at 0; `do_iteration`, [compiler/GHC/Core/Opt/Simplify.hs#L250][g412], computing `sz = coreBindsSize binds` before calling `initSmpl` with it). Every tick the simplifier takes is counted (`tick`, [Monad.hs#L232][g413]), but the count is checked against the limit only when an unfolding is inlined (`checkedTick (UnfoldingDone fun)` in `simplOutId`, [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L2456][g414]) or a rule fires (`checkedTick (RuleFired ...)` in `tryRules`, [#L2807][g415]), and `checkedTick` ([Monad.hs#L240][g416]) throws "Simplifier ticks exhausted" once the count reaches the limit, naming the inlining or rule it was about to take. So the limit grows with the module but not with what the module unfolds into: a few class methods that inline one another at each rank of a type-level shape copy their bodies a number of times growing exponentially with the rank within one iteration, though the copies fold to a constant in the end, and a small module with a deep enough shape exhausts the limit. Here `sizeP` at a rank unfolds `sizeP` at the next rank and, in its error message, `shapeP` at the next rank, while the INLINE `shapeP` unfolds `sizeP` at its own rank through its `seq`; under INLINE on both, the ticks grow by a factor of about 3.3 a rank. With `shapeP` out of the error message they still double a rank while the client also calls `shapeP` (the stored unfolding of `shapeP` holds two calls of `shapeP` at the next rank, one on each non-bottoming path of the inlined `sizeP`'s guard, `m == 0` and the quotient test, from the phase-2 run on, the first with case-of-case, the step that copies the continuation into both not identified; with one such path, `shapeP` is unfolded once a rank); with the client's `shapeP` gone too they grow linearly, 141 ticks a rank. NOINLINE on `sizeP` leaves it a call: 100 ticks at rank 4.

**Seen.** Orthotope's `sizeP` in `instance (Shape s, KnownNat n) => Shape (n ': s)` (`Data/Array/Internal/Shape.hs` at "Give each binding the pragma its kind calls for" on `pragma-run`), NOINLINE since "Reject shapes whose size overflows Int", its comment given its present form by "Mark the list instance pragma-free and give Shape's pragmas reasons": made INLINE in a copy of the checkout built with GHC HEAD 10.1.20260918, the test suite's ShapedTest ran out of simplifier ticks "When trying RuleFired unpack" and ShapedGTest "When trying RuleFired Class op natSing", "Total ticks: 320683".

**Repro** (`~/r/horde-ad/dist-inlcat/cases/O14-sizep-simplifier-ticks`, variants `noinline4`, `inline2`, `inline3`, `inline4`, `inline4big`, `inline5big`, `noshape4`, `noshape5`, `noshape6`, `onlysize5` and `onlysize6`, the digit being the rank, set by `-DRANK=`, `inline` making `sizeP` INLINE, by `-DINL`, `big` raising `-fsimpl-tick-factor` to 1000, `noshape` dropping `shapeP` from the error message, by `-DNOSHAPE`, and `onlysize` the client's call of `shapeP` too, by `-DONLYSIZE`; `onepath4`, `onepath5` and `onepath6`, `noshape` with one non-bottoming path through `sizeP`'s guard, by `-DONEPATH`; `v2c2`, `noshape` at rank 2 with `-dverbose-core2core`; `inline4` and `noshape6` fail to compile by design, so `bin/run-case` exits 1): orthotope's `Shape` class and its two instances, without the `Typeable` superclass and `natsP`, and a client taking the size and the shape of a shape `[2, 3, 4, ...]` of the given rank.

```haskell
{-# LANGUAGE CPP, DataKinds, KindSignatures, ScopedTypeVariables, TypeApplications, TypeOperators, AllowAmbiguousTypes, UndecidableInstances #-}
module Shape (Shape (..)) where

import Data.Proxy
import GHC.TypeLits

-- orthotope's Shape at "Give each binding the pragma its kind calls for", its
-- Typeable superclass and natsP dropped.
class Shape (s :: [Nat]) where
  shapeP :: Proxy s -> [Int]
  sizeP  :: Proxy s -> Int

instance Shape '[] where
  {-# INLINE shapeP #-}
  shapeP _ = []
  {-# INLINE sizeP #-}
  sizeP  _ = 1

instance forall n s . (Shape s, KnownNat n) => Shape (n ': s) where
  {-# INLINE shapeP #-}
  shapeP = const sh
    where sh = sizeP (Proxy :: Proxy (n ': s)) `seq` fromInteger (natVal (Proxy :: Proxy n)) : shapeP (Proxy :: Proxy s)
#if defined(INL)
  {-# INLINE sizeP #-}
#else
  {-# NOINLINE sizeP #-}
#endif
  sizeP = const sz
#if defined(ONEPATH)
    where sz | n > toInteger (maxBound :: Int) || i > 1000000 =
#else
    where sz | n > toInteger (maxBound :: Int) || m /= 0 && i > maxBound `quot` m =
#endif
                 error $ "Shape: a shape ending in "
#if defined(NOSHAPE)
                         ++ show n
#else
                         ++ show (n : map toInteger (shapeP (Proxy :: Proxy s)))
#endif
                         ++ " has an extent or a size past maxBound"
             | otherwise = i * m
          n = natVal (Proxy :: Proxy n)
          i = fromInteger n :: Int
          m = sizeP (Proxy :: Proxy s)
```

```haskell
{-# LANGUAGE CPP, DataKinds #-}
module Client (size, shape) where

import Data.Proxy
import Shape

#if RANK == 2
type Sh = '[2, 3]
#elif RANK == 3
type Sh = '[2, 3, 4]
#elif RANK == 4
type Sh = '[2, 3, 4, 5]
#elif RANK == 5
type Sh = '[2, 3, 4, 5, 6]
#elif RANK == 6
type Sh = '[2, 3, 4, 5, 6, 7]
#elif RANK == 7
type Sh = '[2, 3, 4, 5, 6, 7, 8]
#else
type Sh = '[2, 3, 4, 5, 6, 7, 8, 9]
#endif

size :: Int
size = sizeP (Proxy :: Proxy Sh)

shape :: [Int]
#if defined(ONLYSIZE)
shape = []
#else
shape = shapeP (Proxy :: Proxy Sh)
#endif
```

`Client.dump-simpl-stats`, total ticks, whitespace collapsed:

```
noinline4  Total ticks: 100
inline2    Total ticks: 1306
inline3    Total ticks: 4305
inline4big Total ticks: 14374
inline5big Total ticks: 48599
noshape4   Total ticks: 4044
noshape5   Total ticks: 8185
onlysize5  Total ticks: 705
onlysize6  Total ticks: 846
```

`inline4`'s and `noshape6`'s `build.log`:

```
Simplifier ticks exhausted
When trying RuleFired Class op natSing
Total ticks: 6491
```

```
Simplifier ticks exhausted
When trying RuleFired quotInt#
Total ticks: 7443
```

Inlinings in `inline3`'s statistics, against `noinline4`'s `4 $fShape:_$cshapeP`, at a rank more:

```
9 $fShape:_$csizeP
19 $fShape:_$cshapeP
```

The copies fold away: `inline3`'s `Client.dump-simpl` has `size = I# 24#`, while `noinline4`'s calls the method on the dictionary:

```
shape20 = $fShape:_$csizeP shape22 (C:KnownNat (shape21 `cast` <Co:3>))
size = shape20 Proxy
```

Where the copies double, read in `noshape4`'s `Shape.iface`: the cons instance's stored `shapeP` builds the cons holding `shapeP` at the next rank under both of the guard's non-bottoming paths, `-> case GHC.Internal.Classes.neInt m (GHC.Internal.Types.I# 0#) of wild { GHC.Internal.Types.False -> case i of wild1 { GHC.Internal.Types.I# x2 -> case m of wild2 { GHC.Internal.Types.I# y -> GHC.Internal.Types.:` ... and the join point `$j1 :: [GHC.Internal.Types.Int] JoinPoint(0) [] = case m of wild2 { GHC.Internal.Types.I# y -> case GHC.Internal.Classes.gtInt i (GHC.Internal.Types.I# (GHC.Internal.Prim.quotInt# 9223372036854775807# y)) of wild3 {` ... that `||` gives (whitespace collapsed), so the client's statistics count `15 Shape.$fShape:_$cshapeP` at rank 4 and `31 Shape.$fShape:_$cshapeP` at rank 5, `Total ticks: 8185`; with one such path, `5 Shape.$fShape:_$cshapeP` at rank 5 and `6 Shape.$fShape:_$cshapeP` at rank 6, `Total ticks: 2702`.

**Reproduces small:** yes, at rank 4 at the default tick factor, at `Class op natSing` as orthotope's ShapedGTest did; ShapedTest's `unpack` not met.

### O15. A strict constructor applied in part leaves its field a lazy argument, which float-out lifts from a client as a constant; applied in full, its field is evaluated by a case that stays at each call

**Rule.** A call gets its callee's argument demands only when it gives at least the callee's arity of value arguments; with fewer, every argument is treated as lazy (`mkArgInfo`, [compiler/GHC/Core/Opt/Simplify/Utils.hs#L722][g417], Note [Unsaturated functions]). A strict argument of a saturated call is simplified with the call as its continuation, a `StrictArg`, when case-of-case is on (`rebuildCall`, [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L2490][g65]), so an argument that is a `case`, such as `tail` inlined, ends up outside the call. A constructor with strict fields, one of them unpacked, as `-O` unpacks `T`'s `!Int`, is called through its wrapper `$WT` (A25), whose arity is the number of fields and whose demand on each strict field is strict (`mk_dmd`, [compiler/GHC/Types/Id/Make.hs#L782][g418]). So `fromVectorT sh = T (tail $ getStridesT sh) 0`, the wrapper given two of its three arguments, keeps `$WT (case getStridesT sh of ...) 0` in its INLINE unfolding, the `case` a lazy argument; `fromVectorT sh v = T (tail $ getStridesT sh) 0 v`, the wrapper saturated, has its unfolding simplified in the defining module into `case getStridesT sh of { ...; : _ xs -> ... }`, the constructor inside. In a client the first float-out runs after only the gentle simplifier pass and the specialiser ([compiler/GHC/Core/Opt/Pipeline.hs#L202][g419], [#L209][g319]), which has case-of-case off (`initGentleSimplMode`, [compiler/GHC/Driver/Config/Core/Opt/Simplify.hs#L84][g333]), so the point-free form's `case` is still a lazy argument there, and float-out lifts it, free of local variables where the shape is a constant, to top level as a thunk (`lvlMFE`, [compiler/GHC/Core/Opt/SetLevels.hs#L615][g420]; a `case` in a strict context is not floated whole, [#L611][g421], and this one is lazy). The named form's `case` is a scrutinised expression: float-out lifts its scrutinee, `getStridesT sh` (`lvlExpr`, [SetLevels.hs#L381][g422], the scrutinee by `lvlNonTailMFE`), but a `case` of two alternatives stays put (`lvlCase`, [#L444][g423], its second clause), so the tail is taken at each call and its variable `xs`, bound before the client fills the vector, is live across the fill until the constructor is built after it.

**Seen.** Orthotope's `fromVectorT` (`Data/Array/Internal.hs` at "Give each binding the pragma its kind calls for", with the comment that commit "Say why the point-free definitions stay point-free" gave it), named in "Name the arguments of Internal's point-free definitions", against the point-free form of "Loop over two lists in stretchT and dropBroadcastT": Shaped `traverseA` with its result forced took 13 instructions a call more and one an element, the named build's `OpsShaped.$wlvl374` (the large size, Unboxed elements) taking the tail by a `case` on `$s$wforce5` at its head where the point-free one evaluates the floated constant `lvl834`, and its assembly reloading five stack slots after each element of the fill loop where the point-free one reloads four. In the two builds' `OpsShaped.dump-asm` (`.L$wlvl374_info`), the named form's head enters the strides constant through an untagged reference, `leaq OpsShaped.$s$wforce5_closure(%rip),%rbx`, so through `stg_IND_STATIC` and the cons constructor's entry, then tests its constructor (`andl $7,%eax`, `cmpq $1,%rax`) and pushes a frame holding `xs`, about 20 instructions more, and at its end takes `xs` from that frame where the point-free form enters the floated tail `.Llvl1811_closure`, about 7 fewer: 13 a call, counting `xs` as tagged.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/O15-strict-con-partial-application`, variants `pointfree` and `named`, `named` adding `-DNAMED`, at a [4, 5] shape, and `pointfree80` and `named80` at [8, 10], adding `-DBIG`; `measure.sh N` gives instructions and bytes a call of `step` from N and 2N iterations): orthotope's `T`, `getStridesT`, `fromVectorT`, `fromListT` and `traverseT` over boxed vectors, and a client traversing an array of a constant shape.

```haskell
{-# LANGUAGE BangPatterns, CPP #-}
module Lib (T (..), getStridesT, fromVectorT, fromListT, traverseT) where

import qualified Data.Vector as V

-- orthotope's array: strict strides, offset and values.
data T a = T ![Int] !Int !(V.Vector a)

getStridesT :: [Int] -> [Int]
getStridesT [] = [1]
getStridesT (s : ss) = case getStridesT ss of
  r@(m : _) -> let !x = s * m in x : r
  [] -> []

{-# INLINE fromVectorT #-}
fromVectorT :: [Int] -> V.Vector a -> T a
#if defined(NAMED)
fromVectorT sh v = T (tail $ getStridesT sh) 0 v
#else
fromVectorT sh = T (tail $ getStridesT sh) 0
#endif

{-# INLINE fromListT #-}
fromListT :: [Int] -> [a] -> T a
fromListT sh = fromVectorT sh . V.fromListN (product sh)

{-# INLINE traverseT #-}
traverseT :: Applicative f => [Int] -> (a -> f b) -> T a -> f (T b)
traverseT sh f (T _ o v) = fromListT sh <$> traverse f (V.toList (V.drop o v))
```

```haskell
{-# LANGUAGE BangPatterns, CPP #-}
module Main (main) where

import Data.Functor.Identity
import qualified Data.Vector as V
import Lib
import System.Environment (getArgs)

-- A client with a constant shape, as a Shaped array's is.
{-# NOINLINE step #-}
step :: T Int -> T Int
#if defined(BIG)
step a = runIdentity (traverseT [8, 10] (\x -> Identity (x + 1)) a)
#else
step a = runIdentity (traverseT [4, 5] (\x -> Identity (x + 1)) a)
#endif

main :: IO ()
main = do
  [ns] <- getArgs
  let n = read ns :: Int
#if defined(BIG)
      a0 = fromListT [8, 10] [1 .. 80 :: Int]
#else
      a0 = fromListT [4, 5] [1 .. 20 :: Int]
#endif
      go :: Int -> T Int -> Int
      go 0 (T _ _ v) = V.sum v
      go k !a = go (k - 1) (step a)
  print (go n a0)
```

`Lib.iface`, `fromVectorT`, whitespace collapsed: `pointfree` has `Arity: 1, Strictness: <ML>, Inline: (sat-args=1),` and the unfolding `$WT @a (case getStridesT eta of wild {`; `named` has `Arity: 2, Strictness: <1L><SL>, CPR: 1, Inline: (sat-args=2),` and the unfolding `(eta1['GHC.Internal.Types.Many] :: Data.Vector.Vector a) -> case getStridesT eta of wild {`.

`pointfree`'s `Main.dump-simpl`: the tail floated whole, and evaluated after the fill:

```
lvl1 = case getStridesT main_eta of { [] -> lvl (C:IP main3); : _ xs -> xs }
case lvl1 of wild1 { __DEFAULT ->
```

`named`'s: only the strides floated, the tail taken at the head of `$wstep` and `xs` evaluated after the fill:

```
main7 = getStridesT main_eta
case main7 of { [] -> case main6 of {}; : ds1 xs -> runRW#
case xs of wild2 { __DEFAULT ->
```

`measure.sh 1000000`: the named form costs 32 instructions a call more at 20 elements and 131 at 80, about 1.65 an element and nothing a call, at equal bytes:

```
pointfree: 20957.8 instructions, 2690.7 bytes a call
named: 20989.6 instructions, 2690.7 bytes a call
pointfree80: 82884.7 instructions, 10426.9 bytes a call
named80: 83015.6 instructions, 10426.9 bytes a call
```

**Reproduces small:** yes, the floated constant against the per-call `case` and the cost an element; orthotope's 13 instructions a call not met, the model's call costing nothing measurable; orthotope's are its named form entering and testing the strides constant (Seen).

### O16. A value a case binds whole becomes a join point's argument under case-of-case, so each branch of an inlined function returning a sum builds its constructor to jump there, under INLINE or INLINABLE on the caller and at -O2

**Rule.** Case-of-case pushes an outer `case` into the branches of an inner one by making a join point of each outer alternative too big to duplicate (`uncondInlineJoin`), abstracted over the variables the alternative binds and, if the alternative uses it, over the case binder (`mkDupableAlt`, [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4325][g424], its `abstract_binders`: "Abstract over the case binder too if it's used"). Where the outer `case` scrutinises a call of an inlined function returning a sum, each branch of the function then meets the alternatives with its constructor known: an alternative matching the constructor's fields gets the fields as arguments, and the constructor is never built; an alternative that binds the value whole, a variable pattern or a value bound to a variable and taken apart later, gets the constructor as its argument, so the branch builds it to jump. The join point takes it apart again, and since it holds the walk over the parts it is far past the size at which a join point is inlined at a jump (A18), so case-of-known-constructor never meets the constructor. Orthotope's `foldPartsT` matches its two routes as a pair, `case (routeT s l x, routeT s l y) of`, with the variable patterns `rx` and `ry`: each route is bound to a variable and taken apart in a join point, at INLINE or INLINABLE on the caller and at -O2 alike. Matched by constructor in nested cases, the routes are taken apart where they are built. This is the second half of O12: there a sum is built because the function returning it is called out of line; here it is inlined, and built anyway. The working tree's patch to `simplLetUnfolding` ([compiler/GHC/Core/Opt/Simplify/Iteration.hs][g2] line 4864 in the tree's patch, GHC [#27885](https://gitlab.haskell.org/ghc/ghc/-/work_items/27885), U14) is what gives this join point the unfolding whose rejection (A18) `check` reports; at commit 6913545fd3 a join point occurring many times gets no unfolding, which, by the source, leaves it out of line all the same.

**Seen.** Orthotope's `equalT`, behind `==` and `compare`, in the benchmark's Core (build X1's `OpsDynamic.dump-simpl`), "builds a Route and passes it to a join point that takes it apart", `jump $j12 (Data.Array.Internal.RSlice ww2 wild7)` and `jump $j12 (Data.Array.Internal.RRuns ...`, with `RSlice`, `RRuns`, `RFill` and `Axes` built in 18 to 27 client bindings in the base (X1, H0) and 18 to 30 with the pragma work (R3), "and nothing in the source says whether it is intended"; `docs/perf-checklist.md` A3 records the same. Its source, `foldPartsT` (`Data/Array/Internal.hs` at "Give each binding the pragma its kind calls for"), matches `(routeT s l x, routeT s l y)` with the arms `(RSlice ox _, RSlice oy _)`, `(rx, RSlice oy _)`, `(RSlice ox _, ry)` and `(rx, _)`. At "Condense the account of unorderedRouteT's sort and merge" (`OpsDynamic.dump-simpl`), whose `foldPartsT` is that of "Give each binding the pragma its kind calls for", `OpsDynamic.$w$s$wequalT` takes x's route and y's as the arguments of nested join points, `$j19 (ds26 :: I.Route)` and `$j20 (ds27 :: I.Route)`, and every branch of the inlined `routeT` builds its route to jump, `jump $j20 (Data.Array.Internal.RSlice ww5 wild4)`, `jump $j20 (Data.Array.Internal.RRuns (Data.Array.Internal.Axes 1# ww11` ... and `jump $j20 (Data.Array.Internal.RFill (Data.Array.Internal.Axes wild8 ww11 ww12) ww5 wild4)` (whitespace collapsed): the model's path, `RRuns` and `Axes` included.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/O16-route-at-join-point`, variants `inline` (`-DINL`, `compareT` INLINE) and `inlinable` at -O, `inlineO2` and `inlinableO2` at -O2, `fields` (`-DINL -DFIELDS`, `inline` with `foldPartsT`'s routes matched by constructor) and `check`, `inline` with `-dinline-check $j`; `measure.sh N` gives instructions and bytes a call of `compareT` from N and 2N iterations): O08's model, a transposed [40, 50] view, its route `RFill`, compared with a dense array, its route `RSlice`, their first elements differing so that a call compares one.

```haskell
{-# LANGUAGE BangPatterns, CPP, ScopedTypeVariables #-}
module Lib (T (..), compareT) where

import qualified Data.Vector.Generic as G

-- orthotope's array, its route and its fold over parts, at rank 2.
data T v a = T ![Int] !Int !(v a)

data Axis = Axis !Int !Int  -- stride and extent

data Route = RSlice !Int !Int | RFill !Axis [Axis] !Int
  -- RFill: the innermost axis, the axes outside it innermost first, offset

{-# INLINE routeT #-}
routeT :: [Int] -> T v a -> Route
routeT [m, n] (T [s, t] o _)
  | t == 1 && s == n = RSlice o (m * n)
  | otherwise = RFill (Axis t n) [Axis s m] o
routeT _ _ = error "routeT: rank 2 only"

-- orthotope's odometer, its walk and its step, as at "Give each binding the
-- pragma its kind calls for".
data Odometer = OdoLevel !Int !Int !Axis !Odometer | OdoDone

stepOdometer :: Odometer -> Odometer
stepOdometer OdoDone = OdoDone
stepOdometer (OdoLevel o c axis@(Axis s d) outer)
  | c > 1 = OdoLevel (o + s) (c - 1) axis outer
  | otherwise = case stepOdometer outer of
      OdoDone -> OdoDone
      next@(OdoLevel o' _ _ _) -> OdoLevel o' d axis next

{-# INLINE offsetsT #-}
offsetsT :: forall b. Axis -> [Axis] -> Int -> (Int -> b -> b) -> b -> b
offsetsT (Axis sk dk) above !start step nil =
  let block :: Int -> Odometer -> b
      block o outer =
        let go :: Int -> Int -> b
            go !i !p
              | i < dk = step p (go (i + 1) (p + sk))
              | otherwise = case stepOdometer outer of
                  OdoDone -> nil
                  next@(OdoLevel oNext _ _ _) -> block oNext next
        in  go 0 o
  in  block start
            (foldr (\axis@(Axis _ d) outer -> OdoLevel start d axis outer)
                   OdoDone above)

-- The parts a route reads, by the step and nil of a right fold.
{-# INLINE routePartsT #-}
routePartsT :: Route -> (Int -> Int -> b -> b) -> b -> b
routePartsT route step nil = case route of
  RSlice o l -> step o l nil
  RFill axis outer o -> offsetsT axis outer o (\p rest -> step p 1 rest) nil

{-# INLINE foldPartsT #-}
foldPartsT :: G.Vector v a
           => (r -> r -> r) -> r -> (v a -> v a -> Int -> Int -> Int -> r)
           -> [Int] -> T v a -> T v a -> r
foldPartsT c e goWith s x@(T sx ox vx) y@(T sy oy vy)
  | l == 0 = e
  | sx == sy = routePartsT (routeT s x) (\p n rest -> go p (p + d) n `c` rest) e
#if defined(FIELDS)
  -- Each route taken apart by its constructor, and rebuilt where it is used.
  | otherwise = case routeT s x of
      RSlice ox' _ -> case routeT s y of
        RSlice oy' _ -> go ox' oy' l
        RFill ay as oy ->
          routePartsT (RFill ay as oy) (\p n rest !q -> go q p n `c` rest (q + n))
                      (\ !_ -> e) ox'
      RFill ax as ox'' -> case routeT s y of
        RSlice oy' _ ->
          routePartsT (RFill ax as ox'') (\p n rest !q -> go p q n `c` rest (q + n))
                      (\ !_ -> e) oy'
        RFill {} -> error "foldPartsT: two views not modelled"
#else
  -- orthotope's: the two routes matched as a pair.
  | otherwise = case (routeT s x, routeT s y) of
      (RSlice ox' _, RSlice oy' _) -> go ox' oy' l
      (rx, RSlice oy' _) ->
        routePartsT rx (\p n rest !q -> go p q n `c` rest (q + n)) (\ !_ -> e) oy'
      (RSlice ox' _, ry) ->
        routePartsT ry (\p n rest !q -> go q p n `c` rest (q + n)) (\ !_ -> e) ox'
      _ -> error "foldPartsT: two views not modelled"
#endif
  where
    !l = product s
    !d = oy - ox
    go = goWith vx vy

#if defined(INL)
{-# INLINE compareT #-}
#else
{-# INLINABLE compareT #-}
#endif
compareT :: (G.Vector v a, Ord a) => [Int] -> T v a -> T v a -> Ordering
#if defined(ETA)
compareT s x y = foldPartsT (<>) EQ cmpWith s x y
#else
compareT = foldPartsT (<>) EQ cmpWith
#endif
  where cmpWith u w !ox !oy !k = loop u w 0
          where loop !u' !w' !i
                  | i >= k = EQ
                  | otherwise =
                      case compare (G.unsafeIndex u' (ox + i))
                                   (G.unsafeIndex w' (oy + i)) of
                        EQ -> loop u' w' (i + 1)
                        o -> o
```

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import qualified Data.Vector.Storable as V
import Lib
import System.Environment (getArgs)

-- Opaque, so that each iteration compares anew and nothing about the views
-- is known at the call.
{-# OPAQUE pass #-}
pass :: Int -> T v a -> T v a
pass _ x = x

main :: IO ()
main = do
  [ns] <- getArgs
  let n = read ns :: Int
      -- A transposed [40, 50] view, its route RFill, against a dense array,
      -- its route RSlice; their first elements differ, so a call compares one.
      v = V.generate 2000 fromIntegral :: V.Vector Double
      x = T [1, 40] 0 v
      y = T [50, 1] 0 (V.map (+ 1) v)
      go :: Int -> Int -> Int
      go 0 !acc = acc
      go k !acc =
        go (k - 1) (acc + fromEnum (compareT [40, 50] (pass k x) (pass k y)))
  print (go n 0)
```

`Main.dump-simpl`, whitespace collapsed. `inline`: a jump building the dense array's route, and the join point taking the routes apart:

```
jump $j2 (RSlice bx1 2000#)
join { $j2 ds2 = join { fail ds6 = case ds2 of { RSlice bx2 bx3 -> case ds of { RSlice bx4 bx5 ->
```

`inlinable`: `jump $j2 (RSlice ww5 (*# x7 y5))`; `inlineO2`: `jump $j2 (RFill lvl35 (: (Axis wild24 40#) []) bx3)` and `join { $j2 ds2 = case ds2 of { RSlice bx4 bx5 ->`; `inlinableO2`: `jump $j1 (RFill (Axis 1# y5) (: (Axis x8 x6) []) ww5)`. `fields` has no jump with a route. `check`'s `build.log`, the join point at a jump giving it a constructor:

```
Considering inlining: $j
  arg infos [ValueArg]
  interesting continuation BoringCtxt
  some_benefit True
  is exp: True
  is work-free: True
  guidance IF_ARGS [324] 668 0
  case depth = 3
  inline depth = 1
  join (ww, False, Just False, False) ($wgo, True, Just True, False)
       (lvl, True, Just False, False) (ds, False, Just False, False)
       (stepOdometer, False, Just True, False)
  depth based penalty = 22
  adjusted size = 346
  ANSWER = NO
```

`measure.sh 1000000`:

```
inline: 338.6 instructions, 176.0 bytes a call
inlinable: 474.8 instructions, 184.0 bytes a call
inlineO2: 286.0 instructions, 96.0 bytes a call
inlinableO2: 442.1 instructions, 104.0 bytes a call
fields: 268.0 instructions, 48.0 bytes a call
```

Under INLINE at -O the routes built cost 128 bytes and 71 instructions a call against `fields`.

**Reproduces small:** yes, the routes built for a join point under either pragma and at -O2; the model's `Route` has `RSlice` and `RFill` only, and orthotope's `RRuns` and `Axes`, read in its Core, are built the same way.

### O17. An INLINE function in a recursive group with a self-recursive INLINABLE one is inlined into it and its unfolding, so a client's specialisation of the loop breaker resolves the class methods the INLINE body calls

**Rule.** A self-recursive binding is the first choice for loop breaker of its group, and an INLINE binding among the last (A11). So an INLINE function in a group with a self-recursive INLINABLE function is not the loop breaker, and the defining module inlines it into that function, into its right-hand side and into its INLINABLE unfolding alike, the INLINE unfolding being active throughout the INLINABLE one's activation (U10). A client's specialisation of the INLINABLE function, made from that unfolding, holds the INLINE body's call of a class method at the specialised dictionary, which the class-op rule resolves to the instance's method (A15). Without a pragma, the same function, too big to be inlined there or to have its unfolding exposed (U05), stays a call in the unfolding, and a client cannot specialise it, since it carries no pragma, unless the modules are built with both `-fexpose-overloaded-unfoldings` and `-fspecialise-aggressively` (the specialisation appendix, "Which imported functions are specialised"): the specialisation calls it with the dictionary, and the method is selected inside it at run time. NOINLINE gives the same call. INLINABLE in its place gives the client a specialised copy of it, in which the method is resolved as well. The working tree's patch to `spec_import` ([compiler/GHC/Core/Opt/Specialise.hs][g3], its `not_on_stack` filter and `strictlyMoreGeneral`), which lets a function on the stack of imported functions being specialised be specialised again at a strictly more general key, bears on that chain, the specialised `interpFun` calling `interp` again, but not on this repro's, whose call of `interp` inside the HFun carries no interesting dictionary and so records no call (`mkCallUDs'`, its key `ci_key = dropWhileEndLE (not . isSpecDict)`, [compiler/GHC/Core/Opt/Specialise.hs#L3043][g425], and its `not (null ci_key)` test, [#L3029][g426]). The patch bears on the repro once that call also carries a known dictionary of a second class, as `interpretAst`'s call carries a `KnownSpan` dictionary: the client then specialises `interp`, from inside its own specialisation of `interp`, at a key strictly more general than the one being specialised, a call that the guard the patch removes, `isIn "specImport" fn callers`, would drop (second repro; read from the patch, no compiler without it being at hand).

**Seen.** horde-ad's `interpretAstHFun` (`src/HordeAd/Core/AstInterpret.hs`), INLINE in a recursive group with the INLINABLE `interpretAst`, its loop breaker, its comment saying that "inlining into the specialised interpretAst is what gives the call to tlambda a known instance" and that without it "the grad MapAccum benchmarks of shortProdForCI allocated up to 43% more (GHC 10.1.20260918, 2026-09-27)". Commit 8b78b6566, "Drop INLINE from recursive functions and methods where it costs", kept it with `astConvDown`, `astConvUp`, `tappend` and `tunravelToListShare`: without those five, the benchmarks "took 8 to 14% more instructions and allocated 15 to 43% more", and "INLINABLE in their place recovers only AstRaw's tappend, and NOINLINE is no better than no pragma"; neither figure is met on HEAD as built 2026-10-14, at 8b78b6566 or 4b2ad4979, against either orthotope, the one recorded condition not reproduced being the compiler, which since 2026-10-03 carries the patches named at the top of this catalogue.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/O17-inline-in-recursive-group`, variants `inline` (`-DINL`), `none`, `inlinable` (`-DINLABLE`) and `noinline` (`-DNOINL`), the pragma on `interpFun`; `measure.sh N` gives instructions and bytes a call of `interp` from N and 2N iterations): a class with horde-ad's `tlambda` taking a function given at every target, a recursive INLINABLE interpreter `interp`, and `interpFun`, which calls `tlambda` and, in the function it passes, `interp` at that function's target; and a client interpreting a term at `Double`.

```haskell
{-# LANGUAGE CPP, RankNTypes #-}
module Lib (HFun (..), Target (..), Ast (..), Fn (..), interp) where

-- horde-ad's HFun: a function given at every target.
newtype HFun = HFun (forall f. Target f => f -> f)

-- BaseTensor's tlambda, the one method here besides Num's.
class Num t => Target t where
  tlambda :: HFun -> t -> t

data Ast = Lit Int | Var | Add Ast Ast | Mul Ast Ast | Apply Fn Ast
data Fn = Lambda Ast | Lambda2 Ast Ast | Lambda3 Ast Ast Ast

-- interpretAst: recursive, INLINABLE, the loop breaker of its group.
{-# INLINABLE interp #-}
interp :: Target t => t -> Ast -> t
interp _ (Lit k) = fromIntegral k
interp x Var = x
interp x (Add a b) = interp x a + interp x b
interp x (Mul a b) = interp x a * interp x b
interp x (Apply f a) = interpFun f (interp x a)

-- interpretAstHFun: in the group through interp, which it calls at the
-- target its function is given.
#if defined(INL)
{-# INLINE interpFun #-}
#elif defined(INLABLE)
{-# INLINABLE interpFun #-}
#elif defined(NOINL)
{-# NOINLINE interpFun #-}
#endif
interpFun :: Target t => Fn -> t -> t
interpFun (Lambda body) = tlambda (HFun (\y -> interp y body))
interpFun (Lambda2 b1 b2) =
  tlambda (HFun (\y -> interp y b1 * interp y b2 + interp y b1 - interp y b2))
interpFun (Lambda3 b1 b2 b3) =
  tlambda (HFun (\y -> let z = interp y b1 * interp y b2
                       in z * interp y b3 + z - interp (z + y) b3 * interp z b2))
```

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import Lib
import System.Environment (getArgs)

-- A concrete target: tlambda applies the function at this instance.
instance Target Double where
  tlambda (HFun g) x = g x

-- Opaque, so that each iteration interprets anew.
{-# OPAQUE pass #-}
pass :: Int -> Ast -> Ast
pass _ a = a

-- (\y -> y * y + 1) applied to x + 2.
term :: Ast
term = Apply (Lambda (Add (Mul Var Var) (Lit 1))) (Add Var (Lit 2))

main :: IO ()
main = do
  [ns] <- getArgs
  let n = read ns :: Int
      go :: Int -> Double -> Double
      go 0 !acc = acc
      go k !acc = go (k - 1) (acc + interp (fromIntegral k :: Double) (pass k term))
  print (go n 0)
```

`inline`: `Lib.dump-inlinings` has `Inlining done: interpFun`, and `Lib.iface` has no `interpFun`, `interp`'s INLINABLE unfolding holding `tlambda` itself, `interp` marked `Unfolding(loop-breaker): Core: StableUser`. `none`: `interp`'s unfolding keeps the call, whitespace collapsed:

```
Apply f a -> interpFun @t $dTarget f (interp @t $dTarget eta a) }]
```

`Main.dump-simpl`, the `Apply` branch of the client's specialisation `$sinterp`: at `inline`, the instance's method called directly,

```
Lambda body -> $fTargetDouble_$ctlambda ((\ @f1 $dTarget1 y -> interp $dTarget1 y body) `cast` <Co:2>) ($sinterp eta a);
```

at `none` and `noinline`, the library's function called with the dictionary, and at `inlinable`, a specialised copy:

```
Apply f a -> interpFun $fTargetDouble f ($sinterp eta a)
Apply f a -> $sinterpFun f ($sinterp eta a)
```

`measure.sh 1000000`:

```
inline: 746.2 instructions, 360.0 bytes a call
none: 782.1 instructions, 360.0 bytes a call
inlinable: 756.1 instructions, 360.0 bytes a call
noinline: 782.1 instructions, 360.0 bytes a call
```

A second repro (`~/r/horde-ad/dist-inlcat/cases/O17-spec-import-patch`, variants `inline` and `inlinable`, with `-ddump-spec`; `measure.sh N`): the first repro's interpreter with a second class, a span as horde-ad's `KnownSpan`, so that the call of `interp` inside the HFun, at the function's own target, carries one interesting dictionary, the span's, and one that is not; `Main` is the first repro's, calling `interp (Proxy :: Proxy SA)`.

```haskell
{-# LANGUAGE CPP, RankNTypes, ScopedTypeVariables, KindSignatures #-}
module Lib (HFun (..), Target (..), KnownS (..), SA, Ast (..), Fn (..), interp) where

import Data.Proxy

newtype HFun = HFun (forall f. Target f => f -> f)

class Num t => Target t where
  tlambda :: HFun -> t -> t

class KnownS s where
  sp :: Proxy s -> Int
data SA
instance KnownS SA where
  sp _ = 1

data Ast = Lit Int | Var | Add Ast Ast | Mul Ast Ast | Apply Fn Ast
data Fn = Lambda Ast | Lambda2 Ast Ast | Lambda3 Ast Ast Ast

{-# INLINABLE interp #-}
interp :: forall s t. (KnownS s, Target t) => Proxy s -> t -> Ast -> t
interp p _ (Lit k) = fromIntegral (k + sp p)
interp _ x Var = x
interp p x (Add a b) = interp p x a + interp p x b
interp p x (Mul a b) = interp p x a * interp p x b
interp p x (Apply f a) = interpFun p f (interp p x a)

#if defined(INL)
{-# INLINE interpFun #-}
#elif defined(INLABLE)
{-# INLINABLE interpFun #-}
#endif
interpFun :: forall s t. (KnownS s, Target t) => Proxy s -> Fn -> t -> t
interpFun p (Lambda body) = tlambda (HFun (\y -> interp p y body))
interpFun p (Lambda2 b1 b2) =
  tlambda (HFun (\y -> interp p y b1 * interp p y b2 + interp p y b1 - interp p y b2))
interpFun p (Lambda3 b1 b2 b3) =
  tlambda (HFun (\y -> let z = interp p y b1 * interp p y b2
                       in z * interp p y b3 + z - interp p (z + y) b3 * interp p z b2))
```

In `inline`'s specialiser output the client makes `"SPEC/Main interp @(*) @SA @_"` beside `"SPEC/Main interp @(*) @SA @Double"`, and the HFun's body calls the copy polymorphic in the target, `(\ @f2 $dTarget1 y -> $w$sinterp $dTarget1 y body)` (whitespace collapsed). By `measure.sh 100000`, INLINE 747.1 instructions a call and INLINABLE 763.0, both 360.0 bytes.

**Reproduces small:** in part: the mechanism, yes, the method resolved only under INLINE or INLINABLE; the cost only in instructions, 36 a call, the allocation horde-ad measured not met, the model's `tlambda` building nothing; and INLINABLE recovers most of it here, 26 of the 36. horde-ad's cost was not met on HEAD: at 8b78b6566, removing all five INLINEs the commit kept moves shortProdForCI's four grad MapAccum benchmarks by at most 187 bytes and 2000 instructions a call, against released orthotope 0.1.8.0 and against its commit "Port the Ax path's merge and nest loops to the pair arms" alike. INLINABLE on `interpretAstHFun` alone, and, built from 4b2ad4979, no pragma on it, match INLINE within 8 bytes and 80 instructions: under `-fexpose-overloaded-unfoldings` with `-fspecialise-aggressively`, both of which horde-ad sets, a client specialises the pragma-free function as it does an INLINABLE one, as this repro's `none` variant shows: its `interpFun` is specialised when both flags are given, and not when only one is. With `interpFun` small, one equation, `none` and `inlinable` matched `inline`, the function being inlined into `interp`'s unfolding without a pragma.

### O18. INLINE on a forcing chain puts the copy and the summing into one function, where the sum loop's address and bound, spilled across the copy's `memcpy` call with nothing reading them before the loop, stay in their stack slots and are loaded at every element, the loop's Core unchanged, as in orthotope's Storable sum

**Rule.** A loop evaluating no lifted element, such as a sum over a Storable vector, has no return point to reload its live values at (O02), so where it follows a copy's call in one function with nothing reading its values in between, the values spilled across that call stay in their slots and are loaded at every step. Orthotope's case gives that shape: INLINE inlines `force`, `forceT` and `genericForce` whatever their size (A05), so the summing function receives the copy, `VG.create`'s `runRW#` around it, and the simplifier's `runRW#` rule pushes the strict context of a `runRW#` call, here the summing of the vector it returns, into its argument (`simplOutId`, [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L2390][g427]; Note [Simplification of runRW#], [compiler/GHC/CoreToStg/Prep.hs#L1379][g428]), so the summing is compiled inside force's body, after the copy; without the pragma, the summing function calls `force`'s worker and runs the summing loop over what it returns. Both forms give the sum loop the same Core, a bound test, a `readDoubleOffAddr#`, a `touch#` and an add a step. What moves the instructions is below Core, in the code the linear register allocator makes of the loop inside the larger function, as the third repro shows: the sum loop's address and bound are live across the copy's `call memcpy` and are spilled before it (`saveClobberedTemps`, [compiler/GHC/CmmToAsm/Reg/Linear.hs#L672][g429], its body not read); nothing uses them between the call and the loop, so the block after the call jumps to the loop head with both in their slots, and the head takes that block's assignment as its own, locations in memory included (`joinToTargets_first`, [compiler/GHC/CmmToAsm/Reg/Linear/JoinToTargets.hs#L130][g377]); each read then loads the value from its slot (`loadTemp`, [compiler/GHC/CmmToAsm/Reg/Linear.hs#L1019][g430]), and at the back edge a value held both in a register and in its slot meets the head's slot-only assignment with no move (`expandNode`, `(InBoth _ srcMem, InMem dstMem) | srcMem == dstMem -> []`, [compiler/GHC/CmmToAsm/Reg/Linear/JoinToTargets.hs#L286][g431]), so the next iteration loads it again; the order in which the allocator processes the blocks was not read. A Haskell call or an evaluation between the copy and the loop ends the block at a return point, where the values are read back from the Haskell stack into registers, as in the second repro and in the third's form with the strides computed by a call. This is the class of GHC [#27737](https://gitlab.haskell.org/ghc/ghc/-/work_items/27737).

**Seen.** Summing a forced large dense Storable array, Dynamic and Ranked: the pragma commit "Give each binding the pragma its kind calls for" ran 35% more instructions than the tip, 400,000 a call, about 2 an element, and so did C3, whose `force` path it shares (the pragmas of C8: `genericForce`, the wrapper `force`s and `vForce` INLINE). In the dumps (C3's and the tip's `OpsDynamic.dump-simpl`, the row named `"force"` over Storable vectors): the tip's ("Condense the account of unorderedRouteT's sort and merge", `genericForce` and the wrapper `force`s INLINABLE) summing worker `$wlvl630` calls `OpsDynamic.$w$s$wforce1` and runs one sum loop `$wgo24` over the returned fields; C3's `$wlvl583` copies by `copyAddrToAddrNonOverlapping#` inside `runRW#` and holds four sum loops `$wgo27`, each with the tip's steps, the first (the only one read in place) inside the `runRW#` after the copy. In the same builds' binaries (`--summed`, `Dynamic/force/large/dense/Storable`), the tip's sum loop runs 5 instructions an element, `movsd (%rdx,%rax,8),%xmm1`, `addsd`, `inc`, `cmp`, `jl` (from `0x8968cc`), and C3's 7, adding two reloads from the C stack at every element, the address, `mov 0x50(%rsp),%rsi`, and the length, `mov 0x48(%rsp),%rdx` (from `0x1697978`), slots written just before the copy's `call memcpy@plt` at `0x16977ab`, with `%rsp` 8 lower there, by `mov %r10,0x58(%rsp)`, the new array's payload and the copy's destination, and `mov %r8,0x50(%rsp)`, past the same symbol; `perf`'s samples, about 19,900 against 27,800, fit 5 against 7. All of the chain INLINE (C8) ran Storable Dynamic and Ranked 34.7% more instructions, Unboxed 14.8% fewer and boxed 22 to 23% fewer; read again in its binary, against the tip's (`--summed`, `Dynamic/force/large/dense`, 20 and 40 iterations differenced), Storable 1.553M instructions a call against 1.152M, its loop C3's 7 instructions (from `0x16dc2d0`); Unboxed 1.152M against 1.352M, the tip adding the vector's offset at every element (`mov %rcx,%r9; add %r8,%r9`), C8 dropping that add but reloading its limit from `0x48(%rsp)`, 5 instructions against 6; and boxed 6.42M against 8.42M, the tip's loop reloading five values at each element's return point and saving seven before each evaluation, C8's three and five, about 42 and 32 instructions an element. The same reloads come with inlining done without a pragma: in orthotope's `padT`, U1 has its local `pad'` call itself, a loop breaker (A11) that the row allocates as a recursive local closure; in U4 `pad'`'s third equation recurses into a banged copy `padS`, so `pad'` is not recursive and has one call, outside any lambda of its own, and the simple optimiser that runs on the desugarer's output substitutes it at that call in `Data.Array.Internal` itself (`desugarOpt`, [compiler/GHC/Core/Opt/Pipeline.hs#L581][g432]; `pre_inline_unconditionally` in `simple_bind_pair`, [compiler/GHC/Core/SimpleOpt.hs#L738][g433]), so that `padT`'s interface template binds `padS` and no `pad'` (U4's `Data/Array/Internal.hi` read with `--show-iface`; `~/r/horde-ad/dist-inlcat/cases/O18-pad-simple-opt`, where `Lib.dump-ds-preopt` has `let { pad' = \ ds t ->` and `Lib.dump-ds` none). At summed Dynamic and Ranked Storable `pad.outer` large U4 runs 21 to 36% more instructions: the summing worker `$wlvl582` holds `pad'` as a nest of join points ahead of `$wpadS`, and its loop over the 201000 elements runs 5 instructions an element besides the add where U1's runs 3, reloading the vector's address and the loop's bound from the stack at every element (`mov 0xc8(%rsp),%rdx`, `mov 0x90(%rsp),%r10`), slots written, as at C3, just before the pad's `call memcpy@plt` (`0x10983c5` in U4's binary, `%rsp` 8 lower there, by `mov %r9,0xd0(%rsp)` and `mov %r10,0x98(%rsp)`), and written again at the return point `0x10984b0` with values reloaded from the Haskell stack, before the path to the loop joins (inferred). `pad'` given a local NOINLINE (U4a) removes the reloads, and with them U4's gains at the other `pad` cells (240 to 950 instructions a call), Storable and Unboxed small `pad` then 15 to 29% dearer.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/O18-force-fill-inlined`, variants `inline` and `inlinable`; `run` is `100000 100`; `measure.sh K N`): orthotope's `genericForce` verbatim, under a `forceT` that copies a dense view whole and fills any other row by row, and a wrapper `force`, all three INLINE, as at C3, or `genericForce` and `force` INLINABLE, as at the tip; `sumForce` sums the forced array by the benchmark's `sumVec` loop.

```haskell
{-# LANGUAGE BangPatterns, CPP #-}
-- Everything exported, as orthotope's Data.Array.Internal exports everything.
module Lib (module Lib) where

import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Generic.Mutable as VGM
import qualified Data.Vector.Storable as VS

-- A view: shape, strides, offset, vector; an array: its shape and view.
data T = T ![Int] ![Int] !Int !(VS.Vector Double)
data A = A ![Int] !T

-- Orthotope's genericForce: the vector copied once into a new one.
#if defined(INL)
{-# INLINE genericForce #-}
#else
{-# INLINABLE genericForce #-}
#endif
genericForce :: VG.Vector w a => w a -> w a
genericForce v = VG.create $ do
  out <- VGM.unsafeNew (VG.length v)
  VG.unsafeCopy out v
  return out

-- A strided view of rank 2 filled into a new vector, row by row.
{-# INLINE fillStrided #-}
fillStrided :: Int -> Int -> Int -> Int -> Int -> VS.Vector Double
            -> VS.Vector Double
fillStrided n0 s0 n1 s1 o v = VG.create $ do
  out <- VGM.unsafeNew (n0 * n1)
  let row !i !q | i >= n0 = return ()
                | otherwise = col i 0 q
      col !i !j !p
        | j >= n1 = row (i + 1) (o + (i + 1) * s0)
        | otherwise = do
            VGM.unsafeWrite out (i * n1 + j) (VS.unsafeIndex v p)
            col i (j + 1) (p + s1)
  row 0 o
  return out

-- forceT's shape: a dense view copied whole, any other filled.
{-# INLINE forceT #-}
forceT :: [Int] -> T -> T
forceT sh (T _ ss o v) = case (sh, ss) of
  ([n0, n1], [s0, s1])
    | s1 == 1 && s0 == n1 ->
        T sh [n1, 1] 0 (genericForce (VS.unsafeSlice o (n0 * n1) v))
    | otherwise -> T sh [n1, 1] 0 (fillStrided n0 s0 n1 s1 o v)
  _ -> error "forceT: violated contract: not of rank 2"

-- The wrapper modules' force.
#if defined(INL)
{-# INLINE force #-}
#else
{-# INLINABLE force #-}
#endif
force :: A -> A
force (A sh t) = A sh (forceT sh t)
```

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import Lib
import qualified Data.Vector.Storable as VS
import System.Environment (getArgs)

-- Opaque, so that each iteration forces anew.
{-# OPAQUE pass #-}
pass :: Int -> a -> a
pass _ x = x

-- The benchmark's summed reading: every component of the result summed.
{-# INLINE sumVec #-}
sumVec :: VS.Vector Double -> Double
sumVec v = go 0 0
  where
    !len = VS.length v
    go !i !acc | i >= len = acc
               | otherwise = go (i + 1) (acc + VS.unsafeIndex v i)

{-# NOINLINE sumForce #-}
sumForce :: A -> Double
sumForce a = case force a of
  A sh (T _ st o v) -> fromIntegral (sum sh + sum st + o) + sumVec v

main :: IO ()
main = do
  [ks, repss] <- getArgs
  let k = read ks :: Int
      reps = read repss :: Int
      arr = A [k, 1] (T [k, 1] [1, 1] 0 (VS.generate k fromIntegral))
      loop :: Int -> Double -> Double
      loop 0 !acc = acc
      loop r !acc = loop (r - 1) (acc + sumForce (pass r arr))
  print (loop reps 0)
```

`inline`, `Main.dump-simpl`: `$wsumForce` holds the copy, `case copyAddrToAddrNonOverlapping# (plusAddr# ww3 (*# ww2 8#)) unbx1 x3 ipv of wild16`, inside `runRW#`, and continues there with the summing, its sum loop stepping by `jump $wgo (+# ww7 1#) (+## ww8 ipv3)`; the strided fill's branch holds a second copy of the loop, stepping by `jump $wgo (+# ww7 1#) (+## ww8 ipv8)`, and `Main` has no top-level `$w$j`; `Lib` has no `$wforce`. `inlinable`: `$wsumForce` calls `case $wforce ww4 ww5 ww2 ww6 of { (# ww7, ww8, ww9, ww10, ww11, ww12, ww13 #) ->` and sums the fields; it has no copy.

By `measure.sh 1000000 50` (50 and 100 summed forcings of 1000000 elements differenced): `inline` and `inlinable` both 5.76 instructions and 8.00 bytes an element; by `measure.sh 100000 200`, 5.78 and 5.78. Summing by `VS.foldl'` instead gave 6.76 in both.

A second repro (`~/r/horde-ad/dist-inlcat/cases/O18-force-chain-all-inline`, variants `tip` (`genericForce` and the wrapper `force` INLINABLE) and `c8` (all INLINE), both with `-ddump-asm`; `run` is `Storable 200000 10`; `measure.sh KIND K N`): the first repro's `force` chain made generic in the vector type, a summing function per element type, NOINLINE, summing a forced dense array of `K` Doubles.

```haskell
{-# LANGUAGE BangPatterns, CPP, FlexibleContexts #-}
-- The first repro's force chain, generic in the vector type as orthotope's.
module Lib (module Lib) where

import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Generic.Mutable as VGM

-- A view: shape, strides, offset, vector; an array: its shape and view.
data T v = T ![Int] ![Int] !Int !(v Double)
data A v = A ![Int] !(T v)

-- genericForce and the wrappers' force: INLINE in C8 (-DINL), INLINABLE at
-- the tip; forceT INLINE in both.
#if defined(INL)
{-# INLINE genericForce #-}
#else
{-# INLINABLE genericForce #-}
#endif
genericForce :: VG.Vector w a => w a -> w a
genericForce v = VG.create $ do
  out <- VGM.unsafeNew (VG.length v)
  VG.unsafeCopy out v
  return out

-- A strided view of rank 2 filled into a new vector, row by row.
{-# INLINE fillStrided #-}
fillStrided :: VG.Vector v Double
            => Int -> Int -> Int -> Int -> Int -> v Double -> v Double
fillStrided n0 s0 n1 s1 o v = VG.create $ do
  out <- VGM.unsafeNew (n0 * n1)
  let row !i !q | i >= n0 = return ()
                | otherwise = col i 0 q
      col !i !j !p
        | j >= n1 = row (i + 1) (o + (i + 1) * s0)
        | otherwise = do
            VGM.unsafeWrite out (i * n1 + j) (VG.unsafeIndex v p)
            col i (j + 1) (p + s1)
  row 0 o
  return out

{-# INLINE forceT #-}
forceT :: VG.Vector v Double => [Int] -> T v -> T v
forceT sh (T _ ss o v) = case (sh, ss) of
  ([n0, n1], [s0, s1])
    | s1 == 1 && s0 == n1 ->
        T sh [n1, 1] 0 (genericForce (VG.unsafeSlice o (n0 * n1) v))
    | otherwise -> T sh [n1, 1] 0 (fillStrided n0 s0 n1 s1 o v)
  _ -> error "forceT: violated contract: not of rank 2"

#if defined(INL)
{-# INLINE force #-}
#else
{-# INLINABLE force #-}
#endif
force :: VG.Vector v Double => A v -> A v
force (A sh t) = A sh (forceT sh t)
```

```haskell
{-# LANGUAGE BangPatterns, FlexibleContexts #-}
module Main (main) where

import Lib
import qualified Data.Vector as V
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Storable as VS
import qualified Data.Vector.Unboxed as VU
import System.Environment (getArgs)

-- Opaque, so that each iteration forces anew.
{-# OPAQUE pass #-}
pass :: Int -> a -> a
pass _ x = x

-- The benchmark's summed reading: every component of the result summed.
{-# INLINE sumVec #-}
sumVec :: VG.Vector v Double => v Double -> Double
sumVec v = go 0 0
  where
    !len = VG.length v
    go !i !acc | i >= len = acc
               | otherwise = go (i + 1) (acc + VG.unsafeIndex v i)

{-# INLINE sumForce #-}
sumForce :: VG.Vector v Double => A v -> Double
sumForce a = case force a of
  A sh (T _ st o v) -> fromIntegral (sum sh + sum st + o) + sumVec v

{-# NOINLINE sumForceS #-}
sumForceS :: A VS.Vector -> Double
sumForceS = sumForce
{-# NOINLINE sumForceU #-}
sumForceU :: A VU.Vector -> Double
sumForceU = sumForce
{-# NOINLINE sumForceB #-}
sumForceB :: A V.Vector -> Double
sumForceB = sumForce

main :: IO ()
main = do
  [kind, ks, repss] <- getArgs
  let k = read ks :: Int
      reps = read repss :: Int
      mk :: VG.Vector v Double => (A v -> Double) -> Double
      mk f = let arr = A [k, 1] (T [k, 1] [1, 1] 0 (VG.generate k fromIntegral))
                 loop :: Int -> Double -> Double
                 loop 0 !acc = acc
                 loop r !acc = loop (r - 1) (acc + f (pass r arr))
             in loop reps 0
  print $ case kind of
    "Storable" -> mk sumForceS
    "Unboxed" -> mk sumForceU
    _ -> mk sumForceB
```

`Main.dump-simpl`: `tip`'s summing functions call the specialised `force` workers `$w$s$wforce`, `c8`'s hold the chain inlined, the Unboxed sum indexing the forced copy from 0, `indexDoubleArray# arr'# ww of`. `Main.dump-asm`, whitespace collapsed: the Storable sum loop keeps base and limit in registers in both, 5 instructions an element, `movsd (%rdx,%rsi,8),%xmm1 addsd %xmm1,%xmm0 incq %rsi` in `tip` and `movsd (%rsi,%rax,8),%xmm1 addsd %xmm1,%xmm0 incq %rax` in `c8`; the Unboxed one adds the offset at every element in `tip`, `movq %rcx,%r9 addq %rbx,%r9 addsd 16(%rsi,%r9,8),%xmm0 incq %rbx`, 6 instructions, and not in `c8`, `addsd 16(%rdx,%rsi,8),%xmm0 incq %rsi`, 4; the boxed one, through a return point at each element, runs 26 instructions in `tip`, eight loads from the Haskell stack, the offset added and five stores, and 29 in `c8`, six loads and no offset added but five moves through the C-stack slot `192(%rsp)` and six stores. By `measure.sh KIND 200000 20`, twice alike: Storable 5.77 instructions an element in both, Unboxed 6.77 under `tip` and 4.77 under `c8`, boxed 29.27 and 32.27, every one 8.00 to 8.01 bytes an element.

A third repro (`~/r/horde-ad/dist-inlcat/cases/O18-route-force`, variants `inline` (`-DINL`) and `inlinable`, both with `-ddump-asm`, and `ra`, `inline` with `-ddump-asm-liveness -ddump-asm-regalloc`; `run` is `100000 100`; `measure.sh K N`): the first repro's `genericForce` and `force` under orthotope's `forceT` shape, `VS.empty` for an empty array and otherwise `routeT`, its merge loop `canonicalizeT` out of line, choosing `genericForce (wholeOrSliceT ao n v)` or a strided fill; the strides are given as the shape, so that no call computes them.

```haskell
{-# LANGUAGE BangPatterns, CPP #-}
module Lib (module Lib) where

import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Generic.Mutable as VGM
import qualified Data.Vector.Storable as VS

data T = T ![Int] ![Int] !Int !(VS.Vector Double)
data A = A ![Int] !T

data Axes = Axes !Int !Int [(Int, Int)]
data Route = RSlice !Int !Int | RFill Axes !Int !Int

#if defined(INL)
{-# INLINE genericForce #-}
#else
{-# INLINABLE genericForce #-}
#endif
genericForce :: VG.Vector w a => w a -> w a
genericForce v = VG.create $ do
  out <- VGM.unsafeNew (VG.length v)
  VG.unsafeCopy out v
  return out

canonicalizeT :: [Int] -> [Int] -> Axes -> Axes
canonicalizeT (_ : sts) (1 : ns) !axes = canonicalizeT sts ns axes
canonicalizeT (st : sts) (n : ns) (Axes stHead nHead rest)
  | stHead == n * st = canonicalizeT sts ns (Axes st (nHead * n) rest)
  | nHead == 1 = canonicalizeT sts ns (Axes st n rest)
  | otherwise = canonicalizeT sts ns (Axes st n ((stHead, nHead) : rest))
canonicalizeT _ _ axes = axes

{-# INLINE routeOfT #-}
routeOfT :: Int -> Int -> Axes -> Route
routeOfT ao l axes@(Axes st _ rest)
  | st == 1 && null rest = RSlice ao l
  | otherwise = RFill axes ao l

{-# INLINE routeT #-}
routeT :: [Int] -> Int -> T -> Route
routeT _ 1 (T _ _ ao _) = RSlice ao 1
routeT (n : ns) l (T _ (st : sts) ao _) =
  routeOfT ao l (canonicalizeT sts ns (Axes st n []))
routeT _ _ _ = error "routeT: violated contract"

{-# INLINE wholeOrSliceT #-}
wholeOrSliceT :: Int -> Int -> VS.Vector Double -> VS.Vector Double
wholeOrSliceT ao l v
  | ao == 0 && VS.length v == l = v
  | otherwise = VS.unsafeSlice ao l v

{-# INLINE fillRoute #-}
fillRoute :: VS.Vector Double -> Axes -> Int -> Int -> VS.Vector Double
fillRoute v (Axes st n rest) ao l = VG.create $ do
  out <- VGM.unsafeNew l
  let outer = product (map snd rest)
      os = case rest of { (s, _) : _ -> s; [] -> 0 }
      row !i | i >= outer = return ()
             | otherwise = col i 0
      col !i !j
        | j >= n = row (i + 1)
        | otherwise = do
            VGM.unsafeWrite out (i * n + j) (VS.unsafeIndex v (ao + i * os + j * st))
            col i (j + 1)
  row 0
  return out

{-# INLINE forceT #-}
forceT :: [Int] -> T -> T
forceT sh t@(T _ _ _ v) = T sh sh 0 $
  if l == 0
  then VS.empty
  else case routeT sh l t of
    RSlice ao n -> genericForce (wholeOrSliceT ao n v)
    RFill axes ao n -> fillRoute v axes ao n
  where !l = product sh

#if defined(INL)
{-# INLINE force #-}
#else
{-# INLINABLE force #-}
#endif
force :: A -> A
force (A sh t) = A sh (forceT sh t)
```

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import Lib
import qualified Data.Vector.Storable as VS
import System.Environment (getArgs)

{-# OPAQUE pass #-}
pass :: Int -> a -> a
pass _ x = x

{-# INLINE sumVec #-}
sumVec :: VS.Vector Double -> Double
sumVec v = go 0 0
  where
    !len = VS.length v
    go !i !acc | i >= len = acc
               | otherwise = go (i + 1) (acc + VS.unsafeIndex v i)

{-# NOINLINE sumForce #-}
sumForce :: A -> Double
sumForce a = case force a of
  A sh (T _ st o v) -> let !s = sumVec v in fromIntegral (sum sh + sum st + o) + s

main :: IO ()
main = do
  [ks, repss] <- getArgs
  let k = read ks :: Int
      reps = read repss :: Int
      arr = A [k, 1] (T [k, 1] [1, 1] 0 (VS.generate k fromIntegral))
      loop :: Int -> Double -> Double
      loop 0 !acc = acc
      loop r !acc = loop (r - 1) (acc + sumForce (pass r arr))
  print (loop reps 0)
```

`Main.dump-asm`, whitespace collapsed: under `inline` the copy route's sum loop runs 7 instructions an element, loading its address and bound from the C stack, `movq 80(%rsp),%rcx movsd (%rcx,%rax,8),%xmm1 addsd %xmm1,%xmm0 incq %rax` and `movq 72(%rsp),%rbx cmpq %rbx,%rax`; under `inlinable` it keeps both in registers, `movsd (%rbx,%rdi,8),%xmm1 addsd %xmm1,%xmm0 incq %rdi`. `ra`'s `Main.dump-asm-regalloc` writes the slots just before the copy, `movq %r9,88(%rsp) movq %rcx,80(%rsp) movq %r8,%r14 call memcpy addq $8,%rsp`, `%rsp` 8 lower inside the call's frame, and goes straight to the loop, `.Lc4Xh: movq 72(%rsp),%rbx cmpq %rbx,%rax jl .Lc4Xp jmp .Lc4Xo .Lc4Xp: movq 80(%rsp),%rcx movsd (%rcx,%rax,8),%xmm1`; in its `Main.dump-asm-liveness` the address and the bound are born before the call, `leaq 16(%rbx),%vI_t4Mb` and `movq 56(%rbp),%vI_t4M1`, and no instruction between the call and the loop uses either. By `measure.sh 1000000 50`, twice alike:

```
inline: 7.76 instructions, 8.00 bytes an element
inlinable: 5.76 instructions, 8.00 bytes an element
```

By `measure.sh 100000 200`, 7.79 and 5.79. With the strides computed by a call, `drop 1 (scanr (*) 1 sh)` (`~/r/horde-ad/dist-inlcat/cases/O18-route-force/tried/Lib-scanr-strides.hs`), both run 5.76 instructions an element, the block after the copy calling `scanr` and `$wunsafeDrop` and the loop preceded by a return point. A fourth repro (`~/r/horde-ad/dist-inlcat/cases/O18-fromVectorT`, variants `inline` and `inlinable`) is the third repro with an INLINE `fromVectorT sh = T sh (tail $ getStridesT sh) 0`, orthotope's with the case's shape field, around the same `forceT`, `forceT sh t@(T _ _ _ v) = fromVectorT sh $` in place of `T sh sh 0 $`, and the strides computed out of line by a recursive `getStridesT [] = [1]; getStridesT (s : ss) = case getStridesT ss of { r@(m : _) -> let !x = s * m in x : r; [] -> [] }`; that call does not fall between the copy and the loop, and the figures are the third repro's, 7.76 against 5.76 by `measure.sh 1000000 50`, the `inline` loop `movq 80(%rsp),%rbx movsd (%rbx,%rax,8),%xmm1 addsd %xmm1,%xmm0 incq %rax` after `movq %r10,88(%rsp) movq %r8,80(%rsp) movq %rcx,72(%rsp) movq %r9,%r14 call memcpy addq $8,%rsp`.

**Reproduces small:** in part: the Storable reloads, yes, by the third and fourth repros, 7.76 instructions an element under INLINE against 5.76 under INLINABLE once no call sits between the copy and the sum loop, and 5.76 under both with the strides computed by a call; the first repro inlines the copy into the summing function as C3 does, and copies the sum loop into both of `forceT`'s branches inside the summing worker, where C3 has four copies of it there, yet costs nothing, INLINABLE running the same instructions an element, and the second keeps base and limit in registers under either set of pragmas. The Unboxed offset dropped under C8's pragmas, yes (second repro), 2 instructions an element, where C8's binary saves 1, its limit reloaded from the C stack. The boxed move, no, reversed: C8's pragmas cost the second repro 3 instructions an element, where they save orthotope 10. Not tried: the `vUnsafeFillStrided` fill, and an orthotope build of `OpsDynamic` with `-ddump-asm-liveness -ddump-asm-regalloc`.

### O19. A local recursive function eta-expanded only after its call became a case scrutinee is no join point, so a loop inlined into a non-tail position can become a heap closure allocated each call, as `sumT`'s odometer walk does where `sumA` is inlined

**Rule.** The occurrence analyser makes a recursive group join points only if every occurrence of each binder is a tail call passing as many arguments as its right-hand side has leading lambdas: the tail calls by `okForJoinPoint` ([compiler/GHC/Core/Opt/OccurAnal.hs#L4176][g434], its guard `AlwaysTailCalled arity <- tail_call_info` at [#L4189][g435]), applied to a group by `decideRecJoinPointHood` ([#L4168][g436]), and the count by `tagRecBinders` (`adjustTailUsage`, [#L4057][g437]), as Note [Join arity prediction based on joinRhsArity] says ([#L871][g438]; [#L832][g439]: for a recursive group the two arities must be equal, and neither GHC nor the join points paper eta-expands to make them so); Note [Invariants on join points] ([compiler/GHC/Core.hs#L964][g440]), invariant 1. `occAnal` of a `Case` marks every occurrence in its scrutinee non-tail ([compiler/GHC/Core/Opt/OccurAnal.hs#L2688][g441]). The simplifier floats a non-join `letrec` out of a case scrutinee, simplifying its body with the case as continuation (`simplRecE`, [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L2040][g442]), so that the call becomes the scrutinee; a join point there instead takes the case into its right-hand side (`simplJoinPointBind`, [#L2097][g443]). `sumT`'s walk qualifies only once its left fold, a right fold passing the accumulator to a continuation, is eta-expanded: until Call Arity, `block` has two lambdas against three arguments at its call and its recursive call sits inside `go1`, itself no join point. Inlined into the row's loop, Float inwards sinks the `letrec` into the `case` scrutinee, where its call is the tail of its body, but the arities still differ there; the Simplifier after Call Arity eta-expands it while floating it out again, and from then on its call is a scrutinee, so it stays a `letrec`, which STG allocates as a closure of its free variables. As the whole body of an out-of-line function, the eta-expanded walk's call is a tail call, and it ends a `joinrec`, which STG compiles as `let-no-escape`, allocating nothing. No pass of the working tree moves a `case` into a function's returns to make a join point (the one Core-level mention of loopification, [compiler/GHC/Core.hs#L1167][g444] in Note [The polymorphism rule of join points], points to GHC [#14068](https://gitlab.haskell.org/ghc/ghc/-/work_items/14068)). Why INLINABLE leaves `sumA` out of line: `sumA`'s body, with the INLINE `sumT` inlined into it at the known instance, is big, so worker/wrapper splits it, and the wrapper inlines no earlier than phase 2 (`mkStrWrapperInlinePrag`, [compiler/GHC/Core/Opt/WorkWrap.hs#L902][g187], Note [Wrapper activation], [#L452][g188]); the specialiser, which runs before that, specialises the wrapper and the INLINABLE worker `$wsumA`, and a specialisation of a function other than a dictionary function keeps a stable unfolding only when its guidance is `UnfWhen` (`specUnfolding`, [compiler/GHC/Core/Unfold/Make.hs#L205][g445]; Note [Inline specialisations], [compiler/GHC/Core/Opt/Specialise.hs#L2413][g446]), so `$s$wsumA` has none, is split again into `$w$s$wsumA`, and is called. No patch of the working tree bears on it.

**Seen.** V2a (`sumA` INLINABLE in every module defining it but ShapedG) against C8, Dynamic Storable `rerank 1 (\ r -> scalar (sumA r))`: in C8, `sumA` and `sumT` inlined into the per-subarray function `$weta3`, whose sum is then stored in a one-element array, `sumT`'s odometer walk has a recursive `$wblock :: Int# -> Odometer -> Double# -> Double#` whose one outside call is a `case` scrutinee, `letrec`-bound, a closure of four free variables, 40 bytes a subarray on the views whose subarrays are not contiguous (120 bytes a call at `[3, 3]`, 0.08 an element at `[400, 500]`); in V2a, `$weta8` calls the specialised worker `$w$s$wsumA2`, where `$wblock` is a `joinrec`.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/O19-sum-inlined-scrutinee-closure`, variants `inline` (`-DINL`, `sumA` INLINE), `inlinable` (`sumA` INLINABLE), `tail` (`-DINL -DTAIL`, `sumA` INLINE and inlined as the whole body of a NOINLINE `rowSum`) `passes` (`inline` with `-dverbose-core2core`) and `inlinable-check` (`inlinable` with `-dinline-check sumA -ddump-rule-firings`); `measure.sh N` gives instructions and bytes a call of `rowSums`, three rows, on each view, from N and 2N iterations): orthotope's `sumT`, its odometer walk copied, over a class of vectors with a Storable `sumA` where the instance is known, summing each row of a `[3, 3]` array, transposed so that each row is strided or dense so that each is a slice, each row passed through an OPAQUE function so that nothing about its view is known, as orthotope's route computed for each subarray leaves it.

```haskell
{-# LANGUAGE BangPatterns, CPP, ScopedTypeVariables #-}
-- orthotope's sumT over its routes (Data/Array/Internal.hs at "Condense the
-- account of unorderedRouteT's sort and merge"), cut to two routes, one slice
-- where the view is contiguous and its elements by the odometer walk where it
-- is not, and its two layers: the generic code over a class of vectors, and a
-- wrapper at Storable vectors (DynamicS), where the instance is known.
module Lib (T (..), A (..), sumA) where

import qualified Data.Vector.Storable as V

class Vec v where
  vSum :: (V.Storable a, Num a) => v a -> a
  vIndex :: V.Storable a => v a -> Int -> a
  vSlice :: V.Storable a => Int -> Int -> v a -> v a

instance Vec V.Vector where
  vSum = V.sum
  vIndex = V.unsafeIndex
  vSlice = V.unsafeSlice

data Axis = Axis !Int !Int  -- stride and extent

-- A view: strides, offset, vector; the Storable array: shape and view.
data T v a = T ![Int] !Int !(v a)
data A a = A ![Int] !(T V.Vector a)

data Route = RSlice !Int !Int | RFill !Axis [Axis] !Int
  -- RFill: the innermost axis, the axes outside it innermost first, offset

{-# INLINE routeT #-}
routeT :: [Int] -> Int -> T v a -> Route
routeT sh l (T sts o _)
  | and (zipWith (==) sts (tail (scanr (*) 1 sh))) = RSlice o l
  | otherwise = case reverse (zipWith Axis sts sh) of
      inner : above -> RFill inner above o
      [] -> RSlice o 1

-- orthotope's odometer, its step and its walk, as at "Condense the account of
-- unorderedRouteT's sort and merge".
data Odometer = OdoLevel !Int !Int !Axis !Odometer | OdoDone

stepOdometer :: Odometer -> Odometer
stepOdometer OdoDone = OdoDone
stepOdometer (OdoLevel o c axis@(Axis s d) outer)
  | c > 1 = OdoLevel (o + s) (c - 1) axis outer
  | otherwise = case stepOdometer outer of
      OdoDone -> OdoDone
      next@(OdoLevel oNext _ _ _) -> OdoLevel oNext d axis next

{-# INLINE offsetsT #-}
offsetsT :: forall b. Axis -> [Axis] -> Int -> (Int -> b -> b) -> b -> b
offsetsT (Axis sk dk) above !start step nil =
  let block :: Int -> Odometer -> b
      block o outer =
        let go :: Int -> Int -> b
            go !i !p
              | i < dk = step p (go (i + 1) (p + sk))
              | otherwise = case stepOdometer outer of
                  OdoDone -> nil
                  next@(OdoLevel oNext _ _ _) -> block oNext next
        in  go 0 o
  in  block start
            (foldr (\axis@(Axis _ d) outer -> OdoLevel start d axis outer)
                   OdoDone above)

{-# INLINE routeFoldT #-}
routeFoldT :: (Vec v, V.Storable a)
           => v a -> Route -> (v a -> b -> b) -> (a -> b -> b) -> b -> b
routeFoldT v route onSlice onElem nil = case route of
  RFill axis above o ->
    offsetsT axis above o (\p rest -> onElem (vIndex v p) rest) nil
  RSlice o l -> onSlice (vSlice o l v) nil

-- orthotope's: a strict left fold from 0 over the parts, by a right fold
-- passing the accumulator to its continuation.
{-# INLINE sumT #-}
sumT :: (Vec v, V.Storable a, Num a) => [Int] -> T v a -> a
sumT sh t@(T _ _ v)
  | l == 0 = 0
  | otherwise = routeFoldT v (routeT sh l t)
      (\ s k !acc -> k (acc + vSum s)) (\ x k !acc -> k (acc + x)) id 0
  where !l = product sh

#if defined(INL)
{-# INLINE sumA #-}
#else
{-# INLINABLE sumA #-}
#endif
sumA :: (V.Storable a, Num a) => A a -> a
sumA (A sh t) = sumT sh t
```

```haskell
{-# LANGUAGE BangPatterns, CPP #-}
module Main (main) where

import qualified Data.Vector.Storable as V
import Lib
import System.Environment (getArgs)

-- Opaque, so that nothing about a view is known where it is summed, as
-- orthotope's route, computed for each subarray, leaves it.
{-# OPAQUE pass #-}
pass :: Int -> A Double -> A Double
pass _ x = x

-- orthotope's rerank 1 (\ r -> scalar (sumA r)) at a rank-2 array: the sum
-- of each row, stored in the result, so that the sum is a case scrutinee.
rowSums :: Int -> A Double -> V.Vector Double
rowSums k (A (m : ish) (T (s : ists) o v)) =
  V.generate m (\ i -> rowSum (pass k (A ish (T ists (o + i * s) v))))
rowSums _ _ = error "rowSums: rank 0"

#if defined(TAIL)
-- The control: the sum is the whole body of an out-of-line function.
{-# NOINLINE rowSum #-}
#else
{-# INLINE rowSum #-}
#endif
rowSum :: A Double -> Double
rowSum r = sumA r

main :: IO ()
main = do
  [view, ns] <- getArgs
  let n = read ns :: Int
      v = V.generate 9 fromIntegral :: V.Vector Double
      -- [3, 3]: transposed, each row strided, or dense, each row a slice.
      a | view == "strided" = A [3, 3] (T [1, 3] 0 v)
        | otherwise = A [3, 3] (T [3, 1] 0 v)
      go :: Int -> Double -> Double
      go 0 !acc = acc
      go k !acc = go (k - 1) (acc + V.sum (rowSums k (pass k a)))
  print (go n 0)
```

`Main.dump-simpl`, whitespace collapsed. `inline`, in the row loop:

```
letrec { $wblock = \ ww5 outer ww6 ->
case $wblock bx1 (go1 above) 0.0## of ww5 { __DEFAULT -> jump $j2 ww5 }
```

`inlinable`, the row loop calling `case $w$s$wsumA ww5 ww7 ww8 ww11 ww12`, and in that worker `joinrec { $wblock ww8 outer ww9 =` entered by `jump $wblock ww2 (go1 above) 0.0##`; `tail` the same in `$wrowSum`, `joinrec { $wblock ww7 outer ww8 =`. `Main.dump-stg-final`: `inline` `let { Rec { $wblock = \r [ww5 outer ww6]`, a heap closure; `inlinable` `let-no-escape { Rec { $wblock = \j [ww8 outer ww9]` and `tail` `let-no-escape { Rec { $wblock = \j [ww7 outer ww8]`. `passes`, `Main.dump-call-arity`, the `letrec` inside the scrutinee with two lambdas, called with three arguments, the third the floated accumulator `lvl`:

```
case letrec { block = \ o outer -> let { lvl = stepOdometer outer } in letrec { go1 = \ i p ->
} in block start (letrec {
go1 above) lvl of
```

`inlinable-check`: `build.log` has `Inactive unfolding: sumA`, and `Main.dump-rule-firings` has `Rule fired: SPEC/Main $wsumA @Double (Main)`.

`measure.sh 1000000`:

```
inline strided: 2069.4 instructions, 1376.0 bytes a call
inline dense: 1322.8 instructions, 800.0 bytes a call
inlinable strided: 1998.2 instructions, 1256.0 bytes a call
inlinable dense: 1283.8 instructions, 800.0 bytes a call
tail strided: 1998.2 instructions, 1256.0 bytes a call
tail dense: 1283.8 instructions, 800.0 bytes a call
```

The closure costs 40 bytes a row on the strided view, orthotope's figure, its four free variables the inner axis's stride and extent, the vector's address and the contents its `touch#` keeps alive. On the dense view the slice's sum is vector-stream's `foldlM'_loop`, whose right-hand side has a lambda for each of its three arguments from the start: in `passes` it is a `joinrec` from an early Simplifier on, and no byte moves. `tail` runs the instructions of `inlinable` to the decimal: the call's position decides, not the pragma.

**Reproduces small:** yes, the closure where the inlined walk's call is a case scrutinee and the `joinrec` where it is a function's tail, under INLINE in a NOINLINE caller as under INLINABLE; the model's routes are `RSlice` and `RFill` only, and its row is summed into a vector rather than stored as a scalar array.

### O20. A function inlined where its result is scrutinised jumps from every exit to the continuation, a top-level function after FloatOut; out of line it is a non-tail call, a few instructions a call more; inlined, a boxed result built at the loop exit puts a heap check in every iteration

**Rule.** Inlined where its result is scrutinised (`case f x of r -> K`, orthotope's `scalar (sumA r)`), a function's every exit, each loop exit included, jumps to `K`: case-of-case binds the alternative as a join point and the inlined body's exits jump to it (`mkDupableContWithDmds`, its `Select` case, [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4250][g447], and `mkDupableAlt`, [#L4322][g448]), and the late FloatOut floats that non-recursive join point to the top level, where it stops being a join point (Note [Floating join point bindings], [compiler/GHC/Core/Opt/SetLevels.hs#L871][g406], "float them to the top in the second invocation of FloatOut"; [#L1880][g449]), so each exit is a tail call of a top-level function. Called out of line, here the specialised worker of an INLINABLE function too big to inline (`tryUnfolding`, [compiler/GHC/Core/Opt/Simplify/Inline.hs#L302][g450], `small_enough` at [#L338][g222]), the same call is a case scrutinee, so the code generator pushes a return point before the call (`cgCase`, `withSequel sequel (cgExpr scrut)`, [compiler/GHC/StgToCmm/Expr.hs#L619][g451]): the caller runs its own stack check and pushes the return address, 6 instructions where the inlined form spends 3, the top-level continuation's stack check, and 2 more where the callee takes a sixth argument, which arrives on the stack and is moved down a slot to make room for the return address. A second effect where the result is boxed: inlined into a thunk that returns the boxed sum, the loop's exit allocates the box, and a case on a comparison primop puts no heap check in its alternatives (`NoGcInAlts`, `cgCase`, [#L608][g452], Note [GC for conditionals], [#L629][g453]) but adds their allocation to the heap check at the entry of the loop's join point (`cgLetNoEscapeClosure`, [#L212][g454], its `noEscapeHeapCheck`, [#L217][g455]), so every iteration checks the heap and moves the heap pointer back (`adjustHpBackwards`, [compiler/GHC/StgToCmm/Layout.hs#L143][g456], from `emitEnter`, [compiler/GHC/StgToCmm/Expr.hs#L1190][g457]), 4 instructions, the case Note [Compiling case expressions] ([#L225][g458]) names: "May put a heap-check into the inner loop ... Q is the loop exit, and only it does allocation"; out of line, the worker returns `Double#` (CPR), its loop allocates nothing and has no heap check, and the box is built once after the return.

At boxed vectors the sum is the element of a lazy one-element vector, so `singleton (sumA r)` let-binds it as a thunk, and the inlined walk is that thunk's whole body: its call is a tail call there, and once Call Arity has eta-expanded it the occurrence analyser makes the group a join point (O19's rule), allocating nothing. Out of line, the thunk calls the specialised worker, which keeps no unfolding (`specUnfolding`, [compiler/GHC/Core/Unfold/Make.hs#L205][g445]), and boxes the `Double` it is returned unboxed, where the inlined walk's exit boxes it in place; both allocate the thunk and the box, so the call costs instructions alone (second repro).

**Seen.** V2a (`sumA` INLINABLE in every module defining it but ShapedG) against C8 (INLINE), the row `rerank 1 (\ r -> scalar (sumA r))`: C8's per-subarray worker `$weta3` has `sumA` and `sumT` inlined, its loop exits calling the top-level `$j11`, the scalar's construction (`1# -> $j11 ww10`, C8's `OpsDynamic.dump-simpl`); V2a's `$weta8` has `case OpsDynamic.$w$s$wsumA2 ww6 ww7 ww2 ww3 ww4 ww5 of ww8 { __DEFAULT -> ghc-internal:GHC.Internal.Magic.runRW# ...`. Counted again here with the two binaries, `--summed --iters` at N and 2N: Storable Dynamic `rerank` small dense 3454.1 instructions a call in C8 and 3466.1 in V2a, 12 a call, 4 a subarray; boxed small strided 4271.3 and 4288.9, 17.6 a call, and small scaled the same, 5.9 a subarray; boxed large strided 2402 a call more over 400 subarrays, 6.0 a subarray; boxed large dense 5549538.5 against 4751940.8, 3.99 an element fewer out of line, which with the call's cost gives the 18 a call fewer V2a runs at boxed small dense. In V2a's binary `$weta8` is `lea -0x8(%rbp),%rax; cmp %r15,%rax; jb ...; mov 0x0(%rbp),%rax; movq $0x189b1e8,0x0(%rbp); mov %rax,-0x8(%rbp); add $0xfffffffffffffff8,%rbp; jmp 1891200 <..._OpsDynamic_zdwzdszdwsumA2_info>` (0x189b190 to 0x189b1ad). C8's boxed dense loop (0x1352cf4 to 0x1352d5c, its hottest addresses under `perf record`) does `add $0x10,%r12; cmp 0x358(%r13),%r12; ja` before the bound test and `add $0xfffffffffffffff0,%r12` after the element load, every element; V2a's, in `$w$s$wsumA` (0x1815378 to 0x18153d7), has neither. At boxed vectors: in C8's `OpsDynamic.dump-simpl`, the boxed per-subarray function `$weta1` let-binds the sum, `x2 :: Double`, writes it into a one-element `newArray#`, and the thunk's body holds `joinrec { $wblock :: Int# -> I.Odometer -> Double# -> Double` whose exit is `I.OdoDone -> ghc-internal:GHC.Internal.Types.D# ww8`; in V2a's `$weta7` has no `$wblock`, its thunk `x2` being `case OpsDynamic.$w$s$wsumA ww ww2 ww3 ww7 ww8 ww9 of ww10`, six arguments where the model's worker takes five, and the walk is in `OpsDynamic.$w$s$wsumA`, of type `IU.ShapeL -> [Int] -> Int# -> Int# -> Int# -> Array# Double -> Double#`, a `joinrec` there too. Orthotope's comment at `sumA` ("Leave sumA out of line where inlining it costs a closure") records that with `sumA` INLINE the benchmark "ran Shaped Unboxed rerank of [400, 500] 1.5 times the instructions on contiguous views", which fits this rule's heap check, not measured as such.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/O20-sum-out-of-line-non-tail-call`, variants `inline` (`-DINL`, `sumT` INLINE) and `inlinable` at Storable vectors, `inline-boxed` and `inlinable-boxed` (`-DBOXED`) at boxed ones, and `check`, `inlinable` with `-ddump-spec` and `-dinline-check $w$s$wsumT`; `measure.sh N VIEW ROWS COLS` gives instructions and bytes a call of `row` and instructions a row from N and 2N iterations): orthotope's `sumT` reduced to a dense run summed by vector's `foldl'` and an odometer walk for any other view, behind an out-of-line axes function that takes the offset as orthotope's `absAxesAndStartT` does; the per-row function `perRow` is NOINLINE, standing in for the size that keeps orthotope's out of line in both forms (`$weta3`, `$weta8`); dense rows are contiguous, strided rows every other element.

```haskell
{-# LANGUAGE BangPatterns, CPP #-}
module Lib (T (..), sumT) where

import qualified Data.Vector.Generic as VG

-- A view, as orthotope's T: strides, offset, values.
data T v a = T ![Int] !Int !(v a)

-- The outer levels of a walk, innermost first, as orthotope's Odometer:
-- offset, positions left, stride, extent.
data Odo = Level !Int !Int !Int !Int !Odo | Done

stepOdo :: Odo -> Odo
stepOdo Done = Done
stepOdo (Level o c s d outer)
  | c > 1 = Level (o + s) (c - 1) s d outer
  | otherwise = case stepOdo outer of
      Done -> Done
      next@(Level o' _ _ _ _) -> Level o' d s d next

-- The view's axes, innermost first, those of extent 1 dropped, and its
-- start: out of line and taking the offset, as orthotope's
-- absAxesAndStartT, so that nothing of it floats out of a caller's loop.
{-# NOINLINE axesOf #-}
axesOf :: [Int] -> [Int] -> Int -> ([(Int, Int)], Int)
axesOf sh st o = (reverse [ (d, s) | (d, s) <- zip sh st, d /= 1 ], o)

-- The sum of a view: a run by vector's foldl' over its slice, any other
-- view by a walk over an odometer, as orthotope's sumT.  Every exit adds,
-- as orthotope's do, so that the specialised worker returns Double#.
#if defined(INL)
{-# INLINE sumT #-}
#else
{-# INLINABLE sumT #-}
#endif
sumT :: (VG.Vector v a, Num a) => [Int] -> T v a -> a
sumT sh (T st o v) = case axesOf sh st o of
  ([], start) -> 0 + VG.unsafeIndex v start
  ([(d, 1)], start) -> VG.foldl' (+) 0 (VG.unsafeSlice start d v)
  ((dk, sk) : above, start) ->
    let block !p outer !acc =
          let go !i !q !a
                | i < dk = go (i + 1) (q + sk) (a + VG.unsafeIndex v q)
                | otherwise = case stepOdo outer of
                    Done -> a
                    next@(Level p' _ _ _ _) -> block p' next a
          in go (0 :: Int) p acc
    in block start
             (foldr (\ (d, s) outer -> Level start d s d outer) Done above) 0
```

```haskell
{-# LANGUAGE BangPatterns, CPP #-}
module Main (main) where

import Lib
import System.Environment (getArgs)
#if defined(BOXED)
import qualified Data.Vector as VV
#else
import qualified Data.Vector.Storable as VV
#endif

-- Opaque, so that each iteration computes anew.
{-# OPAQUE pass #-}
pass :: Int -> a -> a
pass _ x = x

-- orthotope's rerank 1 at a rank-2 view: f applied to each row.
{-# INLINE rerank #-}
rerank :: ([Int] -> T v a -> b) -> [Int] -> T v a -> [b]
rerank f (n : ish) (T (s : ss) o v) =
  map (\ i -> f ish (T ss (o + i * s) v)) [0 .. n - 1]
rerank _ _ _ = error "rerank"

-- The results put together, out of line as orthotope's ravelOuter.
{-# NOINLINE ravel #-}
ravel :: [VV.Vector Double] -> VV.Vector Double
ravel = VV.concat

-- The function applied to each row, scalar (sumA r): out of line, as
-- orthotope's is in both forms by its size (its $weta3 and $weta8).
{-# NOINLINE perRow #-}
perRow :: [Int] -> T VV.Vector Double -> VV.Vector Double
perRow ish r = VV.singleton (sumT ish r)

-- The benchmark's row: rerank 1 (\ r -> scalar (sumA r)).
{-# NOINLINE row #-}
row :: [Int] -> T VV.Vector Double -> VV.Vector Double
row sh t = ravel (rerank perRow sh t)

main :: IO ()
main = do
  [view, ns, cs, iterss] <- getArgs
  let n = read ns :: Int
      c = read cs :: Int
      iters = read iterss :: Int
      -- dense: an n x c array, each row contiguous; strided: every other
      -- column of an n x 2c array, each row a walk.
      (sh, t) = case view of
        "dense" -> ([n, c], T [c, 1] 0 (VV.generate (n * c) fromIntegral))
        _ -> ([n, c], T [2 * c, 2] 0 (VV.generate (2 * n * c) fromIntegral))
      loop :: Int -> Double -> Double
      loop 0 !acc = acc
      loop k !acc = loop (k - 1) (acc + VV.sum (row sh (pass k t)))
  print (loop iters 0)
```

`Main.dump-simpl`, whitespace collapsed. `inline`, the dense loop's exit and the continuation it calls:

```
1# -> $w$j ww7
$w$j = \ ww -> runRW# (\ s -> case newAlignedPinnedByteArray# 8# 8# s of
```

`inlinable`, in `$wperRow`: `case $w$s$wsumT ish ww4 ww1 ww2 ww3 of ww5 { __DEFAULT ->`, then the same `runRW#`. `check`: `"SPEC/Main $wsumT @Vector @Double"` in `Main.dump-spec`, and in `build.log` every decision about the worker `ANSWER = NO`, the smallest at `guidance IF_ARGS [0 20 0 0 0] 423 0`.

`Main.dump-asm`, labels left out. `inlinable`, `$wperRow` whole on the path taken, against `inline`'s continuation entry, `.L$w$j_info: leaq -16(%rbp),%rax; cmpq %r15,%rax; jb ...`, reached by `jmp .L$w$j_info` from each exit:

```
leaq -16(%rbp),%rax
cmpq %r15,%rax
jb ...
movq $.Lblock_info,-8(%rbp)
addq $-8,%rbp
jmp $w$s$wsumT_info
```

`inline-boxed`'s dense loop, its exit `1# -> D# ww2` in Core, against `inlinable-boxed`'s, which loads the element and pushes the return point with no heap check between (`movq 24(%r9,%rdx,8),%rdx`, `movq $.Lblock_info,-16(%rbp)`) and has none at its header:

```
movq %rcx,80(%rsp)
movq %rdx,%rcx
movq %rsi,%rdx
movq %rbx,%rsi
movq 80(%rsp),%rbx
addq $16,%r12
cmpq 856(%r13),%r12
ja ...
cmpq %rbx,%rdx
jge ...
movq %rcx,%rsi
addq %rdx,%rsi
movq 24(%rax,%rsi,8),%rax
addq $-16,%r12
```

By `measure.sh N VIEW ROWS COLS`, instructions a row (a row is one subarray), N 200000 at 3 x 3 and 400 at 400 x 500; the bytes are equal in every pair:

```
                    inline  inlinable  inline-boxed  inlinable-boxed
dense 3x3            774.27    777.27       875.02           863.02
strided 3x3          888.19    891.19       924.12           933.61
dense 400x500       3669.41   3672.40     17710.94         14219.95
strided 400x500    14720.96  14723.96     17759.40         17768.67
```

Out of line costs 3 instructions a row at Storable, and 9.3 to 9.5 at boxed strided, at both sizes; at boxed dense 400 x 500 it saves 6.98 an element, the heap check's 4 and three moves more the inlined loop spends spilling a register through `80(%rsp)`, and at 3 x 3 the nine elements' gain outweighs the three calls' cost, 36 a call fewer.

A second repro (`~/r/horde-ad/dist-inlcat/cases/O20-boxed-sum-thunk-out-of-line-call`, variants `b-inline` (`-DBOXED -DINL`, boxed, `sumA` INLINE), `b-inlinable` (`-DBOXED`), and `s-inline` and `s-inlinable`, the Storable form; `measure.sh M N` gives instructions and bytes a call of `rowSums` over an `[M, 3]` array, and a row, on each view, from N and 2N iterations): a model of the row, `sumT`'s walk under `sumA` and a per-row scalar, with a switch to boxed vectors, the class of vectors kept with its `Storable` constraint so that the code differs between the two forms in the vector alone.

```haskell
{-# LANGUAGE BangPatterns, CPP, ScopedTypeVariables #-}
-- orthotope's sumT over its routes (Data/Array/Internal.hs at "Condense the
-- account of unorderedRouteT's sort and merge"), cut to two routes, one slice
-- where the view is contiguous and its elements by the odometer walk where it
-- is not, and its two layers: the generic code over a class of vectors, and a
-- wrapper at Storable vectors (DynamicS), where the instance is known.
-- BOXED: the same at boxed vectors, Data.Vector, the element class
-- kept as Storable so that the code is the Storable model's but for the
-- vector.
module Lib (T (..), A (..), sumA) where

#if defined(BOXED)
import qualified Data.Vector as V
import qualified Foreign.Storable as S
#else
import qualified Data.Vector.Storable as V
import qualified Data.Vector.Storable as S
#endif

class Vec v where
  vSum :: (S.Storable a, Num a) => v a -> a
  vIndex :: S.Storable a => v a -> Int -> a
  vSlice :: S.Storable a => Int -> Int -> v a -> v a

instance Vec V.Vector where
  vSum = V.sum
  vIndex = V.unsafeIndex
  vSlice = V.unsafeSlice

data Axis = Axis !Int !Int  -- stride and extent

-- A view: strides, offset, vector; the Storable array: shape and view.
data T v a = T ![Int] !Int !(v a)
data A a = A ![Int] !(T V.Vector a)

data Route = RSlice !Int !Int | RFill !Axis [Axis] !Int
  -- RFill: the innermost axis, the axes outside it innermost first, offset

{-# INLINE routeT #-}
routeT :: [Int] -> Int -> T v a -> Route
routeT sh l (T sts o _)
  | and (zipWith (==) sts (tail (scanr (*) 1 sh))) = RSlice o l
  | otherwise = case reverse (zipWith Axis sts sh) of
      inner : above -> RFill inner above o
      [] -> RSlice o 1

-- orthotope's odometer, its step and its walk, as at "Condense the account of
-- unorderedRouteT's sort and merge".
data Odometer = OdoLevel !Int !Int !Axis !Odometer | OdoDone

stepOdometer :: Odometer -> Odometer
stepOdometer OdoDone = OdoDone
stepOdometer (OdoLevel o c axis@(Axis s d) outer)
  | c > 1 = OdoLevel (o + s) (c - 1) axis outer
  | otherwise = case stepOdometer outer of
      OdoDone -> OdoDone
      next@(OdoLevel oNext _ _ _) -> OdoLevel oNext d axis next

{-# INLINE offsetsT #-}
offsetsT :: forall b. Axis -> [Axis] -> Int -> (Int -> b -> b) -> b -> b
offsetsT (Axis sk dk) above !start step nil =
  let block :: Int -> Odometer -> b
      block o outer =
        let go :: Int -> Int -> b
            go !i !p
              | i < dk = step p (go (i + 1) (p + sk))
              | otherwise = case stepOdometer outer of
                  OdoDone -> nil
                  next@(OdoLevel oNext _ _ _) -> block oNext next
        in  go 0 o
  in  block start
            (foldr (\axis@(Axis _ d) outer -> OdoLevel start d axis outer)
                   OdoDone above)

{-# INLINE routeFoldT #-}
routeFoldT :: (Vec v, S.Storable a)
           => v a -> Route -> (v a -> b -> b) -> (a -> b -> b) -> b -> b
routeFoldT v route onSlice onElem nil = case route of
  RFill axis above o ->
    offsetsT axis above o (\p rest -> onElem (vIndex v p) rest) nil
  RSlice o l -> onSlice (vSlice o l v) nil

-- orthotope's: a strict left fold from 0 over the parts, by a right fold
-- passing the accumulator to its continuation.
{-# INLINE sumT #-}
sumT :: (Vec v, S.Storable a, Num a) => [Int] -> T v a -> a
sumT sh t@(T _ _ v)
  | l == 0 = 0
  | otherwise = routeFoldT v (routeT sh l t)
      (\ s k !acc -> k (acc + vSum s)) (\ x k !acc -> k (acc + x)) id 0
  where !l = product sh

#if defined(INL)
{-# INLINE sumA #-}
#else
{-# INLINABLE sumA #-}
#endif
sumA :: (S.Storable a, Num a) => A a -> a
sumA (A sh t) = sumT sh t
```

```haskell
{-# LANGUAGE BangPatterns, CPP #-}
module Main (main) where

#if defined(BOXED)
import qualified Data.Vector as V
#else
import qualified Data.Vector.Storable as V
#endif
import Lib
import System.Environment (getArgs)

-- Opaque, so that nothing about a view is known where it is summed, as
-- orthotope's route, computed for each subarray, leaves it.
{-# OPAQUE pass #-}
pass :: Int -> A Double -> A Double
pass _ x = x

-- orthotope's per-subarray function of rerank 1 (\ r -> scalar (sumA r)),
-- out of line as its $weta is: the sum stored in a one-element vector,
-- strictly at Storable, as a thunk at boxed vectors.
{-# NOINLINE rowScalar #-}
rowScalar :: A Double -> V.Vector Double
rowScalar r = V.singleton (sumA r)

-- The rows of an [m, 3] array, each through rowScalar.
rowSums :: Int -> A Double -> V.Vector Double
rowSums k (A (m : ish) (T (s : ists) o v)) =
  V.generate m (\ i -> V.unsafeHead (rowScalar (pass k (A ish (T ists (o + i * s) v)))))
rowSums _ _ = error "rowSums: rank 0"

main :: IO ()
main = do
  [view, ms, ns] <- getArgs
  let m = read ms :: Int
      n = read ns :: Int
      v = V.generate (3 * m) fromIntegral :: V.Vector Double
      -- [m, 3]: transposed, each row strided, or dense, each row a slice.
      a | view == "strided" = A [m, 3] (T [1, m] 0 v)
        | otherwise = A [m, 3] (T [3, 1] 0 v)
      go :: Int -> Double -> Double
      go 0 !acc = acc
      go k !acc = go (k - 1) (acc + V.sum (rowSums k (pass k a)))
  print (go n 0)
```

`Main.dump-simpl`, whitespace collapsed. `b-inline`, in `$wrowScalar`: `let { x = case r of { A sh t -> case t of { T ds2 bx v -> case v of { Vector bx1 bx2 bx3 ->`, holding `joinrec { $wblock ww outer ww1 =` and `OdoDone -> D# ww2`; no `$w$s$wsumA`. `b-inlinable`: the thunk `case $w$s$wsumA ww ww2 ww3 ww7 ww9 of ww10 { __DEFAULT -> D# ww10`. `s-inline`: `case $wblock ww2 (go1 above) 0.0## of ww7`. `Main.dump-stg-final`: `b-inline` `let { x = \u []` and `let-no-escape { Rec { $wblock = \j [ww outer ww1]`; `b-inlinable` `let { x = \u []`; `s-inline` `let { Rec { $wblock = \r [ww7 outer ww8]`, a heap closure, `s-inlinable` `let-no-escape { Rec { $wblock = \j [ww8 outer ww9]`. `Main.dump-asm`, `b-inlinable`, the thunk after evaluating its subarray:

```
movq $.Lblock_info,(%rbp)
movq 15(%rbx),%rax
movq 15(%rax),%rcx
movq 7(%rcx),%r9
movq 15(%rcx),%r8
movq 23(%rax),%rdi
movq 7(%rax),%rsi
movq 7(%rbx),%r14
jmp $w$s$wsumA_info
```

and at its return point `movq $D#_con_info,-8(%r12)`.

`measure.sh 3 1000000` and `measure.sh 400 10000`:

```
b-inline dense: 1861.3 instructions, 1256.0 bytes a call; 620.42 instructions, 418.7 bytes a row
b-inline strided: 2536.2 instructions, 1712.0 bytes a call; 845.40 instructions, 570.7 bytes a row
b-inlinable dense: 1839.9 instructions, 1256.0 bytes a call; 613.30 instructions, 418.7 bytes a row
b-inlinable strided: 2557.2 instructions, 1712.0 bytes a call; 852.41 instructions, 570.7 bytes a row
s-inline dense: 1753.9 instructions, 968.0 bytes a call; 584.65 instructions, 322.7 bytes a row
s-inline strided: 2531.4 instructions, 1544.0 bytes a call; 843.81 instructions, 514.7 bytes a row
s-inlinable dense: 1783.9 instructions, 968.0 bytes a call; 594.65 instructions, 322.7 bytes a row
s-inlinable strided: 2499.3 instructions, 1424.0 bytes a call; 833.11 instructions, 474.7 bytes a row

b-inline dense: 237576.2 instructions, 163232.1 bytes a call; 593.94 instructions, 408.1 bytes a row
b-inline strided: 327624.1 instructions, 224032.1 bytes a call; 819.06 instructions, 560.1 bytes a row
b-inlinable dense: 234765.3 instructions, 163232.1 bytes a call; 586.91 instructions, 408.1 bytes a row
b-inlinable strided: 330425.6 instructions, 224032.1 bytes a call; 826.06 instructions, 560.1 bytes a row
s-inline dense: 223913.9 instructions, 124831.9 bytes a call; 559.78 instructions, 312.1 bytes a row
s-inline strided: 327411.4 instructions, 201631.9 bytes a call; 818.53 instructions, 504.1 bytes a row
s-inlinable dense: 227913.9 instructions, 124831.9 bytes a call; 569.78 instructions, 312.1 bytes a row
s-inlinable strided: 323161.1 instructions, 185631.9 bytes a call; 807.90 instructions, 464.1 bytes a row
```

At boxed vectors the out-of-line call costs 21 instructions a call on the strided view at `[3, 3]`, 7 a row at both sizes, at equal bytes, orthotope's 18 to 21 a call. At Storable the inlined walk's closure costs 40 bytes a row, O19's, and the out-of-line call 10 instructions a row on the dense view. On the boxed dense view the out-of-line form runs 7 instructions a row fewer, a difference whose cause was not read.

A third repro (`~/r/horde-ad/dist-inlcat/cases/O20-sumA-heap-check-per-element`, variants `inline` (C8) and `inlinable` (V2a), both with `-ddump-asm`; `run` is `200000 10`; `measure.sh K N`): orthotope's `sumA`, with a dense and a strided loop as `sumT` has, summing each 500-element row of a boxed vector of `K` Doubles into a one-element boxed vector, the stride given at run time; the result forced apart.

```haskell
{-# LANGUAGE BangPatterns, CPP, FlexibleContexts #-}
-- Orthotope's sumA over a row and rerank's per-row scalar result, cut down.
module Lib (module Lib) where

import qualified Data.Vector as V
import qualified Data.Vector.Generic as VG

-- sumA: INLINE in C8 (-DINL), INLINABLE in V2a.
#if defined(INL)
{-# INLINE sumA #-}
#else
{-# INLINABLE sumA #-}
#endif
-- A row read with a stride, the dense case its own loop, as sumT's.
sumA :: (VG.Vector v a, Num a) => Int -> v a -> a
sumA s v
  | s == 1 = go 0 0
  | otherwise = goS 0 0 0
  where
    !n = VG.length v
    go !i !acc | i >= n = acc
               | otherwise = go (i + 1) (acc + VG.unsafeIndex v i)
    goS !i !k !acc | k >= n = acc
                   | otherwise = goS (i + 1) (k + s)
                                     (acc + VG.unsafeIndex v k * fromIntegral i)

-- rerank 1 (\ r -> scalar (sumA r)) over rows of a dense boxed matrix: each
-- row's sum stored as the one element of a boxed vector.
{-# INLINE rerankSum #-}
rerankSum :: Int -> Int -> V.Vector Double -> V.Vector (V.Vector Double)
rerankSum st cols v =
  V.generate (V.length v `quot` cols)
             (\ r -> V.singleton (sumA st (V.unsafeSlice (r * cols) cols v)))
```

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import Lib
import qualified Data.Vector as V
import System.Environment (getArgs)

-- Opaque, so that each iteration sums anew.
{-# OPAQUE pass #-}
pass :: Int -> a -> a
pass _ x = x

-- The row's call, its result returned, and the harness's forcing apart.
{-# NOINLINE row #-}
row :: Int -> V.Vector Double -> V.Vector (V.Vector Double)
row st v = rerankSum st 500 v

{-# NOINLINE forced #-}
forced :: V.Vector (V.Vector Double) -> Double
forced = V.foldl' (\ acc s -> acc + V.head s) 0

main :: IO ()
main = do
  [ks, repss] <- getArgs
  let k = read ks :: Int
      reps = read repss :: Int
      v = V.generate k fromIntegral
      loop :: Int -> Double -> Double
      loop 0 !acc = acc
      loop r !acc = loop (r - 1) (acc + forced (row (pass r 1) (pass r v)))
  print (loop reps 0)
```

`Main.dump-asm`, whitespace collapsed, of `inline`: at the loop's head, where each element's return point continues, `addq $16,%r12`, `cmpq 856(%r13),%r12`, `ja`, then `movq 24(%rax,%rcx,8),%rax addq $-16,%r12 movq $.Lblock_info,-8(%rbp)` before the next element's evaluation, and at the exit `movq $D#_con_info,-8(%r12) movsd %xmm0,(%r12) leaq -7(%r12),%rbx`; `inlinable`: the client calls `case $w$ssumA ww5 (+# ww (*# ww4 500#)) 500# ww2 of ww6`, whose loop has no heap check and returns by `movsd %xmm0,%xmm1 jmp *(%rbp)`. By `measure.sh 200000 10`, twice alike: `inline` 36.20 instructions an element, `inlinable` 33.22, both 0.38 bytes; at 20, 26.40 and 23.42.

**Reproduces small:** yes, both halves' mechanism, and the figures in part: out of line costs 3 instructions a subarray at Storable, its worker's five arguments in registers (orthotope: 4, though its worker's sixth argument, taken on the stack, costs the 2 instructions of its move, which would make 5; the difference is not attributed); 9.3 to 9.5 at boxed strided in the first repro (orthotope: 5.9 to 6.0), not attributed further, and 21 a call at `[3, 3]` in the second, orthotope's 17.6 at the small strided and scaled views, and 18 to 21 over four small views; and the heap check's 4 instructions an element at an inlined loop whose exit boxes the sum, 6.98 an element saved out of line at boxed dense in the first repro, the check and three spill moves, and 2.98 in the third (orthotope: 3.99). Tried in the first: with the per-row function an INLINE-less lambda and the axes computed from the shape alone, the inlined form floated the shape's work out of the per-row code; with the axes taking the offset and `f` applied in two places, as orthotope's `rerank` does, INLINABLE's per-row lambda was inlined into the list's elements, so that only the INLINE form called a per-row function and out of line ran 8 a row fewer, hence the NOINLINE `perRow`; and with the walk's one-element exit returning the element itself, the boxed worker returned a boxed `Double`, with the heap check in its loop too, and the boxed dense gain did not appear. Tried in the third: a `sumA` with one loop, which the client inlined under INLINABLE too, and a literal stride, which did the same. The 40-byte closure C8 allocates for each subarray on Storable's views whose subarrays are not contiguous is O19's; Shaped's 15 to 24 instructions a call, not attempted.

### O21. A worker that returns through a nullary join point gets no tag signature, so its CPR wrapper rebuilds a strict-field constructor as a thunk; an INLINABLE function inlined call site by call site can make that join point where under INLINE it is inlined once, as `genericForce` does

**Rule.** E18's rule: a jump to a nullary join point is `TagDunno`, so a worker returning through one gets the tag signature `TagFun[TagDunno]`, and the strict-field `T` its CPR wrapper rebuilds under a lazy constructor becomes an updatable thunk of the fields, two header words and three free variables, 40 bytes a call. The nullary join point is the `otherwise` branch of `wholeOrSliceT`, which both failures of its `&&` guard reach after case-of-case; it stays shared when its body is too big to copy, as it is in this model once `genericForce`'s copy is inlined into each branch. INLINE `genericForce` is inlined once; INLINABLE `genericForce` passes the size test call site by call site, `adjusted_size = size + depth_penalty - discount` against `unfoldingUseThreshold`, 90, the penalty `size * (case_depth - 2) / 30` ([compiler/GHC/Core/Opt/Simplify/Inline.hs#L334][g459]--338; [compiler/GHC/Core/Unfold.hs#L103][g379], 119 and 122): at case depth 2 its adjusted size is 90 and it is inlined, at 4 it is 106 and it is not. With the specialiser on, this model's calls, all at case depth 5 or more, are refused and specialised (`SPEC/Main genericForce @Vector @Double`), and no byte moves. No patch of the working tree bears on it.

**Seen.** V3 (`genericForce` INLINABLE, the wrappers' `force` INLINE) against C8 (`genericForce` INLINE), 40 bytes a call more at forced Dynamic and Ranked Unboxed `force` rows, no byte moving summed; with the wrappers' `force` INLINABLE, no byte moving. In orthotope's own binaries (`~/r/horde-ad/dist-inlcat/cases/O21-genericforce-inlinable-under-inline-wrapper/orthotope-binaries.sh`, run by `post`), at the forced Dynamic Unboxed small dense `force` cell, 288 bytes a call in C8 and 328 in V3; at the row worker's return, C8 heap-checks 56 bytes and allocates `T` (`T_con_info`) and `DynamicG.A` directly, while V3 heap-checks 40 bytes and allocates an object whose info pointer, `0x1871710`, is a thunk entered under an update frame (`stg_upd_frame_info`) that evaluates two of its three free variables and builds `T`, then evaluates it and allocates `A`; and V3's worker has two copies of `genericForce`'s copy (`memcpy`) where C8's has one. And the pragma commit, `genericForce` INLINE, against its parent, "Probe whether a client's call builds a Route, a Range or an Axes", INLINABLE, at forced Shaped Unboxed `force`, small dense, 8 instructions a call more (callgrind of the two dump builds' binaries by `~/r/horde-ad/dist-inlcat/cases/O21-vecelem-route/orthotope-cg/run.sh`, 562.43 against 554.51 in its saved output, `~/r/horde-ad/dist-inlcat/cases/O21-vecelem-route/orthotope-cg/run-out.txt`). With `genericForce` INLINABLE the one `vForce (wholeOrSliceT ao n v)` becomes one call per outcome of `wholeOrSliceT`, pushed into the alternatives by Plan A of Note [Duplicating StrictArg] (`mkDupableContWithDmds`, [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4181][g460]; the Note at [#L4658][g461]), as V3's library module `DynamicU` shows, `1# -> jump $j1 (genericForce @V.Vector @a arg v1)`, each call a copy later: the parent's `OpsShaped.$w$s$wforce18` holds three `runRW#`, `newByteArray#` and `copyByteArray#`. Under INLINE the body's case on the vector gets a join point over the vector's fields (`mkDupableAlt`, [#L4322][g448]), so the commit's `$wlvl660` copies once, reached through `$j15`: `jump $j15 (ghc-internal:GHC.Internal.Prim.+# ww2 wild3) bx2 ww4;`, `__DEFAULT -> jump $j15 ww2 bx2 ww4;` and `1# -> jump $j15 ww2 ww3 ww4`, the model's `split-vecelem-gfinline` variant having the same jumps to its `$j2`. The 8 instructions are three stores of `$j15`'s arguments to the Haskell stack across `stg_newByteArray#`, two loads and two register moves to pass them, and the jump.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/O21-genericforce-inlinable-under-inline-wrapper`; variants `winline-gfinline`, `winline-gfinlinable`, `winlinable-gfinline` and `winlinable-gfinlinable`, the wrapper's `force` (`-DW_INLINE`) and `genericForce` (`-DGF_INLINE`) each INLINE or INLINABLE; and `ns-winline-gfinline` and `ns-winline-gfinlinable`, the INLINE wrapper with `-fno-specialise`, the second with `-dinline-check genericForce`; all six with `-ddump-stg-final` and `-ddump-stg-tags`; `measure.sh READING N` gives instructions and bytes a call of `force` on a dense `[3, 3]` Unboxed array, forced or summed, from N and 2N iterations; `post` runs the script reading orthotope's binaries): orthotope's chain at V3 cut to Unboxed vectors and rank 1, and the benchmark's row, `call (\ x -> force x)`, its result forced through `NFData` by an OPAQUE harness.

```haskell
{-# LANGUAGE BangPatterns, CPP #-}
-- orthotope's force chain at V3, cut to Unboxed vectors and rank 1:
-- the wrapper's force (DynamicU), the generic force (DynamicG), forceT
-- (Internal), the instance's vForce, and genericForce.
module Lib (T (..), GA (..), UA (..), force) where

import Control.DeepSeq (NFData (..))

import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Generic.Mutable as VGM
import qualified Data.Vector.Unboxed as U

class Vec v where
  vLength :: U.Unbox a => v a -> Int
  vSlice :: U.Unbox a => Int -> Int -> v a -> v a
  vForce :: U.Unbox a => v a -> v a
  vFill :: U.Unbox a => Int -> Int -> Int -> v a -> v a

-- Copies a vector into a new one of its length, allocated without a fill.
#if defined(GF_INLINE)
{-# INLINE genericForce #-}
#else
{-# INLINABLE genericForce #-}
#endif
genericForce :: VG.Vector w a => w a -> w a
genericForce v = VG.create $ do
  out <- VGM.unsafeNew (VG.length v)
  VG.unsafeCopy out v
  return out

instance Vec U.Vector where
  {-# INLINE vLength #-}
  vLength = U.length
  {-# INLINE vSlice #-}
  vSlice = U.unsafeSlice
  {-# INLINE vForce #-}
  vForce = genericForce
  {-# INLINE vFill #-}
  vFill o s n v = U.generate n (\ i -> U.unsafeIndex v (o + i * s))

-- A view: strides, offset, vector; the generic array: shape and view;
-- the Unboxed wrapper's array.
data T v a = T ![Int] !Int !(v a)
data GA v a = GA ![Int] !(T v a)
newtype UA a = UA { unUA :: GA U.Vector a }

instance NFData (UA a) where
  rnf (UA (GA sh (T sts o v))) = rnf sh `seq` rnf sts `seq` rnf o `seq` (v `seq` ())

{-# INLINE fromVectorT #-}
fromVectorT :: [Int] -> v a -> T v a
fromVectorT sh = T (tail (scanr (*) 1 sh)) 0

{-# INLINE wholeOrSliceT #-}
wholeOrSliceT :: (Vec v, U.Unbox a) => Int -> Int -> v a -> v a
#if defined(SLICE)
-- The control: always a slice, so that no two branches share one.
wholeOrSliceT o l v = vSlice o l v
#else
wholeOrSliceT o l v
  | o == 0 && vLength v == l = v
  | otherwise = vSlice o l v
#endif

data Route = RSlice !Int !Int | RFill !Int !Int !Int

-- At rank 1 here: one slice where the stride is 1, the elements otherwise.
{-# INLINE routeT #-}
routeT :: [Int] -> Int -> T v a -> Route
routeT sh l (T sts o _)
  | sts == tail (scanr (*) 1 sh) = RSlice o l
  | otherwise = RFill o (last sts) l

-- orthotope's forceT: a view that is one slice copied by vForce, any other
-- filled.
{-# INLINE forceT #-}
forceT :: (Vec v, U.Unbox a) => [Int] -> T v a -> T v a
forceT sh t@(T _ _ v) = fromVectorT sh $
  if l == 0
  then vSlice 0 0 v
  else case routeT sh l t of
    RSlice o n -> vForce (wholeOrSliceT o n v)
    RFill o s n -> vFill o s n v
  where !l = product sh

{-# INLINE gforce #-}
gforce :: (Vec v, U.Unbox a) => GA v a -> GA v a
gforce (GA sh t) = GA sh (forceT sh t)

#if defined(W_INLINE)
{-# INLINE force #-}
#else
{-# INLINABLE force #-}
#endif
force :: U.Unbox a => UA a -> UA a
force = UA . gforce . unUA
```

```haskell
{-# LANGUAGE BangPatterns, ExistentialQuantification #-}
module Main (main) where

import Control.DeepSeq (NFData (..))
import qualified Data.Vector.Unboxed as U
import GHC.Exts (inline)
import Lib
import System.Environment (getArgs)

-- orthotope's benchmark row: an operation in a record with its input and
-- a summing of its result, the operation applied by the harness and its
-- result forced by rnf, or summed.
data Call = forall a b. NFData b => Call (a -> b) a (a -> Int)

{-# INLINE call #-}
call :: NFData b => (a -> b) -> (b -> Int) -> a -> Call
call f s x = Call f x (\ y -> s (inline f y))

{-# OPAQUE pass #-}
pass :: Int -> Call -> Call
pass _ c = c

summed :: UA Double -> Int
summed (UA (GA _ (T _ _ v))) = round (U.sum v)

main :: IO ()
main = do
  [reading, ns] <- getArgs
  let n = read ns :: Int
      a = UA (GA [3, 3] (T [3, 1] 0 (U.generate 9 fromIntegral)))
      row = call (\ x -> force x) summed a
      run :: Call -> Int
      run (Call f x s)
        | reading == "summed" = s x
        | otherwise = rnf (f x) `seq` 1
      go :: Int -> Int -> Int
      go 0 !acc = acc
      go k !acc = go (k - 1) (acc + run (pass k row))
  print (go n 0)
```

`Main.dump-simpl`: `winline-gfinlinable` calls the specialisation, `case $w$sgenericForce ww3 wild ww5 of { (# ww8, ww9, ww10 #) ->`, where `winline-gfinline` has no `$w$sgenericForce`; neither, nor either variant with the wrapper INLINABLE, builds the thunk. `Main.dump-stg-tags`, whitespace collapsed, `ns-winline-gfinlinable`: `($wf, <TagFun[TagDunno]>) =`, `($j2, <TagFun[TagTuple[TagEPT, TagEPT, TagEPT, TagEPT]]>) = \j []`, and the thunk:

```
main_f_sat = \u [] case ww9 of ww9 { __DEFAULT -> case ww11 of ww11 { __DEFAULT -> T [ww9 ww10 ww11]; }; };
```

`ns-winline-gfinline`: `($wf, <TagFun[TagTuple[TagEPT, TagEPT, TagEPT, TagEPT]]>) =`, no thunk. `ns-winline-gfinlinable`'s `build.log`, two of Main's decisions:

```
Considering inlining: genericForce
  arg infos [ValueArg, NonTrivArg]
  interesting continuation BoringCtxt
  some_benefit True
  is exp: True
  is work-free: True
  guidance IF_ARGS [120 20] 250 0
  case depth = 2
  inline depth = 2
  depth based penalty = 0
  adjusted size = 90
  ANSWER = YES

Considering inlining: genericForce
  arg infos [ValueArg, NonTrivArg]
  interesting continuation BoringCtxt
  some_benefit True
  is exp: True
  is work-free: True
  guidance IF_ARGS [120 20] 250 0
  case depth = 4
  inline depth = 2
  depth based penalty = 16
  adjusted size = 106
  ANSWER = NO
```

`~/r/horde-ad/dist-inlcat/cases/O21-genericforce-inlinable-under-inline-wrapper/out/head/winline-gfinline/orthotope.txt`, from orthotope's binaries: `C8: Dynamic/force/small/dense/Unboxed ... 288` and `V3: ... 328`; C8 `15a17a8: add $0x38,%r12`, `15a17b5: movq $0x19a25d0,-0x30(%r12)` (`T_con_info`) and `15a17cd: movq $0x1a73108,-0x10(%r12)` (`A_con_info`); V3 `1871898: add $0x28,%r12`, `18718a9: movq $0x1871710,-0x20(%r12)`, the thunk's entry `1871719: movq $0x23ad398,-0x10(%rbp)` (`stg_upd_frame_info`), and `187192d: movq $0x1a75828,-0x10(%r12)` (`A_con_info`); `memcpy` sites, `C8: 1`, `V3: 2`.

`measure.sh forced 1000000` and `measure.sh summed 1000000`:

```
winline-gfinline forced: 1055.9 instructions, 592.0 bytes a call
winline-gfinlinable forced: 1066.9 instructions, 592.0 bytes a call
winlinable-gfinline forced: 1057.9 instructions, 592.0 bytes a call
winlinable-gfinlinable forced: 1068.9 instructions, 592.0 bytes a call
ns-winline-gfinline forced: 1048.9 instructions, 592.0 bytes a call
ns-winline-gfinlinable forced: 1103.5 instructions, 632.0 bytes a call
winline-gfinline summed: 970.7 instructions, 488.0 bytes a call
winline-gfinlinable summed: 981.7 instructions, 488.0 bytes a call
winlinable-gfinline summed: 989.3 instructions, 520.0 bytes a call
winlinable-gfinlinable summed: 1000.3 instructions, 520.0 bytes a call
ns-winline-gfinline summed: 970.7 instructions, 488.0 bytes a call
ns-winline-gfinlinable summed: 959.7 instructions, 488.0 bytes a call
```

The `ns-` pair is V3 against C8: 40 bytes a call forced and none summed, from `genericForce`'s pragma alone, under the INLINE wrapper, and one copy of `genericForce`'s copy in the row worker against two (`post` counting the lines holding `copyByteArray#` in `$wf` in the `Main.dump-simpl` of `ns-winline-gfinline` and of `ns-winline-gfinlinable`, into `~/r/horde-ad/dist-inlcat/cases/O21-genericforce-inlinable-under-inline-wrapper/out/head/ns-winline-gfinlinable/copies.txt`), as C8's one `memcpy` against V3's two. The INLINABLE wrapper's 32 bytes summed are O22's.

**Reproduces small:** in part: the 40-byte thunk, its cause in the nullary join point's `TagDunno`, and V3's pattern, 40 bytes forced and none summed from `genericForce` INLINABLE under the INLINE wrapper, reproduce, and the thunk is located in V3's binary, absent from C8's; but the model shows the pragma's effect only with Main's specialiser off, its calls of `genericForce` sitting too deep in cases for the size test before the specialiser replaces them, and V3, unlike the model, inlines the unspecialised unfolding at one outcome before the specialiser runs. In V3's Core (`OpsDynamic.dump-simpl`) the Dynamic Unboxed `force` row's worker `$wlvl744` holds two `copyByteArray#`, two outcomes of `forceT`'s one `vForce (wholeOrSliceT ao n v)`, each from a different unfolding (a rebuild of V3 tracing `OpsDynamic`, its Tidy Core with V3's binders and right-hand-side sizes). The slice's, in the nullary join point `$j31`, is `genericForce`'s unspecialised unfolding, inlined in the gentle run before the specialiser runs, `case depth = 1 ... adjusted size = 90 ANSWER = YES`, once in each of the eleven Unboxed `force` rows: the simplifier statistics' `11 Data.Array.Internal.genericForce`, beside `22 SPEC/OpsDynamic genericForce @Vector @Double` and `6 $w$sgenericForce`. The whole vector's, in the `1#` alternative, is refused there, `case depth = 3 ... adjusted size = 98 ANSWER = NO`, becomes a call of the specialisation by its rule and of its worker after worker/wrapper, and is inlined in the final simplifier, after CSE, `guidance IF_ARGS [0 0 0] 126 0 case depth = 2 inline depth = 1 depth based penalty = 0 adjusted size = 86 ANSWER = YES`. In the simplifier after worker/wrapper the worker's guidance is `UnfNever`, while its body still holds both `error` calls, whose string literals alone size 1100 against `-funfolding-creation-threshold`, 750 (`litSize`, [compiler/GHC/Core/Unfold.hs#L772][g462]; `TooBig -> UnfNever`, [compiler/GHC/Core/Unfold.hs#L351][g463]). In a model with the wrapper INLINE and the specialiser on (`~/r/horde-ad/dist-inlcat/cases/O21-vecelem-route`), no call of `genericForce` is inlined before the specialiser, both outcomes become worker calls, and at the rows, at case depth 4, A09's penalty puts them over the threshold, `depth based penalty = 8 adjusted size = 94 ANSWER = NO`.

### O22. One pragma of an INLINE chain made INLINABLE: a wrapper or a helper whose result is built in a join point from a vector its branches choose returns that vector boxed out of line, a strides list of a static shape is computed at every call instead of once, and a method whose unfolding is one call inlines as before

**Rule.** Making one wrapper of an INLINE chain INLINABLE, here `force` or `forceT`, gives the client a copy specialised at its types (the rules `"SPEC/Main $wforceS @Double"` and `"SPEC/Main $wforceT @Vector @Double"` in `Main.dump-simpl`) that is too big to inline (`tryUnfolding`, [compiler/GHC/Core/Opt/Simplify/Inline.hs#L302][g450], `small_enough`, [#L338][g222]), so the chain below it runs out of line, with two effects on bytes. First, U19's rule one level down: `forceT` computes the vector in its branches and builds `T` once, so case-of-case puts the result's construction into a join point `$j arg` that each branch jumps to with its finished vector; CPR analysis gives a join point's parameter a CPR property only from its demand (`extendSigEnvForArg`, [compiler/GHC/Core/Opt/CprAnal.hs#L250][g464] and [#L751][g465]; `argCprType`, [#L762][g466]; Note [CPR for binders that will be unboxed], [#L796][g467]), and this join point returns the vector whole, its case binder, so the demand is boxed and the out-of-line worker's CPR is `1`, its result `(# ..., Vector Double #)`: each call builds the vector's 4-word box, and a caller that sums the result takes it apart, 32 bytes a call; a caller that forces the result keeps the box, so its bytes do not move. Inlined, the same join point's body is the caller's sum, whose demand unboxes the vector, and the join point takes its three fields. Second, a shape known statically: inlined, `tail $ getStridesT sh` at Shaped's static shape has no free local variable and full laziness floats it to the top level (`lvlMFE`, [compiler/GHC/Core/Opt/SetLevels.hs#L588][g394]), computed once; out of line the shape is the copy's argument and the strides are built at every call, a cons cell and an `I#` box, 40 bytes, a dimension. Dynamic's shape is a run-time value, so its strides are built at every call either way. A pragma whose function's unfolding is a single call (`vForce = genericForce`, guidance `IF_ARGS [0] 40 60`) is inlined at every call under INLINABLE as under INLINE, and nothing moves.

**Seen.** On "Build no thunk under Right where a conversion gains by it" (CP2's code), FA (the Storable Dynamic and Ranked wrappers' `force` INLINABLE) costs 32 bytes a call at summed small Storable `force` rows; FB (the Storable instance's `vForce` INLINABLE) moves no byte; FC (`forceT` INLINABLE) costs 80 to 200 bytes forced and 112 to 232 summed at Shaped small `force` rows, every kind. Read again here from the stage builds' binaries (CP2, its tree that of "Build no thunk under Right where a conversion gains by it" but for `Data/Array/Convert.hs`, and FA, FB and FC; `--iters 20000 -m glob CELL`, bytes a call), CP2, FA, FB, FC: summed `Dynamic/force/small/dense` 200, 232, 200, 232 at Storable, 184, 184, 184, 216 at Unboxed and 200, 200, 200, 232 at boxed, forced unmoved (304, 288, 304); `Shaped/force/small/dense` Storable and boxed forced 200, 200, 200, 280 and summed 120, 120, 120, 232; `Shaped/force.rank5/small/dense/Storable` forced 480, 480, 480, 680 and summed 400, 400, 400, 632. So FC costs 32 bytes at summed small dense Dynamic `force` too, every kind. FA's Core (`OpsDynamic.dump-simpl`): `OpsDynamic.$w$s$wforce` returns `(# IU.ShapeL, [Int], ghc-internal:GHC.Internal.Prim.Int#, Data.Vector.Storable.Vector Double #)`, and the summing worker `$wlvl747` takes the vector apart, `case ww11 of { Data.Vector.Storable.Vector ipv ipv1 ipv2 ->`. FC's binary has full copies of `forceT` in the benchmark modules (`OpsDynamic_zdwzdszdwforceT_info`, `OpsShaped_zdwzdszdwforceT1_info`) and none in `DynamicS`. Where `forceT` is INLINABLE, the Shaped row calls the specialised wrapper rather than inlining it, its shape a top-level value and its view lambda-bound, both trivial, O23's case: in the Core of C0, a build with `forceT` INLINABLE (`OpsShaped.dump-simpl`), ``lvl388 = \ (a :: IS.Array Sh Double) -> OpsShaped.$sforceT1 lvl354 (a `cast` ...)`` (whitespace collapsed), the wrapper taking `T` apart around `OpsShaped.$w$s$wforceT1` and rebuilding it; the repro's client inlines it. `forceT`'s comment records the level above, `T` returned boxed until its result was built in one place (U19); the vector is the field below it.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/O22-force-chain-one-pragma-bytes`, variants `cp2`, the chain INLINE, and `fa` (`-DFA`), `fb` (`-DFB`), `fc` (`-DFC`), one pragma INLINABLE each, `fa` and `fc` with `-ddump-cpranal`; `fa-fresh` and `fc-fresh`, `fa` and `fc` with `-DFRESH`, the empty view's vector built at each call; `fa-check`, `fb-check` and `fc-check`, `fa`, `fb` and `fc` with each decision about `$s$wforceS`, `$fVectorVector_$cvForce` and `$s$wforceT`, by `-dinline-check`; `measure.sh N` gives bytes and instructions a call of each reading from N and 2N iterations): orthotope's chain in three modules as orthotope has them, `Lib` the generic parts (`Internal`, `DynamicG`, `ShapedG`), `Dyn` the Storable instance and wrapper (`DynamicS`), `Main` the client, reading a [3, 3] dense Storable view through the Dynamic wrapper and a Shaped one at rank 2 and 5, the result forced or summed.

```haskell
{-# LANGUAGE BangPatterns, CPP, ConstraintKinds, DataKinds, KindSignatures,
             ScopedTypeVariables, TypeFamilies #-}
-- orthotope's Internal, DynamicG and ShapedG parts of force's chain, the
-- chain INLINE but for FC's forceT INLINABLE, the fill out of line.
module Lib (T (..), Array (..), ArraySh (..), Shape (..), Vector (..),
            genericForce, genericFill, forceG, forceSh) where

import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (..))
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Generic.Mutable as VGM
import GHC.TypeLits (KnownNat, Nat, natVal)

-- orthotope's view (strides, offset, values) and Dynamic array.
data T v a = T ![Int] !Int !(v a)
data Array v a = A ![Int] !(T v a)

-- The Shaped array, as orthotope's newtype.
newtype ArraySh (sh :: [Nat]) v a = ASh (T v a)

class Shape (sh :: [Nat]) where
  shapeP :: Proxy sh -> [Int]

instance Shape '[] where
  {-# INLINE shapeP #-}
  shapeP _ = []

instance (KnownNat n, Shape sh) => Shape (n ': sh) where
  {-# INLINE shapeP #-}
  shapeP _ = fromInteger (natVal (Proxy :: Proxy n)) : shapeP (Proxy :: Proxy sh)

class Vector v where
  type VecElem v :: Type -> Constraint
  vLength :: VecElem v a => v a -> Int
  vSlice :: VecElem v a => Int -> Int -> v a -> v a
  vForce :: VecElem v a => v a -> v a
  vConcat :: VecElem v a => [v a] -> v a
  vFill :: VecElem v a => [Int] -> [Int] -> Int -> Int -> v a -> v a

-- A copy of the vector, as orthotope's genericForce.
{-# INLINE genericForce #-}
genericForce :: VG.Vector w a => w a -> w a
genericForce v = VG.create $ do
  out <- VGM.unsafeNew (VG.length v)
  VG.unsafeCopy out v
  return out

-- The elements of a view that is not dense, into a new vector.
{-# INLINABLE genericFill #-}
genericFill :: VG.Vector w a => [Int] -> [Int] -> Int -> Int -> w a -> w a
genericFill sh st o l v = VG.fromListN l [VG.unsafeIndex v p | p <- offs sh st o]
  where offs [] [] p = [p]
        offs (d : ds) (s : ss) p = concat [offs ds ss (p + i * s) | i <- [0 .. d - 1]]
        offs _ _ _ = error "genericFill"

-- orthotope's getStridesT: the row-major strides of a shape, its size first.
getStridesT :: [Int] -> [Int]
getStridesT [] = [1]
getStridesT (s : ss) = case getStridesT ss of
  r@(m : _) -> let !x = s * m in x : r
  [] -> []

-- Whether the strides are the row-major ones of the shape; allocates nothing.
dense :: [Int] -> [Int] -> Bool
dense (_ : ds) (s : ss) = s == product ds && dense ds ss
dense [] [] = True
dense _ _ = False

{-# INLINE fromVectorT #-}
fromVectorT :: [Int] -> v a -> T v a
fromVectorT sh = T (tail $ getStridesT sh) 0

-- The view's elements in a vector of their own, as orthotope's forceT: the
-- empty view's vector is vConcat [], a dense one's a copy by vForce, any
-- other's a fill.
#if defined(FC)
{-# INLINABLE forceT #-}
#else
{-# INLINE forceT #-}
#endif
forceT :: (Vector v, VecElem v a) => [Int] -> T v a -> T v a
forceT sh (T st o v) = fromVectorT sh $
  if l == 0
#if defined(FRESH)
  then vForce (vSlice 0 0 v)  -- built at each call, where vConcat [] is a CAF
#else
  then vConcat []
#endif
  else if dense sh st
       then vForce (if o == 0 && vLength v == l then v else vSlice o l v)
       else vFill sh st o l v
  where !l = product sh

-- The generic Dynamic force, INLINE as orthotope's DynamicG.force.
{-# INLINE forceG #-}
forceG :: (Vector v, VecElem v a) => Array v a -> Array v a
forceG (A sh t) = A sh (forceT sh t)

-- The Shaped force, INLINE as orthotope's ShapedG.force.
{-# INLINE forceSh #-}
forceSh :: forall sh v a . (Vector v, VecElem v a, Shape sh)
        => ArraySh sh v a -> ArraySh sh v a
forceSh (ASh t) = ASh (forceT (shapeP (Proxy :: Proxy sh)) t)
```

```haskell
{-# LANGUAGE CPP, TypeFamilies #-}
-- orthotope's DynamicS: the Storable instance of Vector and the Storable
-- Dynamic array's force, INLINE but for FA's (force INLINABLE) and FB's
-- (vForce INLINABLE).
module Dyn (ArrayS (..), forceS) where

import qualified Data.Vector.Storable as VS
import Foreign.Storable (Storable)
import Lib

newtype ArrayS a = AS { unAS :: Array VS.Vector a }

instance Vector VS.Vector where
  type VecElem VS.Vector = Storable
  {-# INLINE vLength #-}
  vLength = VS.length
  {-# INLINE vSlice #-}
  vSlice = VS.unsafeSlice
#if defined(FB)
  {-# INLINABLE vForce #-}
#else
  {-# INLINE vForce #-}
#endif
  vForce = genericForce
  {-# INLINE vConcat #-}
  vConcat [] = VS.empty
  vConcat vs = VS.concat vs
  {-# INLINE vFill #-}
  vFill = genericFill

-- The Storable Dynamic wrapper's force, point-free as orthotope's
-- DynamicS.force.
#if defined(FA)
{-# INLINABLE forceS #-}
#else
{-# INLINE forceS #-}
#endif
forceS :: Storable a => ArrayS a -> ArrayS a
forceS = AS . forceG . unAS
```

```haskell
{-# LANGUAGE BangPatterns, DataKinds #-}
module Main (main) where

import qualified Data.Vector.Storable as VS
import Dyn
import Lib
import System.Environment (getArgs)

-- Opaque, so that each iteration forces anew and the result is built.
{-# OPAQUE pass #-}
pass :: Int -> a -> a
pass _ x = x

{-# OPAQUE consume #-}
consume :: T VS.Vector Double -> Int
consume (T st o v) = sum st + o + VS.length v

-- The benchmark's two readings of a force at a small dense view: the result
-- forced (built and handed to an opaque function), or summed (taken apart).
{-# NOINLINE dynForced #-}
dynForced :: ArrayS Double -> Int
dynForced a = case forceS a of AS (A sh t) -> sum sh + consume t

{-# NOINLINE dynSummed #-}
dynSummed :: ArrayS Double -> Double
dynSummed a = case forceS a of
  AS (A sh (T st o v)) -> fromIntegral (sum sh + sum st + o) + VS.sum v

{-# NOINLINE shForced #-}
shForced :: ArraySh '[3, 3] VS.Vector Double -> Int
shForced a = case forceSh a of ASh t -> consume t

{-# NOINLINE shSummed #-}
shSummed :: ArraySh '[3, 3] VS.Vector Double -> Double
shSummed a = case forceSh a of
  ASh (T st o v) -> fromIntegral (sum st + o) + VS.sum v

{-# NOINLINE sh5Forced #-}
sh5Forced :: ArraySh '[3, 1, 3, 1, 1] VS.Vector Double -> Int
sh5Forced a = case forceSh a of ASh t -> consume t

{-# NOINLINE sh5Summed #-}
sh5Summed :: ArraySh '[3, 1, 3, 1, 1] VS.Vector Double -> Double
sh5Summed a = case forceSh a of
  ASh (T st o v) -> fromIntegral (sum st + o) + VS.sum v

main :: IO ()
main = do
  [reading, ns] <- getArgs
  let n = read ns :: Int
      v = VS.generate 9 fromIntegral :: VS.Vector Double
      dyn = AS (A [3, 3] (T [3, 1] 0 v))
      sh = ASh (T [3, 1] 0 v) :: ArraySh '[3, 3] VS.Vector Double
      sh5 = ASh (T [3, 3, 1, 1, 1] 0 v) :: ArraySh '[3, 1, 3, 1, 1] VS.Vector Double
      loopI :: (Int -> Int) -> Int -> Int -> Int
      loopI _ 0 !acc = acc
      loopI f k !acc = loopI f (k - 1) (acc + f k)
      loopD :: (Int -> Double) -> Int -> Double -> Double
      loopD _ 0 !acc = acc
      loopD f k !acc = loopD f (k - 1) (acc + f k)
  case reading of
    "dyn-forced" -> print (loopI (\ k -> dynForced (pass k dyn)) n 0)
    "dyn-summed" -> print (loopD (\ k -> dynSummed (pass k dyn)) n 0)
    "sh-forced" -> print (loopI (\ k -> shForced (pass k sh)) n 0)
    "sh-summed" -> print (loopD (\ k -> shSummed (pass k sh)) n 0)
    "sh5-forced" -> print (loopI (\ k -> sh5Forced (pass k sh5)) n 0)
    _ -> print (loopD (\ k -> sh5Summed (pass k sh5)) n 0)
```

`fa`'s `Main.dump-cpranal`, whitespace collapsed, the join point and one of the jumps:

```
$j arg = case xs of wild { __DEFAULT -> case arg of wild1 { Vector ipv4 ipv5 ipv6 -> (# ww4, wild, 0#, wild1 #)
False -> jump $j ($sgenericFill ww4 ww5 (I# ww2) l ww6);
```

`fa`'s `Main.iface` for `$s$wforceS`: `-> (# [GHC.Internal.Types.Int], [GHC.Internal.Types.Int], GHC.Internal.Prim.Int#, Data.Vector.Storable.Vector GHC.Internal.Types.Double #)` and `Strictness: <1L><1L><L><1L>, CPR: 1`; in `Main.dump-simpl` the summing worker calls it and takes the vector apart: `case $s$wforceS ww4 ww5 ww2 ww6 of { (# ww7, ww8, ww9, ww10 #) ->` and `case ww10 of { Vector ipv3 ipv4 ipv5 ->`. `fc`'s `$s$wforceT` has the same join point (`case arg of wild2 { Vector ipv ipv ipv -> (# wild1, 0#, wild2 #) }` at CPR analysis), every caller calls it, the Shaped ones with their static shapes, `case $s$wforceT lvl43 ww3 ww1 ww4 of { (# ww5, ww6, ww7 #) ->`, `lvl43` the static `[3, 3]`, and it builds the strides, `case getStridesT sh of`; `cp2` has `lvl38 = getStridesT sh8` at the top level, `sh8` the static `[3, 3]`, and Dynamic's `case getStridesT ww4 of` in each reading. `fb`'s `Main.dump-simpl` is `cp2`'s, and `fb-check`'s `build.log` gives `guidance IF_ARGS [0] 40 60` and `ANSWER = YES` at every call. `fa-check` and `fc-check` answer `NO` at every call, `fa-check`'s smallest guidance `IF_ARGS [20 20 32 20] 527 0`.

`measure.sh 200000`, bytes and instructions a call:

```
          dyn-forced  dyn-summed  sh-forced  sh-summed  sh5-forced  sh5-summed
cp2       296/869.2   216/902.3   200/585.0  136/621.7  200/1068.0  136/1104.7
fa        296/883.1   248/934.0   200/585.0  136/621.7  200/1068.0  136/1104.7
fb        296/869.2   216/902.3   200/585.0  136/621.7  200/1068.0  136/1104.7
fc        296/867.1   248/915.0   280/775.7  248/826.0  400/1501.3  368/1563.7
fa-fresh  296/883.1   248/934.0   200/585.0  136/621.7  200/1068.0  136/1104.7
fc-fresh  296/867.1   248/915.0   280/775.7  248/826.0  400/1501.3  368/1563.7
```

FA, 32 at `dyn-summed` alone; FB, nothing; FC, 32 at `dyn-summed`, 80 and 112 at rank 2 and 200 and 232 at rank 5, `dyn-forced` unmoved: orthotope's figures, each. The fresh variants move nothing against `fa` and `fc`.

**Reproduces small:** yes, every byte figure exactly. Tried: the instance and the wrapper in the module that defines `forceT`, where the wrapper's own body made a copy of `forceT` specialised on the `Vector` dictionary alone, which the client then reached by that copy's rule, its product accumulator boxed, 16 bytes a dimension more than orthotope at every FC reading; with the instance and the wrapper in a module of their own, as orthotope's `DynamicS`, the client makes its own copy. Refuted: that the 32 bytes come from the empty view's branch returning `vConcat [] = V.empty`, a CAF whose case binder takes the CAF's CPR, which is none ([CprAnal.hs#L258][g468], and [#L549][g469] to [#L553][g470], a thunk's CPR trimmed): `fa-fresh` and `fc-fresh` build that vector at each call and cost the same.

### O23. A specialised worker/wrapper wrapper is inlined only where an argument or the context is interesting, so a bang that evaluates an argument can decide it, as for the call of `$sreshape'` in `reshape`'s row

**Rule.** Worker/wrapper gives a wrapper the unfolding guidance `UnfWhen` with `ug_boring_ok = boringCxtNotOk` (`mkWrapperUnfolding`, [compiler/GHC/Core/Unfold/Make.hs#L119][g471]), and a specialisation of the wrapper keeps it (`specUnfolding`, [#L205][g445]). `tryUnfolding` inlines an `UnfWhen` unfolding only when `boring_ok || some_benefit || unfoldingVeryAggressive opts` ([compiler/GHC/Core/Opt/Simplify/Inline.hs#L311][g6]), `some_benefit` being an argument that is not trivial or, saturated, an interesting context (`calc_some_benefit`, [#L394][g7], `interesting_args = any nonTriv arg_infos` at [#L402][g245]). `interestingArg` ([compiler/GHC/Core/Opt/Simplify/Utils.hs#L1148][g472], Note [Interesting arguments]) calls a lambda-bound variable `TrivArg` and a top-level value whose unfolding is neither a constructor application nor expandable `TrivArg` too ([#L1196][g473]), while a variable a `case` has evaluated, whose unfolding is `OtherCon []` (Note [Case binder evaluated-ness], [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L3806][g474]), is `NonTrivArg` ([compiler/GHC/Core/Opt/Simplify/Utils.hs#L1189][g475]). The row `\ x -> reshape x` calls the specialised wrapper `$sreshape'` in the tail of a lambda, a boring context, with the two shapes, top-level values behind a size check, and the lambda-bound array: every argument trivial, so it is called and not inlined. A bang in the INLINABLE wrapper's `reshape` puts a `case` on the array in its unfolding, so the array argument is an evaluated variable, `NonTrivArg`, and `$sreshape'` inlines; shapes that are constructor applications inline it too. Point-free and named without a bang compile alike. No patch of the working tree bears on it.

**Seen.** Forced Shaped Storable and Unboxed `reshape`, 8 instructions a call more at every size without the bang in ShapedS's and ShapedU's `reshape`, no byte moving; in `OpsShaped`'s Core at N (named, unbanged), the row at Storable `[3, 3]` to `[9]` is ``lvl2749 = \ (a :: IS.Array ShSmall Double) -> OpsShaped.$sreshape' @[3, 3] @'[9] sh8 OpsShaped.$s$wbroadcast_x2 (a `cast` ...)``, `$sreshape'` taking the array's `T` apart, calling `$s$wbroadcast_$s$wreshape'` and rebuilding the `T`, and the shapes are, module prefixes dropped, `sh8 = case lvl1562 (Proxy @[Nat] @'[9]) of { I# _ -> lvl392 }` and `$s$wbroadcast_x2 = case $s$wbroadcast106 of { I# ipv -> $s$wbroadcast105 }`; at NB (banged) the row takes the `T` apart and calls the worker. The interface of `reshape'` at N: `Inline: [2]`, `Unfolding: Core: StableSystem <5,TrueFalse>`.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/O23-reshape-bang-specialised-wrapper`, variants `pointfree`, `named` (`-DNAMED`), `banged` (`-DBANGED`), `literal` (`-DNAMED -DLITERAL`, the shapes literal lists), and `named-check` and `banged-check`, `named` and `banged` with `-dinline-check $sreshape'`; `measure.sh N` gives instructions and bytes a forced call from N and 2N iterations): ShapedG's `reshape'`, INLINABLE and split by worker/wrapper, behind the INLINE generic `reshape`, a Storable wrapper module's INLINABLE `reshape`, and the benchmark's row in a record applied by a harness that forces its result, each shape a top-level value behind an OPAQUE size check.

```haskell
{-# LANGUAGE BangPatterns, ScopedTypeVariables #-}
-- orthotope's ShapedG reshape at NB, cut: a class of vectors at
-- Storable elements, a shape class standing in for the type-level shapes,
-- and reshape' with its three cases.
module G (Vec (..), Shape (..), T (..), Array (..), reshape, toVectorT) where

import Data.Proxy (Proxy (..))
import qualified Data.Vector.Storable as V

class Vec v where
  vLength :: V.Storable a => v a -> Int
  vSlice :: V.Storable a => Int -> Int -> v a -> v a
  vForce :: V.Storable a => v a -> v a
  vGen :: V.Storable a => Int -> (Int -> a) -> v a
  vIndex :: V.Storable a => v a -> Int -> a

instance Vec V.Vector where
  {-# INLINE vLength #-}
  vLength = V.length
  {-# INLINE vSlice #-}
  vSlice = V.unsafeSlice
  {-# INLINE vForce #-}
  vForce = V.force
  {-# INLINE vGen #-}
  vGen = V.generate
  {-# INLINE vIndex #-}
  vIndex = V.unsafeIndex

class Shape sh where
  shapeP :: Proxy sh -> [Int]

-- A view: strides, offset, vector; the Shaped array a newtype of it.
data T v a = T ![Int] !Int !(v a)
newtype Array sh v a = A (T v a)

stridesOf :: [Int] -> [Int]
stridesOf = tail . scanr (*) 1

-- The strides of the new shape, where the view is contiguous.
simpleReshape :: [Int] -> [Int] -> [Int] -> Maybe [Int]
simpleReshape ost sh' sh
  | ost == stridesOf sh' = Just (stridesOf sh)
  | otherwise = Nothing

{-# INLINE toVectorT #-}
toVectorT :: (Vec v, V.Storable a) => [Int] -> T v a -> v a
toVectorT sh (T ost oo v)
  | ost == stridesOf sh = vForce (vSlice oo (product sh) v)
  | otherwise = vGen (product sh) (\ i -> vIndex v (oo + i * last ost))

{-# INLINE reshape #-}
reshape :: forall sh' sh v a . (Vec v, V.Storable a, Shape sh, Shape sh')
        => Array sh v a -> Array sh' v a
reshape a = reshape' (shapeP (Proxy :: Proxy sh')) (shapeP (Proxy :: Proxy sh)) a

{-# INLINABLE reshape' #-}
reshape' :: (Vec v, V.Storable a) => [Int] -> [Int] -> Array sh v a -> Array sh' v a
reshape' sh sh' (A t@(T ost oo v))
  | vLength v == 1 = A $ T (map (const 0) sh) 0 v
  | Just nst <- simpleReshape ost sh' sh = A $ T nst oo v
  | otherwise = A $ T (stridesOf sh) 0 (toVectorT sh' t)
```

```haskell
{-# LANGUAGE BangPatterns, CPP, ScopedTypeVariables #-}
-- orthotope's ShapedS wrapper: the array a newtype of the generic one at
-- Storable vectors, its reshape INLINABLE, point-free, named or banged.
module S (Array (..), reshape) where

import qualified Data.Vector.Storable as V
import qualified G

newtype Array sh a = A { unA :: G.Array sh V.Vector a }

{-# INLINABLE reshape #-}
reshape :: forall sh' sh a . (V.Storable a, G.Shape sh, G.Shape sh')
        => Array sh a -> Array sh' a
#if defined(BANGED)
reshape !a = A (G.reshape (unA a))
#elif defined(NAMED)
reshape a = A (G.reshape (unA a))
#else
reshape = A . G.reshape . unA
#endif
```

```haskell
{-# LANGUAGE BangPatterns, CPP, ExistentialQuantification #-}
module Main (main) where

import Control.DeepSeq (NFData (..))
import Data.Proxy (Proxy (..))
import qualified Data.Vector.Storable as V
import qualified G
import qualified S
import System.Environment (getArgs)

data S33
data S9
-- Each shape behind a check of its size, as orthotope's shapes are: a
-- top-level value that is no constructor application.
{-# OPAQUE sizeCheck #-}
sizeCheck :: Int -> Int
sizeCheck n = n

#if defined(LITERAL)
-- The control: each shape a list of literals, a constructor application.
instance G.Shape S33 where shapeP _ = [3, 3]
instance G.Shape S9 where shapeP _ = [9]
#else
instance G.Shape S33 where shapeP _ = sizeCheck 9 `seq` [3, 3]
instance G.Shape S9 where shapeP _ = sizeCheck 9 `seq` [9]
#endif

instance NFData (S.Array sh a) where
  rnf (S.A (G.A (G.T sts o v))) = rnf sts `seq` rnf o `seq` (v `seq` ())

-- The benchmark's row: an operation in a record, applied by the harness,
-- its result forced.
data Call = forall a b. NFData b => Call (a -> b) a

{-# OPAQUE pass #-}
pass :: Int -> Call -> Call
pass _ c = c

main :: IO ()
main = do
  [ns] <- getArgs
  let n = read ns :: Int
      a = S.A (G.A (G.T [3, 1] 0 (V.generate 9 fromIntegral))) :: S.Array S33 Double
      row = Call (\ x -> S.reshape x :: S.Array S9 Double) a
      run (Call f x) = rnf (f x)
      go :: Int -> Int -> Int
      go 0 !acc = acc
      go k !acc = case run (pass k row) of () -> go (k - 1) (acc + 1)
  print (go n 0 + length (G.shapeP (Proxy :: Proxy S9)))
```

`Main.dump-simpl`, whitespace collapsed. `pointfree` and `named`: ``row = \ x -> $sreshape' lvl36 lvl37 (x `cast` <Co:4>)``, with

```
$sreshape' = \ @k @k1 @sh @sh' sh1 sh'1 ds -> case ds `cast` <Co:6> of { T ww ww1 ww2 -> case $s$wreshape' sh1 sh'1 ww ww1 ww2 of { (# ww3, ww4, ww5 #) -> (T ww3 ww4 ww5) `cast` <Co:7>
```

`banged`: ``row = \ x -> case x `cast` <Co:11> of { T ipv ipv1 ipv2 -> case $s$wreshape' lvl36 lvl37 ipv ipv1 ipv2 of``; `literal`: ``row = \ x -> case x `cast` <Co:11> of { T ww ww1 ww2 -> case $s$wreshape' $fShapeTYPES4 $fShapeTYPES1 ww ww1 ww2 of``. `build.log`, Main's decision at the row's call, `named-check` and `banged-check`:

```
Considering inlining: $sreshape'
  arg infos [TrivArg, TrivArg, TrivArg]
  interesting continuation BoringCtxt
  some_benefit False
  is exp: True
  is work-free: True
  guidance ALWAYS_IF(arity=3,unsat_ok=True,boring_ok=False)
  case depth = 0
  inline depth = 2
  ANSWER = NO

Considering inlining: $sreshape'
  arg infos [TrivArg, TrivArg, NonTrivArg]
  interesting continuation BoringCtxt
  some_benefit True
  is exp: True
  is work-free: True
  guidance ALWAYS_IF(arity=3,unsat_ok=True,boring_ok=False)
  case depth = 0
  inline depth = 2
  ANSWER = YES
```

`measure.sh 1000000`:

```
pointfree: 900.3 instructions, 624.0 bytes a call
named: 900.3 instructions, 624.0 bytes a call
banged: 892.3 instructions, 624.0 bytes a call
literal: 874.3 instructions, 624.0 bytes a call
```

The call costs 8 instructions a call at equal bytes, orthotope's figure; `literal` runs 18 fewer than `banged`, not read.

**Reproduces small:** yes, the call of the specialised wrapper unbanged and its inlining banged, and the 8 instructions, at Storable; the shapes are a class over two phantom types rather than type-level lists, and ShapedU is not modelled.

### O24. Strict-constructor wrappers are inlined only in the final phase, so a bang that puts a case at the head of a method's unfolding can move that evaluation ahead of the wrapper's strict fields, as under orthotope's `badShape` guard, and the code generated after it changes; equal Core can compile to different code too, by the order of uniques

**Rule.** The wrapper `$WT` of a constructor with strict fields, one of them unpacked (A25), as `-O` unpacks `T`'s `!Int`, is inactive until the final phase (`dataConWrapperInlinePragma` with `activateDuringFinal`, [compiler/GHC/Types/Id/Make.hs#L791][g476]; Note [Activation for data constructor wrappers], [#L943][g179]). Until then `$WT ss 0 v` is a call of a strict function, and `rebuildCall` simplifies each strict argument with a `StrictArg` continuation when case-of-case is on ([compiler/GHC/Core/Opt/Simplify/Iteration.hs#L2490][g65], its guard `isStrictArgInfo fun_info` at [#L2494][g477]), so an argument headed by a `case` has the call pushed into its alternative and is evaluated before the call, ahead of the wrapper's own `case` on `ss`, which appears only when the wrapper is inlined. The bang gives the boxed instance's `vGenerate` the unfolding `\ irred a1 b -> case a1 of a2 { I# ipv -> new ... }`, where the point-free method is the alias `$sgenerate`, a call: so in the row, under orthotope's `badShape` guard, the banged build evaluates the generated vector's length `s` before the strides `ss`, the point-free one after. Without the guard both evaluate the strides first: the gentle run, case-of-case off, already resolves the row's match on `generate`'s result as a known constructor through the inactive wrappers `$WA` and `$WT` (`rebuildCase`, [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L3258][g478], its `exprIsConApp_maybe` at [#L3268][g158]; Note [exprIsConApp_maybe on data constructors with wrappers], [compiler/GHC/Core/SimpleOpt.hs#L1314][g183]), which floats the strict fields' evaluations in field order, the shape, the strides, then the vector, whose banged unfolding evaluates the length: `case sh of wild { __DEFAULT -> case case ds of { (s, ss1) -> ss1 } of wild { __DEFAULT -> case case case ds of { (s, ss1) -> s } of a2 { I# ipv ->`. Under the guard the match scrutinises the guard's `case`, which the gentle run leaves unpushed (`simplExprF1` with `seCaseCase` off, [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L1285][g66]), so its output keeps `case ds of { T st bx v ->`, and phase 2's run resolves it with the bang's case ahead of the fields, `case lvl of { False -> case ds of { (s, ss1) -> case s of a2 { I# ipv -> case eta of wild { __DEFAULT -> case ss of wild { __DEFAULT ->` (`~/r/horde-ad/dist-inlcat/cases/O24-guard-delays-known-constructor`, the repro's `split-banged` and `guard-banged` with `-dverbose-core2core`); which step of that run moves the bang's case outside was not traced. That order is the Core's one difference; the code generator then lays out the stack and assigns registers differently in the code after it, a swap through a stack slot moving from one block to another and one register-to-register `mov` added in another, the same hunks as in orthotope's binaries. Possibly related, unconfirmed: GHC [#27742](https://gitlab.haskell.org/ghc/ghc/-/work_items/27742), where the linear allocator's assignment follows the order in which values are first defined; the allocator's source was not read here. No patch of the working tree bears on it.

Code generation also depends on what Core does not show: STG-to-Cmm keeps each local variable's unique, and code generation orders by them in two places. Cmm stack layout gives the live variables of a return point their stack slots in the order of their uniques: `allocate` ([compiler/GHC/Cmm/LayoutStack.hs#L726][g479]) takes them as `Set.elems live` ([#L732][g480]), a `Set LocalReg` (`LocalRegSet`, [compiler/GHC/Cmm/Expr.hs#L342][g481]) ordered by unique (`instance Ord LocalReg`, [compiler/GHC/Cmm/Reg.hs#L127][g482]); a variable that stays in the slot it held at the previous return point is not stored again, one given another slot is stored, with a register move to free it. The linear register allocator traverses its assignment in unique order when it picks a register to spill (`allocRegsAndSpill_spill`, [compiler/GHC/CmmToAsm/Reg/Linear.hs#L935][g483]) and when it builds the moves at a block join (`makeRegMovementGraph`, [compiler/GHC/CmmToAsm/Reg/Linear/JoinToTargets.hs#L246][g484], its traversal at [#L247][g485]), both citing Note [Unique Determinism and code generation] ([compiler/GHC/Types/Unique.hs#L456][g486]). A Core dump numbers names in order of appearance and suppresses or hides the uniques' order, so two programs with equal Core can compile to different code; `-fobject-determinism` renames the uniques of each Cmm chunk deterministically before code generation (Note [Object determinism], [compiler/GHC/StgToCmm.hs#L150][g487]), and then they compile alike. A source change elsewhere, such as in an imported unfolding, can reorder the uniques of an unchanged function. An offset to every unique (`-dinitial-unique`) keeps their order and changes nothing; `-dunique-increment=-1` reverses it. No patch of the working tree bears on it. This is not the row's case: its Core differs (Seen); the second repro shows the rule.

**Seen.** NBg3 (C8's code with the boxed instance's `vGenerate`, `vUpdate`, `vMaximum` and `vMinimum` and the Storable instance's `vMaximum` and `vMinimum` banged, `vGenerate !a b = V.generate a b`) against C8, summed boxed `generate` at the empty size 2 instructions a call more, at equal bytes, read as register allocation at equal Core. The Core is not equal: in NBg3's `OpsDynamic`, the two summed boxed `generate` rows `$wlvl225` and `$wlvl381` read `case lvl1127 of { False -> case ds18 of { (s, ss3) -> case s of { I# ipv -> case ss2 of wild14 { __DEFAULT ->`, where C8's evaluate `case ss2` before `case s`; the interface of Dynamic's `$cvGenerate` is `Data.Vector.$sgenerate @a` in C8 and `\ ... (a1 :: Int) (b :: Int -> a) -> case a1 of a2 { I# ipv -> Data.Vector.Generic.new ...` in NBg3. In orthotope's binaries (`~/r/horde-ad/dist-inlcat/cases/O24-vgenerate-bang-evaluation-order/orthotope-binaries.sh`, run by `post`), the cell `Dynamic/generate/empty/strided/boxed` summed takes 396.0 instructions a call in C8 and 398.0 in NBg3; NBg3's row has an extra entry block evaluating a field (`movq $0x13cc840,0x0(%rbp)`, `mov 0x7(%rbx),%rbx`), and its hottest block, at `0x13ccb4c`, five moves where C8's, at `0x13cc884`, has four. In the dump builds of C8 and NBg3 that cell is the row `lvl2005`, its worker `$wlvl225`, and the case order is the one hunk by which the two builds' `$wlvl225` differ once local names are numbered out; the same cell takes 396.12 instructions a call at C8 and 398.12 at NBg3 (Ranked 412.12 and 414.12, Shaped 331.12 and 333.11). Callgrind on the empty cell (the scripts and their outputs in `~/r/horde-ad/dist-inlcat/cases/O24-equal-core-unique-order/asm/`) gives 379.04 instructions a call in the binary's own code at C8 and 381.04 at NBg3, and every block whose instructions differ lies in the row's code (the last four pairs its block listing prints are one library return sequence at moved addresses, mispaired): two entry blocks trade two moves, a spill slot of the C stack moves (`0x68(%rsp)` against `0x60(%rsp)`), and of the two loops the summing runs twice a call (`sum sh` and `sum st` over the two-element shape and strides) one stores a value more to the Haskell stack each iteration, NBg3's block of 12 instructions against C8's 11:

```
C8                                    NBg3
movq $A,-0x10(%rbp)                   movq $A,-0x10(%rbp)
mov %rbx,%rax                         mov %rbx,%rdi
mov 0x6(%rdx),%rbx                    mov 0x6(%rcx),%rbx
mov 0xe(%rdx),%rdx                    mov 0xe(%rcx),%rcx
mov %rdx,-0x8(%rbp)                   mov %rcx,-0x8(%rbp)
mov %rcx,0x0(%rbp)                    mov %rdx,0x0(%rbp)
mov %rax,0x8(%rbp)                    mov %rax,0x8(%rbp)
                                      mov %rdi,0x10(%rbp)
mov %rsi,0x18(%rbp)                   mov %rsi,0x18(%rbp)
```

The store is relative to `%rbp`, the Haskell stack, so Cmm's stack layout put it there, not a spill of the register allocator, which spills to the C stack; orthotope's Cmm does not survive to show it. Another bang on a `Vector` method moves code the same way: `vFromListN !a b`, in R against vec (the eta pass's forms), moves the join point finishing `traverseT`'s result out of `runRW#` to enclose `getStridesT` and the shape's product, 14 instructions a call more at forced Dynamic empty Unboxed `traverseA`, and at the large size one an element more over a fill loop whose Core is equal (`$wfoldlM'_loop`), the walk over the list of elements pushing its frame below the stack pointer where vec's reuses a slot of the fill loop's frame, 38 instructions an element against 37. And `vUpdate`'s bang (orthotope's commit "Make six Vector methods and the Shaped reshape strict where it gains": "the summing loop, whose Core does not change, compiled with one register swap through the stack fewer an element") leaves a summing loop's Core equal and runs it at 22 instructions an iteration against C8's 25, C8 swapping two registers through a stack slot, `mov %rcx,0x70(%rsp); mov %rbx,%rcx; mov 0x70(%rsp),%rbx`; where this swap was read in C8's `OpsDynamic.o`, it sits on the edge from a summing loop's per-element return point into its header, which holds the counter in another register, a return continuation entering a loop as in GHC [#27800](https://gitlab.haskell.org/ghc/ghc/-/work_items/27800) (inferred from the assembly); in the build of its parent, "Leave the Storable force out of line in Dynamic and Ranked", orthotope's callgrind has summed boxed Dynamic `update2000` at `[3, 3]` run the same three instructions through `0x70(%rsp)` on each of its nine passes; and the allocator breaks such a cycle of moves through a spill slot by design (`handleComponent` in `GHC.CmmToAsm.Reg.Linear.JoinToTargets`).

**Repro** (`~/r/horde-ad/dist-inlcat/cases/O24-vgenerate-bang-evaluation-order`, variants `pointfree` and `banged` (`-DBANG`); `split-pointfree` and `split-banged` (`-DSPLIT`, the class with orthotope's element constraint in `Lib`, the instance in `Inst`); `guard-pointfree` and `guard-banged` (`-DSPLIT -DGUARD`, orthotope's `badShape` guard around `generate`'s body); `post` compares the pairs' Core and runs the script reading orthotope's binaries; `measure.sh N` gives instructions and bytes a summed call from N and 2N iterations): orthotope's boxed instance's `vGenerate`, its `generateT` and `getStridesT`, and the benchmark's summed `generate` row at `[0, 3]`, summed by the benchmark's `Summed` for an array, whose sums over the two-element shape and stride lists are loops run twice a call.

```haskell
{-# LANGUAGE BangPatterns, CPP, TypeFamilies #-}
-- orthotope's generate at NBg3, cut: the boxed instance's vGenerate,
-- point-free (C8) or banged on its length (NBg3), generateT and getStridesT.
-- SPLIT: the class with orthotope's element constraint here, the instance
-- in Inst, as orthotope's Internal and Dynamic hold them.
module Lib (Vec (..), None, T (..), A (..), generate) where

#if !defined(SPLIT)
import qualified Data.Vector as V
#endif
import Data.Kind (Constraint, Type)
import GHC.Exts (build)

class None a
instance None a

#if defined(SPLIT)
class Vec v where
  type VecElem v :: Type -> Constraint
  vGenerate :: VecElem v a => Int -> (Int -> a) -> v a
#else
class Vec v where
  vGenerate :: Int -> (Int -> a) -> v a

instance Vec V.Vector where
  {-# INLINE vGenerate #-}
#if defined(BANG)
  vGenerate !a b = V.generate a b
#else
  vGenerate = V.generate
#endif
#endif

-- A view: strides, offset, vector; an array: shape and view.
data T v a = T ![Int] !Int !(v a)
data A v a = A ![Int] !(T v a)

getStridesT :: [Int] -> [Int]
getStridesT [] = [1]
getStridesT (s : ss) = case getStridesT ss of
  r@(m : _) -> let !x = s * m in x : r
  [] -> []

{-# INLINE generateT #-}
#if defined(SPLIT)
generateT :: (Vec v, VecElem v a) => [Int] -> ([Int] -> a) -> T v a
#else
generateT :: Vec v => [Int] -> ([Int] -> a) -> T v a
#endif
generateT sh f = T ss 0 $ vGenerate s g
  where s : ss = getStridesT sh
        g i = f (build $ \ cons nil ->
                   let go [] !_ = nil
                       go (n : ns) !j = case quotRem j n of
                         (q, r) -> q `cons` go ns r
                   in  go ss i)

{-# INLINE generate #-}
#if defined(SPLIT)
generate :: (Vec v, VecElem v a) => [Int] -> ([Int] -> a) -> A v a
#else
generate :: Vec v => [Int] -> ([Int] -> a) -> A v a
#endif
#if defined(GUARD)
generate sh | badShape sh = error ("generate: bad shape " ++ show sh)
            | otherwise = A sh . generateT sh

-- orthotope's (Data/Array/Internal.hs at NBg3).
badShape :: [Int] -> Bool
badShape = go 1
  where go !_ [] = False
        go !n (s : ss) | s < 0 = True
                       | s == 0 = any (< 0) ss
                       | n > maxBound `quot` s = any (< 0) ss || 0 `notElem` ss
                       | otherwise = go (n * s) ss
#else
generate sh = A sh . generateT sh
#endif
```

```haskell
{-# LANGUAGE BangPatterns, CPP, TypeFamilies #-}
-- SPLIT: the boxed instance in a module of its own, as in orthotope's
-- Dynamic, its element constraint None; without SPLIT, empty.
module Inst () where

#if defined(SPLIT)
import qualified Data.Vector as V
import Lib

instance Vec V.Vector where
  type VecElem V.Vector = None
  {-# INLINE vGenerate #-}
#if defined(BANG)
  vGenerate !a b = V.generate a b
#else
  vGenerate = V.generate
#endif
#endif
```

```haskell
{-# LANGUAGE BangPatterns, ExistentialQuantification #-}
module Main (main) where

import qualified Data.Vector as V
import GHC.Exts (inline)
import Inst ()
import Lib
import System.Environment (getArgs)

-- orthotope's benchmark row with its summed reading: the operation inlined
-- into a closure that sums its result, applied by the harness.
data Call = forall a b. Call (a -> b) a (a -> Double)

{-# INLINE call #-}
call :: (a -> b) -> (b -> Double) -> a -> Call
call f s x = Call f x (\ y -> s (inline f y))

{-# OPAQUE pass #-}
pass :: Int -> Call -> Call
pass _ c = c

-- The benchmark's Summed for an array (bench/Summed.hs at NBg3): its
-- shape, strides and offset summed, and its elements, each forced.
summed :: A V.Vector Double -> Double
summed (A sh (T st o v)) = fromIntegral (sum sh + sum st + o) + sumVec v

sumVec :: V.Vector Double -> Double
sumVec v = go 0 0
  where
    !len = V.length v
    go !i !acc | i >= len = acc
               | otherwise = go (i + 1) (acc + V.unsafeIndex v i)

main :: IO ()
main = do
  [ns] <- getArgs
  let n = read ns :: Int
      -- The empty size, [0, 3], as the benchmark's generate row has it.
      row = call (\ k -> generate [0, 3] (\ ix -> fromIntegral (sum ix + k) :: Double))
                 summed (0 :: Int)
      run (Call _ x s) = s x
      go :: Int -> Double -> Double
      go 0 !acc = acc
      go k !acc = go (k - 1) (acc + run (pass k row))
  print (go n 0)
```

`Main.dump-simpl`, whitespace collapsed, the row's head: `guard-pointfree` `$wrow = \ y -> case lvl18 of { False -> case ss of wild1 { __DEFAULT -> case ds of { (s, ss1) -> case s of { I# ipv ->`; `guard-banged` `$wrow = \ y -> case lvl18 of { False -> case ds of { (s, ss1) -> case s of { I# ipv -> case ss of wild1 { __DEFAULT ->`; `~/r/horde-ad/dist-inlcat/cases/O24-vgenerate-bang-evaluation-order/out/head/guard-banged/diff.txt` `Main.dump-simpl against guard-pointfree: 4 diff lines`, and `split-banged`'s `0 diff lines`. `Main.dump-asm`: `guard-pointfree` `movq %rbx,96(%rsp) movq %rcx,%rbx movq 96(%rsp),%rcx` before a compare where `guard-banged` has `cmpq %rax,%rdx` alone; and in another block three moves against four, as in orthotope's hottest block:

```
guard-pointfree: movq %rax,104(%rsp)  movq %rbx,%rax  movq 104(%rsp),%rbx
guard-banged:    movq %rax,96(%rsp)  movq %rcx,%rax  movq %rbx,%rcx  movq 96(%rsp),%rbx
```

`~/r/horde-ad/dist-inlcat/cases/O24-vgenerate-bang-evaluation-order/out/head/guard-banged/orthotope.txt`, from orthotope's binaries, where NBg3 is labelled N3: `C8: 396.0 instructions a call`, `N3: 398.0 instructions a call`, and the hottest block, `C8 13cc884 mov %rax,0x68(%rsp) ... C8 13cc891 mov %rax,%rdi` against `N3 13ccb4c mov %rax,0x60(%rsp) N3 13ccb51 mov %rcx,%rax N3 13ccb54 mov %rbx,%rcx N3 13ccb57 mov 0x60(%rsp),%rbx N3 13ccb5c mov %rcx,%rdi`.

`measure.sh 2000000`:

```
pointfree: 304.9 instructions, 56.0 bytes a call
banged: 304.9 instructions, 56.0 bytes a call
split-pointfree: 304.9 instructions, 56.0 bytes a call
split-banged: 304.9 instructions, 56.0 bytes a call
guard-pointfree: 384.9 instructions, 56.0 bytes a call
guard-banged: 388.9 instructions, 56.0 bytes a call
```

The guard pair costs 4 instructions a call at equal bytes, orthotope's pair 2; where in the row the 4 are executed was not measured.

A second repro (`~/r/horde-ad/dist-inlcat/cases/O24-equal-core-unique-order`, variants `fwd` (`vGenerate` as at C8), `rev` (the same with `-dinitial-unique=1099511627776 -dunique-increment=-1`, the order of uniques reversed), `fwd-od` and `rev-od` (each with `-fobject-determinism`) and `bang` (`-DBANG`, NBg3's bang in `vGenerate`); `post` compares the pairs' Core, Cmm and assembly with labels and local names numbered out, into `~/r/horde-ad/dist-inlcat/cases/O24-equal-core-unique-order/out/head/fwd/same.txt`; `measure.sh N` gives instructions and bytes a call from N and 2N iterations): orthotope's generic `generateT`, its `getStridesT` and the boxed instance's `vGenerate`, the benchmark's summed row at the empty size `[0, 3]`.

```haskell
{-# LANGUAGE BangPatterns #-}
-- orthotope's generate at NBg3, cut: the class of vectors with
-- its vGenerate (Internal), getStridesT and generateT (Internal) as they
-- are there, and the generic array's generate (DynamicG).
module Lib (Vec (..), T (..), GA (..), generateG) where

import GHC.Exts (build)

class Vec v where
  vGenerate :: Int -> (Int -> a) -> v a

-- A view: strides, offset, vector; the generic array: shape and view.
data T v a = T ![Int] !Int !(v a)
data GA v a = GA ![Int] !(T v a)

-- orthotope's: the stride of each dimension, the total length first.
getStridesT :: [Int] -> [Int]
getStridesT [] = [1]
getStridesT (s : ss) = case getStridesT ss of
  r@(m : _) -> let !x = s * m in x : r
  [] -> []

{-# INLINE generateT #-}
generateT :: Vec v => [Int] -> ([Int] -> a) -> T v a
generateT sh f = T ss 0 $ vGenerate s g
  where s : ss = getStridesT sh
        g i = f (build $ \ cons nil ->
                   let go [] !_ = nil
                       go (n : ns) !j = case quotRem j n of
                         (q, r) -> q `cons` go ns r
                   in  go ss i)

{-# INLINE generateG #-}
generateG :: Vec v => [Int] -> ([Int] -> a) -> GA v a
generateG sh | any (< 0) sh = error "generate: bad shape"
             | otherwise = GA sh . generateT sh
```

```haskell
{-# LANGUAGE BangPatterns, CPP #-}
-- orthotope's boxed instance and array (Dynamic): vGenerate as at C8, or
-- with NBg3's bang on the length (BANG).
module B (A (..), generate) where

import qualified Data.Vector as V
import Lib

instance Vec V.Vector where
  {-# INLINE vGenerate #-}
#if defined(BANG)
  vGenerate !a b = V.generate a b
#else
  vGenerate = V.generate
#endif

newtype A a = A (GA V.Vector a)

{-# INLINE generate #-}
generate :: [Int] -> ([Int] -> a) -> A a
generate sh = A . generateG sh
```

```haskell
{-# LANGUAGE BangPatterns, ExistentialQuantification #-}
module Main (main) where

import B
import qualified Data.Vector as V
import GHC.Exts (inline)
import Lib
import System.Environment (getArgs)

-- orthotope's benchmark row, its summing applied by the harness.
data Call = forall a b. Call (a -> b) a (a -> Double)

{-# INLINE call #-}
call :: (a -> b) -> (b -> Double) -> a -> Call
call f s x = Call f x (\ y -> s (inline f y))

{-# OPAQUE pass #-}
pass :: Int -> Call -> Call
pass _ c = c

-- The bench's sumT: the shape, strides and offset, then each element.
summedA :: A Double -> Double
summedA (A (GA sh (T st o v))) = fromIntegral (sum sh + sum st + o) + go 0 0
  where !len = V.length v
        go :: Int -> Double -> Double
        go !i !acc | i >= len = acc
                   | otherwise = go (i + 1) (acc + V.unsafeIndex v i)

main :: IO ()
main = do
  [ns] <- getArgs
  let n = read ns :: Int
      -- the empty size of orthotope's generate row: [0, 3]
      row = call (\ k -> generate [0, 3] (\ ix -> fromIntegral (sum ix + k) :: Double))
                 summedA (0 :: Int)
      run (Call _ x s) = s x
      go :: Int -> Double -> Double
      go 0 !acc = acc
      go k !acc = go (k - 1) (acc + run (pass k row))
  print (go n 0)
```

That file: `fwd rev Main.dump-simpl: equal`, `fwd rev Main.dump-cmm: different`, `fwd rev Main.dump-asm: different`; `fwd-od rev-od Main.dump-cmm: equal`, `fwd-od rev-od Main.dump-asm: equal`; `fwd bang Main.dump-simpl: different`. `Main.dump-cmm`, a return point's frame: `fwd` `rep: StackRep [True, True, False]`, `rev` `rep: StackRep [False, True, True]`, `rev-od` as `fwd`. `Main.dump-simpl`, `fwd` `case ds of { (s, ss1) -> case ss of wild1 { __DEFAULT -> case s of { I# ipv ->`, `bang` `case ds of { (s, ss1) -> case s of { I# ipv -> case ss of wild1 { __DEFAULT ->`.

`measure.sh 1000000`:

```
fwd: 391.84 instructions, 56.0 bytes a call
rev: 386.84 instructions, 56.0 bytes a call
fwd-od: 391.84 instructions, 56.0 bytes a call
rev-od: 391.84 instructions, 56.0 bytes a call
bang: 393.84 instructions, 56.0 bytes a call
```

Reversing the uniques' order costs nothing in bytes and saves 5 instructions a call at equal Core; `-fobject-determinism` compiles both orders to the code of 391.84. NBg3's `vGenerate` bang costs this model 2 instructions a call, orthotope's figure, through Core, as in the first repro: it moves the length's evaluation ahead of the strides'.

**Reproduces small:** yes: the bang's reordering of the length and the strides in the row's Core, under the guard alone, which delays the known-constructor step past the gentle run, and the downstream register assignment, the same hunks as in orthotope's binaries. And apart from this row, by the second repro, equal Core compiled to different code by the order of uniques alone, its stack layout and registers, and the renaming that removes it; tried there: `vGenerate a b = V.generate a b` and `vGenerate a !b = V.generate a b`, each giving Core and assembly identical to C8's form, and offsets of `-dinitial-unique` from 0 to 100000, the assembly identical, an offset keeping the order. `vUpdate`'s register swap, not tried.

### O25. INLINABLE in place of INLINE on a point-free wrapper trades two unrelated effects by kind: the boxed wrapper, not overloaded, is called out of line through its cast worker, and the Storable one, specialised in the client, escapes a re-boxing its inlined copy pays

**Rule.** Two single-binding rules of opposite sign make the trade. Boxed: a wrapper with no class constraint gives the client nothing to specialise, and its right-hand side, a newtype constructor composed with the generic function, is split by the cast worker/wrapper (U17; `tryCastWorkerWrapper`, [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L617][g218]), a stable unfolding moving to the worker `scalarB1` (`Inline: [2]`, `StableSystem <1,TrueFalse>` in `Lib.iface`) and the binding left without a pragma and with a vanilla unfolding ``scalarB1 `cast` ...``. The client's row `\ x -> scalarB x` meets `scalarB1` while its unfolding is inactive and is eta-reduced to it; afterwards the lone occurrence, with no argument, in a boring context, is refused by `tryUnfolding` ([compiler/GHC/Core/Opt/Simplify/Inline.hs#L310][g5], an `UnfWhen` unfolding inlining only on `boring_ok || some_benefit`), so the row runs Lib's compiled worker, polymorphic in the element, whose fill loop boxes its counter, where the INLINE body inlined into the client loops on `Int#`. Storable: the wrapper is overloaded, so INLINABLE gives a client specialisation `$sscalarS1`, which builds the `PlainPtr` once and returns it; under INLINE the body inlined into the row's lambda is split by demand worker/wrapper with nested CPR, its worker building a `PlainPtr` for `touch#` and returning the byte array unboxed, the wrapper building a second (U20).

**Seen.** Orthotope's V2b (`scalar` INLINABLE alone in every module) against C8: bytes move at the `scalar` row alone, forced, 16 a call more boxed and 16 less Storable; instructions in V2 (`sumA` and `scalar` INLINABLE): boxed 4.1 to 4.8% more, Storable 1% fewer. The surviving binaries give, at 20000 calls (`--iters 20000`, forced, small size; the row exists at the strided view alone), C8 against V2b: Dynamic, Ranked and Shaped boxed 160, 160 and 136 bytes a call against 176, 176 and 152; Storable 176, 176 and 152 against 160, 160 and 136; Unboxed 144, 144 and 120 in both. C8's `OpsDynamic` Core has both rows inlined: the boxed `lvl496` storing its argument unevaluated, the Storable `lvl1304` writing a pinned array; V2b's Core does not survive. Its binary, read by callgrind and `objdump` at Dynamic `scalar` small strided: boxed, C8's inlined row allocates the array and then `Vector`, `T` and `A`, and V2b's calls the library's `Data.Array.Internal.Dynamic.scalar1` out of line, whose generic `unstream` loop allocates the same and an `I#` for its counter, read back as the vector's length after the loop: the 16 bytes; Storable, C8's inlined row builds a `PlainPtr` that only the fill loop's `touch#` keeps and a second for the result, after a join point whose worker took the buffer apart, and V2b's out-of-line `$sscalar2` builds one: the 16 fewer.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/O25-scalar-inlinable-trade`, variants `inline` (C8), by `-DINL`, `inlinable` (V2b) and `check` (`inlinable` with `-dinline-check scalarB1`); `run` is `boxed 1000000`; `measure.sh N ROW`, `ROW` being `boxed` or `Storable`): orthotope's `Vector` class with its element constraint (`None` for boxed vectors, `Storable`), the point-free `scalarT`, the generic `scalar` and its two point-free wrappers, INLINE or INLINABLE together, and `NF` standing for `NFData`, each row's result forced.

```haskell
{-# LANGUAGE CPP, TypeFamilies, ConstraintKinds, FlexibleContexts, FlexibleInstances, UndecidableSuperClasses #-}
-- Orthotope's scalar: the Vector class, the generic scalar and its boxed and
-- Storable wrappers, cut down; NF stands for NFData.
module Lib (module Lib) where

import Data.Kind (Constraint, Type)
import qualified Data.Vector as V
import qualified Data.Vector.Storable as VS

class Vector v where
  type VecElem v :: Type -> Constraint
  vSingleton :: VecElem v a => a -> v a
  vToList :: VecElem v a => v a -> [a]

class None a
instance None a

instance Vector V.Vector where
  type VecElem V.Vector = None
  {-# INLINE vSingleton #-}
  vSingleton = V.singleton
  {-# INLINE vToList #-}
  vToList = V.toList

instance Vector VS.Vector where
  type VecElem VS.Vector = VS.Storable
  {-# INLINE vSingleton #-}
  vSingleton = VS.singleton
  {-# INLINE vToList #-}
  vToList = VS.toList

data T v a = T ![Int] !Int !(v a)
data G v a = A ![Int] !(T v a)
newtype B a = B (G V.Vector a)
newtype S a = S (G VS.Vector a)

{-# INLINE scalarT #-}
scalarT :: (Vector v, VecElem v a) => a -> T v a
scalarT = T [] 0 . vSingleton

-- The generic module's scalar and the wrappers', INLINE (C8) or INLINABLE (V2b).
#ifdef INL
{-# INLINE gScalar #-}
{-# INLINE scalarB #-}
{-# INLINE scalarS #-}
#else
{-# INLINABLE gScalar #-}
{-# INLINABLE scalarB #-}
{-# INLINABLE scalarS #-}
#endif
gScalar :: (Vector v, VecElem v a) => a -> G v a
gScalar = A [] . scalarT

scalarB :: a -> B a
scalarB = B . gScalar

scalarS :: VS.Storable a => a -> S a
scalarS = S . gScalar

class NF a where
  rnf :: a -> ()
instance NF Double where
  {-# INLINE rnf #-}
  rnf x = x `seq` ()
instance NF a => NF (B a) where
  {-# INLINABLE rnf #-}
  rnf (B (A sh (T st _ v))) = sum sh `seq` sum st `seq` foldr seq () (map rnf (vToList v))
instance NF (S a) where
  {-# INLINABLE rnf #-}
  rnf (S (A sh (T st _ _))) = sum sh `seq` sum st `seq` ()
```

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import System.Environment (getArgs)
import Lib

-- The benchmark's forced reading: the call's result forced to normal form.
data Call = forall a b. NF b => Call String (a -> b) a

{-# NOINLINE rows #-}
rows :: [Call]
rows = [ Call "boxed" (\ x -> scalarB x) x0
       , Call "Storable" (\ x -> scalarS x) x0 ]
  where x0 = 1.5 :: Double

-- Opaque, so that each iteration calls anew.
{-# OPAQUE pass #-}
pass :: Int -> a -> a
pass _ x = x

main :: IO ()
main = do
  [nm, ns] <- getArgs
  let reps = read ns :: Int
  case [ c | c@(Call nm' _ _) <- rows, nm' == nm ] of
    Call _ f x : _ ->
      let loop :: Int -> ()
          loop 0 = ()
          loop r = rnf (f (pass r x)) `seq` loop (r - 1)
      in print (loop reps)
    [] -> error nm
```

Boxed, `inlinable`: ``rows5 = Call (C:NF $s$fNFB_$crnf) rows4 (scalarB1 `cast` <Co:6>) x0`` (`Main.dump-simpl`); `Lib.iface` gives `scalarB` ``Unfolding: Core: <vanilla> scalarB1 `cast` ...`` and `scalarB1` `Inline: [2]`, `StableSystem <1,TrueFalse>`; `check`'s `build.log` reads `Inactive unfolding: scalarB1`, then at the row `arg infos []`, `interesting continuation BoringCtxt`, `guidance ALWAYS_IF(arity=1,unsat_ok=True,boring_ok=False)`, `ANSWER = NO`. `Lib.dump-simpl`'s `scalarB1` loops by `jump foldlM'_loop SPEC (I# (+# ipv6 1#)) False ...`; `inline`'s client loop by `jump $wfoldlM'_loop SPEC (+# ww 1#) False ...`. Storable, `inline`: the worker binds `let { ipv2 = PlainPtr ipv1 } in` for `touch#` and returns `(# 0#, ww1, ipv5, ipv1 #)`, the wrapper building ``(A [] (T [] ww1 (Vector ww2 ww3 (PlainPtr ww4)))) `cast` <Co:3>``; `inlinable`: `$sscalarS1` binds `let { ipv5 = PlainPtr ipv2 } in` and returns through a join point, `join { $w$j ww = A [] (T [] 0# (Vector ww ipv3 ipv5)) }`. By `measure.sh 1000000`, twice alike: boxed 228.4 instructions and 216.0 bytes a call under INLINE, 240.4 and 232.0 under INLINABLE; Storable 331.1 and 232.0 under INLINE, 327.6 and 216.0 under INLINABLE.

`scalarB1`'s compiled loop boxes its counter because worker/wrapper's split is undone (`~/r/horde-ad/dist-inlcat/cases/O25-worker-inlined-back`, the repro's `inlinable` with `-dinline-check $wscalarB`): inside the worker `$wscalarB` the loop is `joinrec { $wfoldlM'_loop ds4 ww s6 eta` on `Int#` (`Lib.dump-worker-wrapper`), but the worker's INLINABLE unfolding, simplified at each iteration (U10), shrinks from `IF_ARGS [0] 170 10` through `IF_ARGS [0] 130 10` to `IF_ARGS [0] 100 10`, and at that size it is inlined into its wrapper (`adjusted size = 70 ANSWER = YES`, after `140` and `100` refused; `build.log`), so the loop is rebuilt from the template after worker/wrapper, which `-O` does not run again, the late round running only under `late_dmd_anal` ([compiler/GHC/Core/Opt/Pipeline.hs#L321][g367]): `jump foldlM'_loop SPEC (I# (+# ipv6 1#)) False` (`Lib.dump-simpl`), and no `$wscalarB` is left.

**Reproduces small:** yes, the bytes in both directions and the signs of the instructions, and the boxed counter, its worker inlined back into its wrapper; and orthotope's `Data.Array.Internal.Dynamic.scalar1` at V2b loses its unboxed loop the same way (V2b's library rebuilt with `-ddump-worker-wrapper -dinline-check $wscalar`, its `scalar1` compiled byte for byte as in the measured binary): worker/wrapper gives it a worker `$wscalar` looping by `$wfoldlM'_loop` on `Int#`, refused at `IF_ARGS [0] 170 10` and `IF_ARGS [0] 130 10` and inlined into its wrapper at `IF_ARGS [0] 100 10`, `adjusted size = 70`, `ANSWER = YES`, as the repro's `$wscalarB` is, and its final Core keeps no `$wscalar` and loops by a `foldlM'_loop` taking `(z :: Int)`; Ranked's and Shaped's boxed `scalar1` likewise. With `-flate-dmd-anal` the late worker/wrapper splits the rebuilt loop again, and the repro's `scalarB1` loops by `$wfoldlM'_loop` on `Int#` (`~/r/horde-ad/dist-inlcat/cases/O25-worker-inlined-back`, variant `late`). The worker inlined back is filed as GHC [#27984](https://gitlab.haskell.org/ghc/ghc/-/work_items/27984), `docs/ghc-issue-inlinable-worker-inlined-back.md` in horde-ad.

### O26. A dictionary of a single-method class, a function, is inlined unconditionally where its one call sits in a lambda and applies it to a value, and stays out of line, split by worker/wrapper, while several rows call it; in orthotope's build the one call left stays a call (not reproduced small)

**Rule.** A top-level binding with one occurrence, inside a lambda, in an interesting context (applied to a value argument), whose right-hand side is a lambda, is inlined there unconditionally before its right-hand side is simplified: `preInlineUnconditionally`, [compiler/GHC/Core/Opt/Simplify/Utils.hs#L1665][g360], its `one_occ` case for `IsInsideLam` and `IsInteresting` at [#L1701-1703][g488] requiring `canInlineInLam rhs` ([#L1733-1741][g489], its `Cast` case at [#L1734][g490] looking through to the lambda); called for a top-level pair from `simplRecOrTopPair`, [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L282][g491], which logs `SimplBindr:inline-uncond1` ([#L291][g492]). A dictionary of a single-method class is a newtype of its method, so `$fSummedEither d1 d2` becomes a function of the `Either`, and is kept out of line and split by worker/wrapper while more than one row calls it; this rule is what takes it once the rows are merged.

**Seen.** Orthotope's edit CV, the class default `convertE x = Right $! convert x`, costs 40 bytes a call at summed boxed Dynamic and Ranked `convertE.unboxed`. In CV's `OpsDynamic.dump-simpl` the row's summing function `lvl2142` calls the conversion worker `$w$s$w$cconvert11` and then `$w$dSummed (Right (DG.A wild4 wild5))`, `$w$dSummed :: Either [Char] (IU.Array Double) -> Double#` (99 terms) being called there alone; at the tip the summing function, also named `lvl2142`, calls `$wlvl564`, which holds the Unboxed sum loop, and no top-level dictionary at that type exists. Both builds' `dump-simpl-stats` carry the grand totals alone, with equal tick counts on every `$dSummed`, and record no `PreInlineUnconditionally` of a `$w$dSummed`, so they do not place the step that differs; CV's runs all four iterations of every simplifier run in `OpsDynamic` (`SimplifierDone` 28), as E14's builds do. The difference is that in CV the call occurs twice. Once CSE has merged the three rows, the row's summing function, whose worker was inlined back into its worker/wrapper wrapper, holds the call both in its right-hand side and in its stable unfolding (inferred from the dumps). An occurrence in a stable unfolding counts as many (A16; Note [Occurrences in stable unfoldings and RULES]), so no unconditional inlining takes the call, and `callSiteInline` does not inline it either, at adjusted size 91 against the threshold of 90; Tidy then drops the unfolding, so the final dump shows one call (section 6, item 8).

**Repro** (`~/r/horde-ad/dist-inlcat/cases/O26-one-use-dictionary-argument-form`, variants `lazy`, `strict` and `trace`, the last strict with `-dverbose-core2core`; `run` is `convertE.unboxed 100000`): orthotope's `Convert` default, lazy or strict by `-DSTRICT`, at a boxed-to-Unboxed instance overloaded in the element, summed by the benchmark's `Summed` through its `call`, the row in three out-of-line row functions as orthotope's three sizes; `tried/` holds the form with two row functions.

```haskell
{-# LANGUAGE CPP, MultiParamTypeClasses, FlexibleInstances, BangPatterns, TypeFamilies, FlexibleContexts #-}
-- Orthotope's Convert and the benchmark's Summed and call, cut down.
module Lib (module Lib) where

import GHC.Exts (inline)
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Generic as VG

-- Strides, offset, vector; shape and view; boxed and Unboxed arrays.
data T v a = T ![Int] !Int !(v a)
data A v a = A ![Int] !(T v a)
newtype B a = B (A V.Vector a)
newtype U a = U (A VU.Vector a)

-- The class default, lazy as orthotope's or strict as its edit CV.
class Convert a b where
  convert :: a -> b
  convertE :: a -> Either String b
  {-# INLINE convertE #-}
#ifdef STRICT
  convertE x = Right $! convert x
#else
  convertE = Right . convert
#endif

-- A dense copy of the view.
convertT :: (VG.Vector v a, VG.Vector w b)
         => [Int] -> (v a -> w b) -> T v a -> T w b
convertT sh g (T _ o v) = T (tail (scanr (*) 1 sh)) 0 (g (VG.slice o (product sh) v))

instance (a ~ b, VU.Unbox a) => Convert (B a) (U b) where
  {-# INLINABLE convert #-}
  convert (B (A sh t)) = U (A sh (convertT sh VG.convert t))

class Summed b where
  summed :: b -> Double

{-# INLINE sumVec #-}
sumVec :: (VG.Vector v e, Summed e) => v e -> Double
sumVec v = go 0 0
  where
    !len = VG.length v
    go !i !acc | i >= len = acc
               | otherwise = go (i + 1) (acc + summed (VG.unsafeIndex v i))

instance Summed Double where
  {-# INLINE summed #-}
  summed = id
instance Summed Char where
  {-# INLINE summed #-}
  summed = fromIntegral . fromEnum
instance Summed a => Summed [a] where
  {-# INLINE summed #-}
  summed = sum . map summed
instance (Summed a, Summed b) => Summed (Either a b) where
  {-# INLINE summed #-}
  summed = either summed summed
instance (VU.Unbox a, Summed a) => Summed (U a) where
  {-# INLINE summed #-}
  summed (U (A sh (T st o v))) = fromIntegral (sum sh + sum st + o) + sumVec v

-- A row: the function, its input and the function's result summed.
data Call = forall a b. Call String (a -> b) a (a -> Double)

{-# INLINE call #-}
call :: Summed b => String -> (a -> b) -> a -> Call
call nm f x = Call nm f x (\ y -> summed (inline f y))
```

```haskell
{-# LANGUAGE BangPatterns, CPP #-}
module Main (main) where

import qualified Data.Vector as V
import System.Environment (getArgs)
import Lib

-- The benchmark's lists of rows, one a size, each out of line and taking
-- its form and view, as orthotope's OPS.
rowsLarge, rowsSmall, rowsEmpty :: Int -> Int -> [Call]
#define ROWS(NAME, K) \
{-# NOINLINE NAME #-}; \
NAME form view = \
  [ call "convert.unboxed" (\ a -> convert a :: U Double) t \
  , call "convertE.unboxed" (\ a -> convertE a :: Either String (U Double)) t ] \
  where t = B (A [K, form] (T [form, 1] view (V.fromList [1 .. fromIntegral (K * form)])))
ROWS(rowsLarge, 400)
ROWS(rowsSmall, 3)
ROWS(rowsEmpty, 0)

-- Opaque, so that each iteration sums anew.
{-# OPAQUE pass #-}
pass :: Int -> a -> a
pass _ x = x

main :: IO ()
main = do
  [nm, ns] <- getArgs
  let reps = read ns :: Int
  case [ c | c@(Call nm' _ _ _) <- rowsSmall 3 0 ++ rowsLarge 500 0 ++ rowsEmpty 3 0, nm' == nm ] of
    Call _ _ x s : _ ->
      let loop :: Int -> Double -> Double
          loop 0 !acc = acc
          loop r !acc = loop (r - 1) (acc + s (pass r x))
      in print (loop reps 0)
    [] -> error nm
```

Neither variant keeps the dictionary: `Main.dump-simpl` holds no `$dSummed` in either, and both allocate 53,709,456 bytes over the run's 100000 calls. The strict variant's route, in `trace`: worker/wrapper splits the dictionary, `$dSummed = \ ds1 -> case $w$dSummed ds1 of ww { __DEFAULT -> D# ww }` (`Main.dump-worker-wrapper`); CSE merges the three rows, leaving one `$wlvl` that calls the conversion worker and then ``$w$dSummed (Right ((A ww (T ww ww ((Vector ww ww ww) `cast` <Co:4>))) `cast` <Co:3>))`` (`Main.dump-cse`), the form CV's final Core keeps; and the next Simplifier inlines that one call, `SimplBindr:inline-uncond1 $w$dSummed` (`build.log`).

**Reproduces small:** no. The repro reaches CV's final form at its CSE pass and then inlines it, where CV does not, in the final Simplifier's first iteration at each cap tried (`~/r/horde-ad/dist-inlcat/cases/O26-iteration-cap`, the repro at `-fmax-simplifier-iterations=1`, `2` and `3`); and so does a second (`~/r/horde-ad/dist-inlcat/cases/O26-unsplit-summing`) whose summing function is floated out only after worker/wrapper and so stays unsplit, as CV's `lvl2142` does, at the default cap and at 1 or 2. Why CV's last Simplifier leaves the one call is not found. Tried: the arrays monomorphic in the element, one row function (the dictionary, used once, inlined into the row in both variants); two row functions of one argument (`~/r/horde-ad/dist-inlcat/cases/O26-one-use-dictionary-argument-form/tried/Main-two-rows.hs`) and three of two arguments, each also carrying the `convert.unboxed` row (the case's `Main.hs`), both taking the route above in both variants. Not tried: the benchmark's other rows at other `Either` types, and a module the size of `OpsDynamic` (78 MB of final Core), where a second live occurrence of `$w$dSummed` could last into the final run (not shown).

### O27. Inlined in the gentle run, an INLINE wrapper's body brings vector's size tests into a client before the first float-out, which lifts them to top-level `Bool`s that cost more to enter than the tests; a specialisation of the same body meets that float-out with the tests still in a call, and later tests a case-bound size

**Rule.** The first float-out runs after the gentle Simplifier and the specialiser and before any other Simplifier ([compiler/GHC/Core/Opt/Pipeline.hs#L202][g419], [#L206][g493], [#L208][g494]). The gentle run inlines an INLINE wrapper and, its dictionaries known, the element type's vector code with it, so vector's length checks in `basicUnsafeNew`, the count below 0 and above `maxBound` over the element's size, are comparisons on the size, a top-level value, each scrutinised by a `case`; after the next Simplifier each is a top-level `Bool`, the lazy pattern `n : st = getStridesT ss` a top-level pair, and the row enters each (which step of SetLevels lifts them was not read). An INLINABLE wrapper over a polymorphic element type is specialised in the client instead, and the specialised body meets the first float-out unsimplified, the element's `basicUnsafeNew` still a call; a later Simplifier inlines it, and the one after evaluates the size and the strides' head by cases at the function's head and tests the case-bound size, which the late float-out leaves in place: the tests scrutinise a size bound by a `case` on a top-level thunk inside `runRW#`'s lambda, and `lvlCase` floats a single-alternative `case` only if its scrutinee is in head normal form and its destination is not the top level ([compiler/GHC/Core/Opt/SetLevels.hs#L447][g495], [#L448][g496]; `~/r/horde-ad/dist-inlcat/cases/O27-case-bound-size`). E17's rule from the other side: there inlining exposes work that float-out saves, here what floats is a test cheaper than entering its result (O15 enters a floated constant the same way). The element type's polymorphism is needed: with the element fixed in the library, the INLINABLE template already holds vector's checks, and both forms float them.

**Seen.** VD, INLINE in place of INLINABLE on orthotope's Shaped, ShapedU and ShapedS `ravel` wrappers, carried by the pragma commit "Give each binding the pragma its kind calls for" against its parent, "Probe whether a client's call builds a Route, a Range or an Axes": forced Shaped `ravel` empty Unboxed 506.2 instructions a call at the parent and 528.1 at the commit, small Unboxed 1308.8 and 1330.7, empty Storable 587.1 and 594.8; by callgrind, `stg_IND_STATIC` 10 a call more, `False`'s entry 4, the pair's 2, `(:)`'s 2 fewer and the row's own code 8 more, the 22. The parent's out-of-line `OpsShaped.$w$s$wravel7` (`OpsShaped.dump-simpl`) reads `case OpsShaped.$s$wbroadcast_eta1 of { I# ipv3 -> case OpsShaped.$s$wfromList75 of { [] -> ...; : n15 st -> case n15 of { I# x30 -> runRW# ... (\ (s6 :: State# RealWorld) -> case <# ipv3 0# of { __DEFAULT -> case ># ipv3 1152921504606846975# of {`; the commit's row worker `$wlvl896` reads `case ds9 of { (n15, st) -> case n15 of { I# x19 -> runRW# ... (\ (s6 :: State# RealWorld) -> case lvl1186 of { False -> case lvl1183 of { False -> case lvl1167 of { I# x20 -> case newByteArray# ...`, the shape's split, the two comparisons and the size all top-level constants (qualifiers dropped, whitespace collapsed).

**Repro** (`~/r/horde-ad/dist-inlcat/cases/O27-inline-tests-floated`, variants `inlinable`, the wrapper INLINABLE as at the parent, and `inline`, INLINE by `-DINL` as at the commit; `run` is `100000`; `measure.sh N`): orthotope's `Shape` class, `sizeP` NOINLINE and `shapeP` forcing it, and its generic `ravel` with `fromVector`'s check, polymorphic in an `Unbox` element, in `Lib`; the point-free ShapedU wrapper in `Wrap`; and a client ravelling no subarrays into a `'[0, 3]` array of Doubles.

```haskell
{-# LANGUAGE Haskell2010, BangPatterns, ScopedTypeVariables, TypeApplications,
             AllowAmbiguousTypes, DataKinds, KindSignatures, TypeOperators,
             FlexibleInstances #-}
module Lib (Shape (..), T (..), Arr (..), ravelG) where

import Data.Proxy (Proxy (..))
import GHC.TypeLits (KnownNat, Nat, natVal)
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Unboxed.Mutable as MVU

class Shape (s :: [Nat]) where
  shapeP :: Proxy s -> [Int]
  sizeP  :: Proxy s -> Int

instance Shape '[] where
  {-# INLINE shapeP #-}
  shapeP _ = []
  {-# INLINE sizeP #-}
  sizeP  _ = 1

instance (Shape s, KnownNat n) => Shape (n ': s) where
  {-# INLINE shapeP #-}
  shapeP = const sh
    where sh = sizeP (Proxy :: Proxy (n ': s)) `seq` valueOf @n : shapeP (Proxy :: Proxy s)
  {-# NOINLINE sizeP #-}
  sizeP = const sz
    where sz | n > toInteger (maxBound :: Int) || m /= 0 && i > maxBound `quot` m =
                 error "Shape: past maxBound"
             | otherwise = i * m
          n = natVal (Proxy :: Proxy n)
          i = fromInteger n :: Int
          m = sizeP (Proxy :: Proxy s)

valueOf :: forall n i . (KnownNat n, Num i) => i
valueOf = fromInteger $ natVal (Proxy :: Proxy n)

natT :: forall n . KnownNat n => Int
natT = fromInteger (natVal (Proxy :: Proxy n))

data T a = T ![Int] !Int !(VU.Vector a)

newtype Arr (sh :: [Nat]) a = Arr (T a)

getStridesT :: [Int] -> [Int]
getStridesT [] = [1]
getStridesT (s : ss) = case getStridesT ss of
  r@(m : _) -> let !x = s * m in x : r
  [] -> []

{-# INLINE fromVector #-}
fromVector :: forall sh a . (VU.Unbox a, Shape sh) => VU.Vector a -> Arr sh a
fromVector v | n /= l = error $ "fromVector: size mismatch " ++ show (n, l)
             | otherwise = Arr (T st 0 v)
  where n : st = getStridesT ss
        l = VU.length v
        ss = shapeP (Proxy :: Proxy sh)

{-# INLINE concatN #-}
concatN :: VU.Unbox a => Int -> [VU.Vector a] -> VU.Vector a
concatN n vs = VU.create (do mv <- MVU.unsafeNew n
                             let go _ [] = return ()
                                 go i (v : rest) = do
                                   VU.unsafeCopy (MVU.unsafeSlice i (VU.length v) mv) v
                                   go (i + VU.length v) rest
                             go 0 vs
                             return mv)

{-# INLINE ravelG #-}
ravelG :: forall s sh a . (VU.Unbox a, KnownNat s, Shape sh) => [T a] -> Arr (s ': sh) a
ravelG ts | natT @s == 1, [T ss o v] <- ts = Arr (T (0 : ss) o v)
          | otherwise = fromVector (concatN (sizeP (Proxy :: Proxy (s ': sh)))
                                            [ v | T _ _ v <- ts ])
```

```haskell
{-# LANGUAGE CPP, DataKinds, TypeOperators #-}
module Wrap (Sub (..), Outer (..), ArrU (..), ravel) where

import qualified Data.Vector.Unboxed as VU
import GHC.TypeLits (KnownNat)
import Lib

newtype Sub a = Sub (T a)
newtype Outer a = Outer [Sub a]
newtype ArrU sh a = ArrU (Arr sh a)

#if defined(INL)
{-# INLINE ravel #-}
#else
{-# INLINABLE ravel #-}
#endif
ravel :: (VU.Unbox a, KnownNat s, Shape sh) => Outer a -> ArrU (s ': sh) a
ravel = ArrU . ravelG . map unSub . unOuter
  where unSub (Sub t) = t
        unOuter (Outer ss) = ss
```

```haskell
{-# LANGUAGE BangPatterns, DataKinds #-}
module Main (main) where

import qualified Data.Vector.Unboxed as VU
import Lib
import Wrap
import System.Environment (getArgs)

{-# NOINLINE row #-}
row :: Outer Double -> ArrU '[0, 3] Double
row vs = ravel vs

{-# OPAQUE input #-}
input :: Int -> Outer Double
input _ = Outer []

main :: IO ()
main = do
  [n] <- map read <$> getArgs
  let go :: Int -> Int -> Int
      go !i !acc | i == n = acc
                 | otherwise = case row (input i) of
                     ArrU (Arr (T _ _ v)) -> go (i + 1) (acc + VU.length v)
  print (go 0 0)
```

`Main.dump-simpl`, whitespace collapsed: `inlinable` has `row = $sravel` and `$w$s$wravel = \ eta -> case $s$wravel10 of { I# ipv -> case $s$wravel5 of { [] -> case $s$wravel4 of {}; : n st -> case n of { I# x -> runRW# (\ s -> case <# ipv 0# of { __DEFAULT -> case ># ipv 1152921504606846975# of {`, and no `tagToEnum# (<# x 0#)`; `inline` has `$wrow = \ vs -> case ds1 of { (n1, st) -> case n1 of { I# x -> runRW# (\ s -> case lvl22 of { False -> case lvl16 of { False -> case eta of { I# x1 ->`, with `ds1 = case eta of { I# ipv -> case getStridesT lvl28 of { [] -> case patError lvl23 of {}; : n st -> (n, st) } }`, `lvl16 = case eta of { I# x -> tagToEnum# (># x 1152921504606846975#) }` and `lvl22 = case eta of { I# x -> tagToEnum# (<# x 0#) }`.

`measure.sh 1000000`, twice alike:

```
inlinable: 226.9 instructions, 96.0 bytes a call
inline: 213.5 instructions, 32.0 bytes a call
```

The INLINABLE variant also pays the out-of-line call and the rebuilding of its result. With the wrapper INLINE [1] (`~/r/horde-ad/dist-inlcat/cases/O27-tests-cost`, this repro with a third variant `inline1`, `-DINL1`), inlined after the first float-out, the row is the specialisation's body inlined, the tests in place, `$wrow = \ vs -> case lvl20 of { I# ipv -> case lvl18 of { [] -> case lvl13 of {}; : n st -> case n of { I# x1 -> runRW# (\ s1 -> case <# ipv 0# of {`, and its `measure.sh 1000000` gives `inline1: 192.5 instructions, 32.0 bytes a call`: the floated pair and `Bool`s cost 21 instructions a call by themselves, and the INLINABLE form's call and rebuilt result 34.4 instructions and 64 bytes.

**Reproduces small:** yes in Core: the floated pair and `Bool`s against the tests on a case-bound size, orthotope's Core in both variants; their cost, 21 instructions a call, isolated by an INLINE [1] variant. Also tried, both forms then floating the tests alike: the element type fixed to `Double` in the library, and the wrapper a bare alias.

### O28. A function argument that an INLINE function applies at two places is copied into both only while small: with its own callee INLINABLE it is copied, a local closure over the caller's values, and with the callee INLINE it grows first and stays bound, a top-level worker, as the function orthotope's `rerank` applies to each subarray does under `scalar`'s Storable wrappers

**Rule.** A function argument that an INLINE function applies at two places is copied into both only while its right-hand side is small, so whether the argument's own callee is inlined into it first decides whether it is copied. Orthotope's `rerank` is such a function: it is INLINE and applies its function argument at two places, `case f (A ish s) of` for a single subarray and `map (f . A ish) $ subArraysT osh t` otherwise, so where `rerank` is inlined, `f` is copied into its uses only while its right-hand side is small (`postInlineUnconditionally`'s `smallEnoughToInline` test, [compiler/GHC/Core/Opt/Simplify/Utils.hs#L1855][g359]; E12, E20). In a model (`~/r/horde-ad/dist-inlcat/cases/O28-row-function-copied`), with `scalar` a call of the INLINABLE function the row's function is small and is copied, `PostInlineUnconditionally eta \ r -> scalar $fStorableDouble (sumA $fStorableDouble $fNumDouble r)` (`build.log`), so the subarray loop applies it to `A ish x` and closes over `ish`; with `scalar` INLINE its body is inlined into the function first, whose guidance is then `IF_ARGS [0] 180 10`, and the function stays bound, ending as the top-level worker `$weta`. Orthotope's `$wcons` comes from a copy of the row's function made by another route. In SS the function is `eta1`, the function parameter of `S.rerank`'s stable unfolding. With `G.rerank` already inlined, the unfolding uses `eta1` in the right-hand side of the pattern guard's `fail` join point and in the join's body. The occurrence analyser carries only local let-bound Ids through a join point ((W4) of Note [Occurrence analysis for join points], [compiler/GHC/Core/Opt/OccurAnal.hs#L783][g497]), so `eta1` is `ManyOccs` and `postInlineUnconditionally` leaves it bound. Call-site inlining copies it into both applications instead: `guidance IF_ARGS [0] 80 0`, `adjusted size = 60` and `= 52`, `ANSWER = YES`, where N2's `IF_ARGS [0] 260 0` is refused. The function applied to each subarray holds the copy. `prepareRhs` let-binds it under the name of `subArraysT`'s `cons`, and at `IF_ARGS [20] 220 10` it is too big for its two uses, so it becomes `$wcons`. The model takes the same route once `rerank1`'s guard is made such a pattern guard: its `eta` loses `[Occ=OnceL2!]` and is inlined at both calls, `IF_ARGS [0] 70 0`. The model's allocation runs the other way for another reason: under INLINE its worker `$weta` boxes the buffer for its `touch#`, `let { ipv3 = PlainPtr! [ipv2]; }`, and returns it unboxed, and the row boxes it again, `let { $wgo_$wrow_sat = PlainPtr! [ww8]; } in Vector [ww6 ww7 $wgo_$wrow_sat];` (`Main.dump-stg-final`), 16 bytes a subarray and, by a ticky build, the whole 48 a call, where under INLINABLE the inlined copy boxes it once; orthotope's `$weta7` in N2 and `$wcons` in SS both return the buffer unboxed the same way (U20).

**Seen.** SS (N2 with the Storable wrappers' `scalar` INLINABLE) against N2 (N without `sameSize` INLINE), at the row `rerank 1 (\ r -> scalar (sumA r))`: Storable `rerank` small 16 bytes a call more in both readings and 20 to 28 instructions, Shaped empty 16 bytes forced and 7 instructions; by callgrind at forced small Dynamic, a function closure (`FUN_1_0`) holding the thunk (`THUNK_1_0`) that N2 allocates alone, applied to each of the three subarrays. At small Dynamic the 16 bytes are that closure alone: in SS's STG `$wcons` is `{lvl} \r [...]`, one free variable, two words, and the shape thunk `{ww4} \u []`, three words, is bound in both builds; a ticky run of a one-row reduction counts the closure, `$wcons` `Alloc'd` 16 a call and one function closure more (`ALLOC_FUN_gds` 208 against 192), the shape thunk 24 a call in both. In N2's `OpsDynamic.dump-simpl` the row worker `$wlvl677` calls the top-level worker `$weta7`, the row's function after worker/wrapper, the subarray's shape first, `case $weta7 wild16 wild15 ww2 ipv ipv1 ipv2 of`; in SS's `$wlvl677` binds `let { lvl3466 :: IU.ShapeL lvl3466 = case ww4 of { [] -> [] @Int; : ipv3 ipv4 -> ipv4 } } in let { $wcons :: [Int] -> Int# -> Int# -> Addr# -> ForeignPtrContents -> ...`, whose body begins `case ww9 of ww14 { __DEFAULT -> case lvl3466 of wild14 { __DEFAULT -> case OpsDynamic.$w$s$wsumA wild14 ww14 ...`, closing over the shape (qualifiers dropped, whitespace collapsed). Late lambda lifting would not remove the closure: SS's `OpsDynamic` recompiled with `-fstg-lift-lams`, which `-O` leaves off, still binds `$wcons` inside `$wlvl677` as a closure over `lvl3466` (`-ddump-stg-final`), the lifter refusing a binding whose arguments after lifting would exceed `liftLamsNonRecArgs`, 5 by default, and `$wcons` having five before gaining `lvl3466` (the count inferred). Shaped empty's 16 bytes are another allocation: the `PlainPtr` box of the buffer `genericUnsafeConcatN` allocates (`mallocPlainForeignPtrAlignedBytes`, through vector's Storable `basicUnsafeNew`), which only the `touch#` after each copy into the buffer uses. In a one-row reduction whose `$wcons` has the bench's right-hand-side size, SS's STG binds it, `ipv6_t31l = PlainPtr! [ipv4_t31j]` (qualifiers dropped), before `rerank`'s `product osh == 0` test, `case lvl20_r2WI of`, so the empty row allocates it unused, 16 bytes a call by ticky's `Alloc'd` and the only allocation in which the two builds' reductions differ; N2's binds it inside the join point only the non-empty path enters. The late Float inwards ([compiler/GHC/Core/Opt/Pipeline.hs#L286][g498]) moves N2's there and keeps SS's above the test, a binding used at two drop points staying above both ([compiler/GHC/Core/Opt/FloatIn.hs#L740][g499]): `$j_s2BS`, the join point both paths jump to, passes the boxed result to `$j_s2VI`, which returns the worker's result unboxed. `$j_s2VI` is the join point `$j_s2Tv` that the simplifier after worker/wrapper makes, and none of that pass's four iterations gives it an unfolding, where N2's counterpart has one from iteration 2 and is inlined in iteration 3. One of its jumps lies inside the join point `$w$j_s2RU`, which only the `joinrec` `$wfoldlM'_loop` jumps to, so the occurrence analyser marks it `OnceL2`, used once inside a lambda, where N2's is `Once2`; by the source, that is what `isExitJoinId` takes for an exit join point ([compiler/GHC/Core/Opt/Simplify/Utils.hs#L3063][g151]), and `simplLetUnfolding` gives an exit join point no unfolding ([compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4855][g152]): E14's route. The second `runRW#` around that jump, the one-subarray path's 8-byte allocation, does not give the mark, the state token's lambda being one-shot: a join point jumped to from inside `runST` and from an `else` branch is `Once2`. The late Float out moves `$j_s2VI` to top level (`floatJoinsToTop`, [compiler/GHC/Core/Opt/Pipeline.hs#L276][g500]) and the final simplifier inlines it, but no Float inwards follows that pass at `-O` ([compiler/GHC/Core/Opt/Pipeline.hs#L288][g501]). A base-only model, a box bound above an emptiness test and used inside the loop, shows the same marks, its join point `OnceL2` on HEAD and `Once2` on 9.8.4, and its final Core binds the box before the test, so the empty path allocates it and never uses it: 16 bytes a call on 9.10.3, 9.12.4, 9.14.1 and HEAD, none on 9.6.7 and 9.8.4. It is posted as a comment on GHC [#27982](https://gitlab.haskell.org/ghc/ghc/-/work_items/27982), `docs/ghc-issue-replay-wider-form-27982-comment.md` in horde-ad.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/O28-inlinable-scalar-cons-closure`, variants `inline` and `inlinable` (`-DINB`); `run` is `100000`): a reduced `rerank` mapping `f . A ish` over Storable slices, `f` applied at two places as in orthotope, a `sumA`, and `scalar = A [] . VS.singleton`, INLINE or INLINABLE, in a module of its own.

```haskell
{-# LANGUAGE Haskell2010, BangPatterns #-}
module Lib (A (..), rerank1, sumA) where

import qualified Data.Vector.Storable as VS

data A a = A ![Int] !(VS.Vector a)

{-# INLINE subArrays #-}
subArrays :: VS.Storable a => Int -> Int -> VS.Vector a -> [VS.Vector a]
subArrays n k v = [ VS.unsafeSlice (i * k) k v | i <- [0 .. n - 1] ]

{-# INLINE rerank1 #-}
rerank1 :: (VS.Storable a, VS.Storable b) => (A a -> A b) -> A a -> A b
rerank1 f (A sh v) = case sh of
  o : ish | o == 1 -> case f (A ish v) of A rsh w -> A (1 : rsh) w
          | otherwise ->
              let rs = map (f . A ish) (subArrays o (product ish) v)
              in A [o] (VS.concat [ w | A _ w <- rs ])
  [] -> error "rerank1"

{-# INLINE sumA #-}
sumA :: (VS.Storable a, Num a) => A a -> a
sumA (A _ v) = VS.sum v
```

```haskell
{-# LANGUAGE CPP #-}
module Scal (scalar) where

import qualified Data.Vector.Storable as VS
import Lib

#if defined(INB)
{-# INLINABLE scalar #-}
#else
{-# INLINE scalar #-}
#endif
scalar :: VS.Storable a => a -> A a
scalar = A [] . VS.singleton
```

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import qualified Data.Vector.Storable as VS
import Lib
import Scal
import System.Environment (getArgs)

{-# NOINLINE row #-}
row :: A Double -> A Double
row a = rerank1 (\ r -> scalar (sumA r)) a

{-# OPAQUE input #-}
input :: Int -> A Double
input i = A [3, 3] (VS.fromList (map fromIntegral [i .. i + 8]))

main :: IO ()
main = do
  [n] <- map read <$> getArgs
  let go :: Int -> Double -> Double
      go !i !acc | i == n = acc
                 | otherwise = case row (input i) of
                     A _ v -> go (i + 1) (acc + VS.unsafeIndex v 2)
  print (go 0 0)
```

`Main.dump-simpl` holds no `$weta` and no `$wcons` in either variant, and the run's `+RTS -s` report reads `186,502,376 bytes allocated in the heap` in both.

A second repro (`~/r/horde-ad/dist-inlcat/cases/O28-row-function-copied`, variants `inline` and `inlinable` (`-DINB`); `inlinetr` and `inlinabletr`, with `-dverbose-core2core`; `inlineid`, with the binders' information; `inlinestg` and `inlinablestg`, with `-ddump-stg-final`; `run` is `100000`): the first repro's `Scal` and `Main`, with `subArrays` a `build` using its `cons` at two places, `rerank1` applying `f` at two places, and `sumA` NOINLINE.

```haskell
{-# LANGUAGE Haskell2010, BangPatterns #-}
module Lib (A (..), rerank1, sumA) where

import GHC.Exts (build)
import qualified Data.Vector.Storable as VS

data A a = A ![Int] !(VS.Vector a)

{-# INLINE subArrays #-}
subArrays :: VS.Storable a => Int -> Int -> VS.Vector a -> [VS.Vector a]
subArrays n k v = build $ \ cons nil ->
  if n == 0 then nil
  else if n == 1 then cons v nil
  else let go i | i == n = nil
                | otherwise = cons (VS.unsafeSlice (i * k) k v) (go (i + 1))
       in go 0

{-# INLINE rerank1 #-}
rerank1 :: (VS.Storable a, VS.Storable b) => (A a -> A b) -> A a -> A b
rerank1 f (A sh v) = case sh of
  o : ish | o == 1 -> case f (A ish v) of A rsh w -> A (1 : rsh) w
          | otherwise ->
              A [o] (VS.concat (map (\ (A _ w) -> w)
                                    (map (f . A ish) (subArrays o (product ish) v))))
  [] -> error "rerank1"

{-# NOINLINE sumA #-}
sumA :: (VS.Storable a, Num a) => A a -> a
sumA (A _ v) = VS.sum v
```

**Reproduces small:** in part. With `subArrays` a `build` using its `cons` at two places and `sumA` out of line (`~/r/horde-ad/dist-inlcat/cases/O28-row-function-copied`): the copy under INLINABLE and the top-level worker under INLINE, yes; the closure over `ish` is a thunk in the subarray loop's list cells, `: (case k of { I# y -> case ish of { __DEFAULT -> case $wsumA`, not a separate `$wcons`; and the allocation goes the other way, 305,702,376 bytes at 100000 calls under INLINABLE against 310,502,376 under INLINE. With `subArrays` a list comprehension and `sumA` INLINE, the first repro, both variants inline the row's function into the loop, and so, in a scratch build, does `scalar` NOINLINE. Not tried: orthotope's `subArraysT` and `ravelOuter`.

### O29. A row's body that inlining turns into a `case` stays under the row's lambda, which SetLevels levels as a strict context, so a result independent of the lambda's argument is built at every call, where a constructor application around an out-of-line call floats to a constant

**Rule.** A `case` in a strict context is never floated as a maximal free expression (`lvlMFE`'s `AnnCase` equation, [compiler/GHC/Core/Opt/SetLevels.hs#L611][g421]; Note [Case MFEs], [#L1098][g502]), and a lambda's body is levelled as a strict context (`lvlExpr`'s lambda case, `lvlNonTailMFE new_env True body`, [#L360][g503]). So a body that is a constructor application around calls is free to float to top level, the calls with it, and then the lambda returns a constant, as the parent's does; a body that is a `case`, as inlining a function that fills a vector under `runRW#` makes it, stays inside the lambda and runs at every call, whatever it depends on (the same hold-back as O15's). Worker/wrapper then drops the lambda's absent argument and, no value argument being left, gives the worker a void one (`needsVoidWorkerArg`, [compiler/GHC/Core/Opt/WorkWrap/Utils.hs#L384][g504]; Note [Protecting the last value argument], [#L415][g505]), its result's fields returned unboxed and boxed again by the caller (U20): in a model whose row is a top-level binding, `$wrow = \ (void :: (# #)) ->` and `row = \ (x [Dmd=A] :: Double) -> case $wrow GHC.Internal.Prim.void# of wild { (# ww, ww, ww, ww, ww, ww #) ->` right after worker/wrapper (`~/r/horde-ad/dist-inlcat/cases/O29-void-worker-arg`, `Main.dump-worker-wrapper`, whitespace collapsed).

**Seen.** The pragma commit "Give each binding the pragma its kind calls for" against its parent, "Probe whether a client's call builds a Route, a Range or an Axes", boxed `iterateN` empty strided, 112 bytes a call more forced in Dynamic and Ranked and 88 in Shaped. The row is `\ x -> ARR.iterateN (ROWS * cols) (+ 1) x` in Dynamic and Ranked, `\ x -> ARR.iterateN @NN (+ 1) x` in Shaped, at the empty size of no elements, its result independent of `x`, and the commit makes `fromListT`, which `iterateNT n f x = fromListT [n] $ take n $ iterate f x` calls, INLINE in place of INLINABLE. In the parent's `OpsDynamic.dump-simpl` the row is `lvl625 = \ (x5 :: Double) -> lvl624`, with `lvl624 = Data.Array.Internal.DynamicG.A @Data.Vector.Vector @Double lvl357 lvl621`, `lvl621 = lvl620 []` and `lvl620` the library's specialisation `Data.Array.Internal.Dynamic.$fTraversableArray_$sfromListT @Double ...`, called out of line; in the commit's it is `lvl1126 = \ (x2 :: Double) -> case $wlvl79 (##) of { (# ww, ww1, ww2, ww3, ww4, ww5 #) -> (A ww (T ww1 ww2 (Vector ww3 ww4 ww5)))`, its worker `$wlvl79 :: (# #) -> (# IU.ShapeL, [Int], Int#, Int#, Int#, Array# Double #)` running the fill's `runRW#` at every call (the commit's qualifiers dropped, whitespace collapsed).

**Repro** (`~/r/horde-ad/dist-inlcat/cases/O29-iterate-constant-per-call`, variants `inlinable` and `inline` (`-DINL`), by `fromListT`'s pragma; `run` is `100000`): orthotope's `iterateN`, `iterateNT` and `fromListT` over boxed vectors, and the row `\ x -> iterateN 0 (+ 1) x` passed to an out-of-line harness.

```haskell
{-# LANGUAGE Haskell2010, CPP, BangPatterns #-}
module Lib (T (..), A (..), getStridesT, iterateN) where

import qualified Data.Vector as V

data T a = T ![Int] !Int !(V.Vector a)
data A a = A ![Int] !(T a)

getStridesT :: [Int] -> [Int]
getStridesT [] = [1]
getStridesT (s : ss) = case getStridesT ss of
  r@(m : _) -> let !x = s * m in x : r
  [] -> []

{-# INLINE fromVectorT #-}
fromVectorT :: [Int] -> V.Vector a -> T a
fromVectorT sh = T (tail $ getStridesT sh) 0

#if defined(INL)
{-# INLINE fromListT #-}
#else
{-# INLINABLE fromListT #-}
#endif
fromListT :: [Int] -> [a] -> T a
fromListT sh = fromVectorT sh . V.fromListN (product sh)

{-# INLINE iterateNT #-}
iterateNT :: Int -> (a -> a) -> a -> T a
iterateNT n f x = fromListT [n] $ take n $ iterate f x

{-# INLINE iterateN #-}
iterateN :: Int -> (a -> a) -> a -> A a
iterateN n f | n < 0 = error $ "iterateN: negative size " ++ show n
             | otherwise = A [n] . iterateNT n f
```

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import qualified Data.Vector as V
import Lib
import System.Environment (getArgs)

{-# NOINLINE call #-}
call :: Int -> (Double -> A Double) -> Double -> Int
call n f x0 = go 0 0
  where go :: Int -> Int -> Int
        go !i !acc | i == n = acc
                   | otherwise = case f (x0 + fromIntegral i) of
                       A _ (T _ _ v) -> go (i + 1) (acc + V.length v)

main :: IO ()
main = do
  [n] <- map read <$> getArgs
  print (call n (\ x -> iterateN 0 (+ 1) x) 1)
```

`Main.dump-simpl`, whitespace collapsed: `inlinable` has `main3 = \ x -> case $wfromListT main4 [] of { (# ww, ww1, ww2, ww3, ww4 #) -> A main4 (T ww ww1 (Vector ww2 ww3 ww4)) }` and `inline` `main3 = \ x -> case main7 of { [] -> case main6 of {}; : ds xs -> runRW# (\ s -> case newArray# 0# uninitialised`: both bodies are `case`s, and both are built at every call.

A second repro (`~/r/horde-ad/dist-inlcat/cases/O29-library-spec-floats`, variants `inlinable` and `inline` (`-DINL`), as the first's; `run` is `100000`): `fromListT` over a vector class in `Lib`, specialised at the boxed instance in a library module `Inst`, as orthotope's Dynamic specialises it, and the same row in `Main`.

```haskell
{-# LANGUAGE Haskell2010, CPP, BangPatterns #-}
module Lib (Vec (..), T (..), A (..), getStridesT, fromListT, iterateN) where

class Vec v where
  vFromListN :: Int -> [a] -> v a
  vLength :: v a -> Int
  vToList :: v a -> [a]

data T v a = T ![Int] !Int !(v a)
data A v a = A ![Int] !(T v a)

getStridesT :: [Int] -> [Int]
getStridesT [] = [1]
getStridesT (s : ss) = case getStridesT ss of
  r@(m : _) -> let !x = s * m in x : r
  [] -> []

{-# INLINE fromVectorT #-}
fromVectorT :: [Int] -> v a -> T v a
fromVectorT sh = T (tail $ getStridesT sh) 0

#if defined(INL)
{-# INLINE fromListT #-}
#else
{-# INLINABLE fromListT #-}
#endif
fromListT :: Vec v => [Int] -> [a] -> T v a
fromListT sh = fromVectorT sh . vFromListN (product sh)

{-# INLINE iterateNT #-}
iterateNT :: Vec v => Int -> (a -> a) -> a -> T v a
iterateNT n f x = fromListT [n] $ take n $ iterate f x

{-# INLINE iterateN #-}
iterateN :: Vec v => Int -> (a -> a) -> a -> A v a
iterateN n f | n < 0 = error $ "iterateN: negative size " ++ show n
             | otherwise = A [n] . iterateNT n f
```

```haskell
module Inst (travA) where

import qualified Data.Vector as V
import Lib

instance Vec V.Vector where
  {-# INLINE vFromListN #-}
  vFromListN = V.fromListN
  {-# INLINE vLength #-}
  vLength = V.length
  {-# INLINE vToList #-}
  vToList = V.toList

travA :: Applicative f => (a -> f b) -> A V.Vector a -> f (A V.Vector b)
travA f (A sh (T _ _ v)) = A sh . fromListT sh <$> traverse f (vToList v)
```

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import qualified Data.Vector as V
import Inst ()
import Lib
import System.Environment (getArgs)

{-# NOINLINE call #-}
call :: Int -> (Double -> A V.Vector Double) -> Double -> Int
call n f x0 = go 0 0
  where go :: Int -> Int -> Int
        go !i !acc | i == n = acc
                   | otherwise = case f (x0 + fromIntegral i) of
                       A _ (T _ _ v) -> go (i + 1) (acc + V.length v)

main :: IO ()
main = do
  [n] <- map read <$> getArgs
  print (call n (\ x -> iterateN 0 (+ 1) x) 1)
```

`Inst.dump-simpl` has `"SPEC/Inst fromListT @Vector @_" forall @a $dVec. fromListT $dVec = $sfromListT`. `Main.dump-simpl`, whitespace collapsed: `inlinable` has `main3 = \ x -> main4`, with `main4 = A main7 main5`, `main5 = main6 []` and `main6 = $sfromListT main7`, the parent's shape, a constant; `inline` has `main3 = \ x -> case main7 of { [] -> case main6 of {}; : ds xs -> runRW# (\ s -> case newArray# 0# uninitialised`, built at every call. `+RTS -s` at 100000 calls: 3,256,144 bytes allocated under INLINABLE against 14,455,912 under INLINE, 112 bytes a call more, orthotope's Dynamic figure.

**Reproduces small:** yes, by the second repro, `fromListT` specialised in a library module: under INLINABLE the row returns a constant, under INLINE it builds its result at every call, 112 bytes a call more. With `fromListT` called directly, the first repro, the INLINABLE form's body is a `case` too, `fromListT`'s worker called through its inlined wrapper.

### O30. A copy specialised in a module polymorphic in the element is keyed on the vector type alone, its element and the element's evidence parameters; without a pragma on the wrapper a client calls, the wrapper's worker has no unfolding and runs with the element's dictionary

**Rule.** A call's key keeps a dictionary argument only if `interestingDict` returns `True` for it, a dictionary constructor application under casts and unfoldings (the specialisation appendix, "What a call is specialised on"). In a module polymorphic in the element, the evidence for a `VecElem v a` constraint is a cast of a lambda-bound dictionary, so a call of an INLINABLE function at a known vector type is specialised on the vector type alone, the copy taking the element and its evidence as parameters; at a client with a known element the same evidence is a cast of `$fStorableDouble`, which is interesting. A client reaches a copy at its own element only through an unfolding of the wrapper it calls: an INLINABLE wrapper's worker carries the stable unfolding (U08), which the client specialises, while a worker of a wrapper without a pragma has no unfolding, so the client cannot specialise it (the specialisation appendix, "Which imported functions are specialised"; why worker/wrapper gives this one no unfolding was not read). Source: [compiler/GHC/Core/Opt/Specialise.hs#L3026][g506] (`mkCallUDs'`), [#L3086][g390] (`interestingDict`), [#L911][g330] (`canSpecImport`).

**Seen.** `docs/perf-checklist.md` S1: orthotope's Storable and Unboxed modules' rules keyed on the vector type alone with the element's `VecElem` constraint `irred`, Storable `pad` 43 times as slow per element; and `DynamicS.toVector`, without a pragma, "split into a wrapper and a worker with no unfolding, which no client could specialise".

**Repro** (`~/r/horde-ad/dist-inlcat/cases/O30-vecelem-key-vector-alone`, variants `inlinable` and `nopragma`, the latter `-DNOPRAG`; `run` is `10`; `measure.sh N`): a vector class whose element constraint is an associated type family, its Storable instance and an INLINABLE generic sum in `G`; a Storable wrapper polymorphic in the element in `S`, INLINABLE or without a pragma; and a client at `Double`.

```haskell
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeFamilies #-}
module G (Vector (..), sumG) where

import Data.Kind (Constraint, Type)
import qualified Data.Vector.Storable as VS

class Vector v where
  type VecElem v :: Type -> Constraint
  vIndex :: VecElem v a => v a -> Int -> a
  vLength :: VecElem v a => v a -> Int

instance Vector VS.Vector where
  type VecElem VS.Vector = VS.Storable
  {-# INLINE vIndex #-}
  vIndex = VS.unsafeIndex
  {-# INLINE vLength #-}
  vLength = VS.length

{-# INLINABLE sumG #-}
sumG :: (Vector v, VecElem v a) => (a -> Double) -> v a -> Double
sumG f v = go 0 0
  where n = vLength v
        go !acc i | i >= n = acc
                  | otherwise = go (acc + f (vIndex v i)) (i + 1)
```

```haskell
{-# LANGUAGE CPP #-}
module S (sumS) where

import qualified Data.Vector.Storable as VS
import qualified G

#if !defined(NOPRAG)
{-# INLINABLE sumS #-}
#endif
sumS :: VS.Storable a => (a -> Double) -> VS.Vector a -> Double
sumS f v = G.sumG f v + G.sumG f (VS.reverse v)
```

```haskell
module Main (main) where

import System.Environment (getArgs)
import qualified Data.Vector.Storable as VS
import S

callS :: VS.Vector Double -> Double
callS = sumS id
{-# NOINLINE callS #-}

main :: IO ()
main = do
  [ns] <- getArgs
  let n = read ns :: Int
  print (sum [ callS (VS.replicate 1000 (fromIntegral k)) | k <- [1 .. n] ])
```

`S.dump-simpl`, whitespace collapsed, both variants: S's copy of `sumG` is keyed on `VS.Vector` alone, `$w$s$wsumG = \ @a irred f ww ww1 ww2 ->`, and S's worker calls it with the cast dictionary, ``case $w$s$wsumG ($dStorable `cast` <Co:4>) f ww ww1 ww2 of ww3``. Without a pragma, `S.iface` gives the wrapper `Unfolding: Core: StableSystem <3,TrueFalse>` and the worker `$wsumS` no unfolding, its information ending `Inline: [2]]`, and the client calls the worker with the dictionary, `$wsumS $fStorableDouble` (`Main.dump-simpl`). Under INLINABLE the worker has `Inline: [2], Unfolding: Core: StableUser`, and the client specialises it and, through it, S's copy: `"SPEC/Main $w$s$wsumG @Double" [2] forall irred. $w$s$wsumG irred = $s$w$s$wsumG` (`Main.dump-simpl`). `measure.sh 20000`, two sums of 1000 elements a call, and `measure.sh 10000` within one instruction of it:

```
inlinable: 176611.43 instructions a call
nopragma: 507006.34 instructions a call
```

**Reproduces small:** yes, the copy keyed on the vector alone and the pragma-free worker with no unfolding; not the clients' calls sent to the library's copy, which on this tree, carrying the fix of GHC [#27873](https://gitlab.haskell.org/ghc/ghc/-/work_items/27873) (the specialisation appendix, "Already covered"), make copies of their own: a client calling `G.sumG` at `Double` with S's rule in scope got `Rule fired: SPEC/Main sumG @Vector @Double (Main)` (no case kept).

## 4. Which unfolding a call gets: stable or vanilla

Which unfolding a binding carries and its importers get, how a stable unfolding is itself simplified, and when either form is the better; and, from U19 on, what a worker/wrapper split leaves boxed.

### U01. A binding without a pragma carries an unfolding made from its optimised right-hand side, and its importer computes that unfolding's guidance

**Rule.** A binding with no stable unfolding gets, each time the simplifier processes it, a `VanillaSrc` unfolding made from the right-hand side just simplified, so the unfolding a later pass and an importer get is the latest optimised right-hand side, not the source. A freshly born or exit join point gets none (U14). The interface stores such an unfolding with no guidance, and the importing module computes the guidance from the template with its own `UnfoldingOpts`, its creation threshold among them (U06). Worker/wrapper replaces this unfolding with a stable one for a small function (U07) and for a wrapper (A26); which vanilla unfoldings reach the interface at all is U05. Source: [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4846][g507] (`simplLetUnfolding`, its `otherwise` branch calling `mkLetUnfolding env ... VanillaSrc ... new_rhs`), [Iteration.hs#L4871][g508] (`mkLetUnfolding`, which makes an unfolding even for a loop breaker), [compiler/GHC/Types/Basic.hs#L1086][g509] (`VanillaSrc`, "The current rhs of the function" and "Replace uf_tmpl each time around"), [compiler/GHC/CoreToIface.hs#L536][g510] (`toIfGuidance`: `IfWhen` only for a stable `UnfWhen` unfolding, `IfNoGuidance` otherwise), [compiler/GHC/IfaceToCore.hs#L1906][g511] (`tcUnfolding`: `IfNoGuidance -> calcUnfoldingGuidance uf_opts ...` with the importer's options), [compiler/GHC/Core/Unfold.hs#L349][g23] (`calcUnfoldingGuidance`).

**Seen.** Not in our record as such; it is the baseline that the stable unfoldings of U03, U04, U07 and A26 depart from.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/U01-vanilla-unfolding`, variant `base`, with `-dinline-check chooseTwice`): a function whose optimised right-hand side collapses to another function, and an importer that inlines it.

```haskell
module A (choose, chooseTwice) where

-- Nothing for worker/wrapper to do: Bool is not unboxed and the result is
-- polymorphic, so no wrapper replaces the unfolding made from the RHS.
choose :: Bool -> a -> a -> a
choose b x y = if b then x else y

chooseTwice :: Bool -> a -> a -> a
chooseTwice b x y = choose b (choose b x y) (choose (not b) y x)
```

```haskell
module B (useTwice) where

import A

useTwice :: Bool -> Int -> Int
useTwice b n = chooseTwice b n (n + 1)
```

The optimised right-hand side, `A.dump-simpl`, is `chooseTwice = choose`, and the interface carries exactly that, with no guidance: `Unfolding: Core: <vanilla> choose`. In compiling B, `-dinline-check chooseTwice` prints the guidance B computed from that template, `guidance ALWAYS_IF(arity=0,unsat_ok=True,boring_ok=True)`, and `B.dump-inlinings` records `Inlining done: chooseTwice`.

**Reproduces small:** yes.

### U02. CSE replacing a binding's whole right-hand side by an earlier binding drops its INLINE or INLINABLE unfolding

**Rule.** When common sub-expression elimination finds a binding's entire right-hand side equal to that of a binding met earlier, it rewrites the right-hand side to the earlier binder and zaps the binding's stable unfolding, whatever its source: an INLINE or INLINABLE unfolding goes as well as one made by worker/wrapper. The next simplifier pass gives the binding a vanilla unfolding of the trivial right-hand side, so importers inline the earlier binder, with that binder's own unfolding, instead of what the user wrote. The guard that protects stable user unfoldings, `noCSE`, keeps such a binding out of CSE's environment but, for a non-recursive binding, does not stop its own right-hand side being replaced. `cse_bind` does not test the unfolding's source, contrary to Note [CSE for stable unfoldings] (section 6, item 4). Which of two equal right-hand sides is replaced follows the order of the bindings in Core: in this repro the twins come first in the source and after `sumSq` in Core, and with the order the other way round (`incAll` before its INLINE twin in the source, tried by hand) the INLINE twin came first in Core and kept its unfolding. Source: [compiler/GHC/Core/Opt/CSE.hs#L437][g512] (`cse_bind`, at line 455 `out_id'' | cse_done = zapStableUnfolding $ delayInlining toplevel out_id'`), [CSE.hs#L514][g513] (`noCSE`, line 517 `isStableUserUnfolding unf = no_cse`), [CSE.hs#L400][g228] (`cseBind` of a single recursive binding, which turns a repeated loop into a reference to the first, line 405), [CSE.hs#L233][g514] (Note [CSE for stable unfoldings]). The working tree's patch to [compiler/GHC/Core/Map/Expr.hs][g1] changes the keying of a non-recursive `let`; the right-hand sides compared here contain none.

**Seen.** Not in our record.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/U02-cse-drops-stable-unfolding`, variants `base`, plain `-O`, `nocse`, `-O -fno-cse`, and `passes`, below): an INLINE and an INLINABLE `foldr` consumer with the same body as a function without a pragma, and an importer applying the INLINE one to an enumeration.

```haskell
module A (sumSq, sumSqInl, sumSqInlb) where

sumSqInl :: [Integer] -> Integer
{-# INLINE sumSqInl #-}
sumSqInl xs = foldr (\x acc -> x * x + acc) 0 xs

sumSqInlb :: [Integer] -> Integer
{-# INLINABLE sumSqInlb #-}
sumSqInlb xs = foldr (\x acc -> x * x + acc) 0 xs

sumSq :: [Integer] -> Integer
sumSq xs = foldr (\x acc -> x * x + acc) 0 xs
```

```haskell
module B (total) where

import A

total :: Integer -> Integer
total n = sumSqInl [1 .. n]
```

Before CSE each of the three right-hand sides is `sumSqInl = \ xs -> go1 xs` and the like, over its own copy of the loop (variant `passes`, `-O -ddump-float-out -ddump-cse -dsuppress-all -dsuppress-uniques`: the last dump in `A.dump-float-out` is CSE's input, `A.dump-cse` its output, `sumSqInl = sumSq`). In `base`, A's Core ends with `sumSqInlb = sumSq` and `sumSqInl = sumSq`, and the interface gives both the vanilla unfolding `sumSq`: `Inline: (sat-args=1), Unfolding: Core: <vanilla> sumSq` and `Inline:, Unfolding: Core: <vanilla> sumSq`. B then builds the list and calls the loop:

```
total = \ n -> sumSq (enumDeltaToInteger1 total1 n)
```

In `nocse`, `sumSqInl` keeps `Inline: (sat-args=1), Unfolding: Core: StableUser <1,FalseFalse>` over `foldr`, `B.dump-inlinings` records `Inlining done: enumDeltaToInteger1FB`, and `total` is one loop with no list, `integerAdd (integerMul x1 x1) (go2 (integerAdd x1 total3));`.

**Reproduces small:** yes.

### U03. INLINE gives a stable unfolding of the right-hand side as written, inlined at saturated calls with something to gain, while the right-hand side is optimised on its own

**Rule.** The desugarer gives a binding with an INLINE pragma a `StableUserSrc` unfolding of its right-hand side before any optimisation (run through the simple optimiser only), with `UnfWhen` guidance, its count of arguments and its `unsat_ok` as in E01 and its `boring_ok` as in A01, and eta-expands the right-hand side to that count. From then on the right-hand side and the unfolding are optimised separately: the right-hand side by every pass, the unfolding only by the simplifier, as U10 describes, and worker/wrapper leaves an INLINE function unsplit (U09). The unfolding is inlined at a call as A01 describes, the third disjunct of the test, `unfoldingVeryAggressive`, being set by no flag on HEAD (R02). The interface prints the pragma as `Inline: (sat-args=N)` and the unfolding as `StableUser <arity,unsat_ok boring_ok>`. Source: [compiler/GHC/HsToCore/Binds.hs#L441][g240] (`makeCorePair`: `Inline {} -> inline_pair`, which at line 466 sets `mkInlineUnfoldingWithArity simpl_opts StableUserSrc runtime_arity rhs` and at line 468 `etaExpand runtime_arity rhs`), [Binds.hs#L474][g239] (`findSatArity`), [compiler/GHC/Core/Unfold/Make.hs#L157][g10] (`mkInlineUnfoldingWithArity`), [compiler/GHC/Core.hs#L2139][g515] (Note [Stable unfoldings]), [compiler/GHC/Core/Opt/Simplify/Inline.hs#L310][g5] (`tryUnfolding`, the `UnfWhen` branch: `enough_args && (boring_ok || some_benefit || ...)`).

**Seen.** What `docs/perf-checklist.md` I3 credits to inlining an INLINE unfolding: O07 to O10.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/U03-inline-unfolding`, variant `base`, with `-dinline-check sumSq`): an INLINE `foldr` consumer and its overloaded twin, called by an importer once on an enumeration and once in a boring context.

```haskell
module A (sumSq, sumSqN) where

sumSq :: [Int] -> Int
{-# INLINE sumSq #-}
sumSq xs = foldr (\x acc -> x * x + acc) 0 xs

sumSqN :: Num a => [a] -> a
{-# INLINE sumSqN #-}
sumSqN xs = foldr (\x acc -> x * x + acc) 0 xs
```

```haskell
module B (total, boring) where

import A

total :: Int -> Int
total n = sumSq [1 .. n]

boring :: [Int] -> Maybe Int
boring xs = Just (sumSq xs)
```

The interface gives `Inline: (sat-args=1), Unfolding: Core: StableUser <1,FalseFalse>` for `sumSq` and `<2,FalseFalse>` for `sumSqN`, whose dictionary counts; the template is the `foldr` as written, `\ (xs['GHC.Internal.Types.Many] :: [GHC.Internal.Types.Int]) -> GHC.Internal.Base.foldr ...`, with the always-active `+` and `*` of `Int` inlined into it. The right-hand side in `A.dump-simpl` is a loop floated out and split, while `sumSq` itself has no worker: `sumSq = \ xs -> case $wgo1 xs of ww { __DEFAULT -> I# ww }`. In B, `total` inlines the unfolding, `Inlining done: eftIntFB` shows the enumeration fused into it, and `$wtotal` is one loop with `join { $j y = +# (*# x x) y } in`. In `boring`, `-dinline-check` prints `arg infos [TrivArg]`, `interesting continuation BoringCtxt`, `some_benefit False`, `guidance ALWAYS_IF(arity=1,unsat_ok=False,boring_ok=False)`, `ANSWER = NO`, and the Core keeps the call, `boring = \ xs -> Just (sumSq xs)`.

**Reproduces small:** yes.

### U04. INLINABLE gives a stable unfolding of the right-hand side as written, and an importer inlines it by the size of that form, not of the optimised right-hand side

**Rule.** The desugarer gives a binding with an INLINABLE pragma a `StableUserSrc` unfolding of its right-hand side before optimisation, with guidance computed from that template: `UnfIfGoodArgs` in general, `UnfWhen` for a tiny template (A02), `UnfNever` past the creation threshold. The simplifier re-simplifies the template (U10) and recomputes the guidance from it each time, an `UnfWhen` one excepted, which is kept; the interface stores no guidance but an `UnfWhen` one, and the importer computes the rest from the template with its own options (U01, U06). So whether an importer inlines an INLINABLE function depends on the size of the source form, simplified only as a stable unfolding is, not on the optimised right-hand side, which can be much larger (here 51 against 245) or smaller. Worker/wrapper changes this in two ways: a small INLINABLE unfolding becomes an always-inline `StableSystemSrc` one (U07), and a large one moves to the worker (U08); the repro's `noww` variant, `-fno-worker-wrapper`, shows the unfolding as the desugarer made it. Source: [compiler/GHC/HsToCore/Binds.hs#L458][g516] (`inlinable_unf = mkInlinableUnfolding simpl_opts StableUserSrc rhs`), [compiler/GHC/Core/Unfold/Make.hs#L172][g517] (`mkInlinableUnfolding`: `mkUnfolding` of the simple-optimised expression), [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4938][g518] (`simplStableUnfolding`, the `_other` branch for INLINABLE things: `mkLetUnfolding env top_lvl src id False expr'`, "we need to make sure the guidance is kept up to date"), [compiler/GHC/CoreToIface.hs#L536][g510] (`toIfGuidance`), [compiler/GHC/IfaceToCore.hs#L1911][g519] (`IfNoGuidance -> calcUnfoldingGuidance uf_opts ...`), [compiler/GHC/Core/Opt/Simplify/Inline.hs#L319][g520] (`tryUnfolding`, the `UnfIfGoodArgs` branch).

**Seen.** `docs/perf-checklist.md` P, the half with `-fexpose-overloaded-unfoldings`: what INLINABLE buys there is "the unfolding taken before the module's own optimisation rather than the optimised one"; U13 is the case where that was better.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/U04-inlinable-unfolding`, variants `noww`, `-O -fno-worker-wrapper -dinline-check f`, and `base`, plain `-O`): a function with an INLINABLE pragma and one without, both calling an INLINE [1] function that the right-hand side inlines and the always-active stable unfolding does not.

```haskell
module A (fPlain, fInlb) where

-- Inlined into a right-hand side from phase 1 on, but never into an
-- always-active stable unfolding (U10).
g :: Int -> Int -> Int
{-# INLINE [1] g #-}
g x y
  | x > 1000 = x * y + 7 * x - y
  | x > 500 = x - y * 3 + 11
  | x > 300 = (x + y) * (x - y) + 5
  | x > 200 = x * x * y - 13
  | x > 100 = x * y * y + 17 * x - 3 * y
  | x > 50 = (x - 7) * (y + 9) - x * 21
  | x > 10 = x * 31 + y * 37 - x * y * 41
  | otherwise = (x + 43) * (y - 47) * (x - y)

fPlain :: Int -> Int
fPlain x = g x x + 1

fInlb :: Int -> Int
{-# INLINABLE fInlb #-}
fInlb x = g x x + 2
```

```haskell
module B (usePlain, useInlb) where

import A

usePlain :: Int -> Int
usePlain n = fPlain n + 1

useInlb :: Int -> Int
useInlb n = fInlb n + 1
```

In `noww`, `fInlb`'s optimised right-hand side has `g` inlined (`fInlb = \ x -> case x of { I# x1 -> case ># x1 1000# of ...`), while its interface unfolding is the source form with no guidance, `Inline:, Unfolding: Core: StableUser \ (x['GHC.Internal.Types.Many] :: GHC.Internal.Types.Int) -> case g x x of wild ...`. Compiling B, the two decisions at the `+` (a `case` context) are:

```
Considering inlining: fInlb
  ...
  guidance IF_ARGS [0] 51 10
  ...
  adjusted size = 21
  ANSWER = YES
Considering inlining: fPlain
  ...
  guidance IF_ARGS [20] 245 60
  ...
  adjusted size = 165
  ANSWER = NO
```

so B inlines `fInlb` and then `g` (`Inlining done: g`), and keeps the call `usePlain = \ n -> case fPlain n of { I# x -> I# (+# x 1#) }`. In `base`, `fInlb`'s unfolding has become `CPR: 1, Inline:, Unfolding: Core: StableSystem <1,TrueFalse> \ (x['GHC.Internal.Types.Many] :: GHC.Internal.Types.Int) -> case g x x of wild ...`, still the source form, and B inlines it and `g`, while it calls `fPlain`'s worker, `case $wfPlain ww of ww1 { __DEFAULT -> I# (+# ww1 1#) }`.

**Reproduces small:** yes.

### U05. Which unfoldings the interface carries: every stable one, a vanilla one only when GHC might inline it, and more or fewer under the exposure flags

**Rule.** Tidy decides, binding by binding, whether the unfolding goes into the interface; one that does not is trimmed to its evaluatedness (`OtherCon []` in `-ddump-simpl`, which prints Tidy Core). By default (`ExposeSome`) it exposes every stable unfolding, INLINE, INLINABLE, worker/wrapper's and compulsory alike, a DFun unfolding, and a vanilla one only when "profitable": not NOINLINE (never active), not a strong loop breaker, and with guidance that is `UnfWhen`, or `UnfIfGoodArgs` for a function that is not bottoming. A vanilla unfolding over the creation threshold (750 by default) has guidance `UnfNever` and is not exposed; one between the use threshold (90) and the creation threshold is exposed though an importer rarely inlines it. The test applies to each binding in its final form, so the worker of a function over the threshold, a new binding and smaller for taking unboxed arguments, can fall under it and be exposed: A13's `hugeN` had guidance `NEVER` before worker/wrapper and its worker `$whugeN` `IF_ARGS [498 0] 490 0` after, read with `-dverbose-core2core`. `-fexpose-all-unfoldings` exposes every unfolding, NOINLINE, loop breaker, bottoming and `UnfNever` ones included, the loop breakers printed `Unfolding(loop-breaker):`. `-fexpose-overloaded-unfoldings` adds the unfolding of every binding whose type has a constraint (equalities included), loop breakers and NOINLINE ones included, unless it is bottoming. `-fomit-interface-pragmas`, which `-O0` sets, exposes none but compulsory unfoldings (U11); `-O0` also sets `-fignore-interface-pragmas`, so an `-O0` importer loads none but compulsory ones. The flags are tested in that order, so `-fomit-interface-pragmas` wins over both exposure flags and `-fexpose-all-unfoldings` over `-fexpose-overloaded-unfoldings`. An exposed loop breaker is still inlined only by `inline` (A11). Source: [compiler/GHC/Iface/Tidy.hs#L704][g207] (`addExternal`; at line 731 `show_unfolding (CoreUnfolding ...) = stable || profitable || explicitly_requested`, with `profitable` false for `never_active` and `loop_breaker` and `UnfIfGoodArgs {} -> not bottoming_fn`, and `explicitly_requested` per exposure level), [Iface/Tidy.hs#L762][g521] (`isOverloaded`) and Note [Exposing overloaded functions] below it, [Iface/Tidy.hs#L1313][g522] (`tidyTopIdInfo`: an unexposed unfolding becomes `trimUnfolding unf_info`), [compiler/GHC/Driver/Config/Tidy.hs#L47][g523] (the order of the flags), [compiler/GHC/Driver/DynFlags.hs#L1307][g524] (`-fignore-interface-pragmas` and `-fomit-interface-pragmas` at `-O0` only), [compiler/GHC/IfaceToCore.hs#L1849][g525] (`need_prag`: an importer ignoring pragmas still loads a compulsory unfolding), [compiler/GHC/Core/Unfold.hs#L351][g463] (`TooBig -> UnfNever`).

**Seen.** `docs/perf-checklist.md` I2: `-fexpose-overloaded-unfoldings` exposes loop breakers' unfoldings too; P's two halves, which are split by whether a module is built `-fexpose-overloaded-unfoldings`.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/U05-exposure`, variants `base` `-O`, `all` `-O -fexpose-all-unfoldings -dinline-check huge`, `ovl` `-O -fexpose-overloaded-unfoldings`, `omit` `-O -fomit-interface-pragmas`, `O0` `-O0`, and `idinfo`, below): one module of bindings that worker/wrapper leaves alone, of each kind, and an importer of the two largest.

```haskell
module A (pick, mid, huge, noinl, countDown, countDownN, oops, inl) where

-- Nothing here but inl gives worker/wrapper anything to split: the arguments
-- are lazy or polymorphic and no result is a single-constructor value, and
-- worker/wrapper leaves an INLINE function alone.

-- Small: exposed.
pick :: Bool -> a -> a -> a
pick b x y = if b then x else y

-- Too big to inline at the default use threshold, under the creation threshold.
mid :: Int -> [Int]
mid n = [n + 1, n + 2, ..., n + 20]          -- written out in A.hs

-- Over the creation threshold: no guidance but UnfNever.
huge :: Int -> [Int]
huge n = [n + 1, n + 2, ..., n + 150]        -- written out in A.hs

noinl :: Bool -> a -> a -> a
{-# NOINLINE noinl #-}
noinl b x y = if b then y else x

-- Self-recursive: its own loop breaker.
countDown :: Int -> [Int]
countDown n = if n == 0 then [] else n : countDown (n - 1)

countDownN :: (Eq a, Num a) => a -> [a]
countDownN n = if n == 0 then [] else n : countDownN (n - 1)

-- Bottoming.
oops :: [Int] -> a
oops xs = errorWithoutStackTrace ("oops " ++ show (length xs))

inl :: Int -> Int -> Int
{-# INLINE inl #-}
inl x y = x * y + 1
```

```haskell
module B (useHuge, useMid) where

import A

useHuge :: Int -> Int
useHuge n = head (huge n)

useMid :: Int -> Int
useMid n = head (mid n)
```

Which bindings carry an unfolding in `A.iface` (`V` vanilla, `S` StableUser, `-` none):

```
            base  all  ovl  omit  O0
pick        V     V    V    -     -
mid         V     V    V    -     -
huge        -     V    -    -     -
noinl       -     V    -    -     -
countDown   -     V    -    -     -
countDownN  -     V    V    -     -
oops        -     V    -    -     -
inl         S     S    S    -     -
```

In `base`, for example, `huge :: GHC.Internal.Types.Int -> [GHC.Internal.Types.Int] [HasNoCafRefs, TagSig: <TagFun[TagEPT]>, LambdaFormInfo: LFReEntrant 1, Arity: 1, Strictness: <L>]` ends without an unfolding, while `mid` (size 620: `Guidance=IF_ARGS [400] 620 10` in Tidy Core, variant `idinfo`, `-O -ddump-simpl -dsuppress-uniques`) ends `Unfolding: Core: <vanilla>`; in `all`, the recursive ones end `Unfolding(loop-breaker): Core: <vanilla>`, and B, recomputing `huge`'s guidance, prints `Considering inlining: huge UnfNever`. In `omit` and `O0`, `inl :: GHC.Internal.Types.Int -> GHC.Internal.Types.Int -> GHC.Internal.Types.Int []` carries nothing and the interface has no `Unfolding` at all.

**Reproduces small:** yes.

### U06. An importer recomputes the guidance of every imported unfolding not marked always-inline, with its own thresholds, so `-funfolding-creation-threshold` also decides which imported functions it inlines

**Rule.** Only a stable unfolding with `UnfWhen` guidance (INLINE, a tiny INLINABLE one, a worker/wrapper or `certainlyWillInline` one, a compulsory one) carries its guidance in the interface. For every other one, vanilla or INLINABLE, the importer computes the guidance from the template when it loads it, with its own `UnfoldingOpts`; so a template over the importing module's creation threshold gets `UnfNever` there and is not inlined, though the module that wrote it was built with a higher threshold. This holds for base's functions too: compiling a module with `-funfolding-creation-threshold=30` stops it inlining any imported template over 30, and that includes the simplification of its own INLINE unfoldings, so the INLINE unfoldings it stores are less simplified, and calls in them stay calls. An importer at the default threshold, inlining such a stored unfolding, simplifies the template again with its own options and recovers what the threshold cost. Source: [compiler/GHC/CoreToIface.hs#L536][g510] (`toIfGuidance`: `IfWhen` only for a stable `UnfWhen` unfolding), [compiler/GHC/IfaceToCore.hs#L1906][g511] (`tcUnfolding`: `IfNoGuidance -> calcUnfoldingGuidance uf_opts is_top_bottoming False expr`, `uf_opts` from the importer's `DynFlags`), [compiler/GHC/Core/Unfold.hs#L349][g23] (`calcUnfoldingGuidance`: `TooBig -> UnfNever`, with `bOMB_OUT_SIZE = unfoldingCreationThreshold opts` at line 368), [Unfold.hs#L96][g526] (`defaultUnfoldingOpts`: creation threshold 750, use threshold 90), [compiler/GHC/Driver/Session.hs#L1872][g527] (`-funfolding-creation-threshold` sets `updateCreationThreshold`).

**Seen.** `docs/perf-checklist.md` P, the thin-wrapper paragraph (Mikolaj's ruling of 2026-10-13): with the package built `-funfolding-creation-threshold=30`, `all` among base's functions was not inlined into the INLINE unfoldings a module stores.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/U06-importer-guidance`, variants `base` `-O -dinline-check scale`, `t30` `-O -funfolding-creation-threshold=30 -dinline-check scale`, with `-ddump-rule-firings`, and `t30all1` `-O -funfolding-creation-threshold=30 -dinline-check all1`, both modules alike; and `mixed`, A at 30 and B at the default, made by the case's `post` hook, `~/r/horde-ad/dist-inlcat/cases/U06-importer-guidance/mixed.sh`): an INLINE function calling base's `all` and an INLINABLE overloaded one, and an importer of both.

```haskell
module A (allEven, scale) where

allEven :: [Int] -> Bool
{-# INLINE allEven #-}
allEven xs = all even xs

scale :: Num a => a -> a -> a
{-# INLINABLE scale #-}
scale k x = k * x + k * k + x * x + 3
```

```haskell
module B (useScale, useAll) where

import A

useScale :: Int -> Int
useScale n = scale n (n + 1)

useAll :: Int -> Bool
useAll n = allEven [1 .. n]
```

From the same kind of template, B computes `guidance IF_ARGS [630 0 0] 280 0` for `scale` in `base` and `Considering inlining: scale UnfNever` in `t30` (B still gets `scale`'s arithmetic in `t30`, by specialising the INLINABLE `scale` at `Int`: `Rule fired: SPEC/B scale @Int (B)`). Compiling A in `t30all1` prints `Considering inlining: all1 UnfNever`, and the INLINE unfolding A stores differs. At the default threshold it is base's `all` inlined into a `foldr` over `map`:

```
Unfolding: Core: StableUser <1,FalseFalse>
  (\ (xs['GHC.Internal.Types.Many] :: [GHC.Internal.Types.Int]) ->
   GHC.Internal.Base.foldr ...
```

and at 30 a call of Foldable's `all1` with the list instance's dictionary:

```
Unfolding: Core: StableUser <1,FalseFalse>
  (\ (xs['GHC.Internal.Types.Many] :: [GHC.Internal.Types.Int]) ->
   GHC.Internal.Data.Foldable.all1
     @[]
     @GHC.Internal.Types.Int
     GHC.Internal.Data.Foldable.$fFoldableList
     GHC.Internal.Float.$seven
     xs)
```

With both modules at 30, B builds the list and passes it to that call, `useAll1 = \ n -> lvl (case n of { I# y -> eftInt 1# y })`; at the default threshold, and in `mixed` with A at 30 and B at the default, B's `useAll1` is one loop, `jump go2 (+# x 1#);`, with no list.

**Reproduces small:** yes.

### U07. Worker/wrapper does not split a small function but gives it an always-inline stable unfolding, which from then on is not refreshed from the right-hand side

**Rule.** When worker/wrapper could split a function but it is small by `certainlyWillInline` (its unfolding `UnfWhen`, or `UnfIfGoodArgs` with its size, less ten for each argument and ten more, within the use threshold, arity above zero, not bottoming, not NOINLINE), it leaves the function whole and gives it a `StableSystemSrc` unfolding with `UnfWhen` guidance, `unsat_ok` True and `boring_ok` by `inlineBoringOk` (an unfolding already `UnfWhen` keeping its own guidance). The template is the right-hand side as it stood at that moment, or, for a function already carrying a stable unfolding, that unfolding's template; so a small INLINABLE function becomes an always-inline one over its source form (U04, variant `base`), keeping its INLINABLE pragma. Being stable, the unfolding is from then on only simplified as a stable unfolding is (U10), not remade from the right-hand side: in particular it is always active, so the wrapper of a function it calls, active only from phase 2, is never inlined into it, and the template keeps calling the wrapper while the right-hand side calls the worker. Note [Don't w/w inline small non-loop-breaker things] gives the reason (a function small at worker/wrapper time can grow later) and Note [Inline pragma for certainlyWillInline] accepts the wrapper call. The interface shows such a function with `Unfolding: Core: StableSystem <arity,TrueFalse>` and, unlike a wrapper, no `Inline:` activation. Source: [compiler/GHC/Core/Opt/WorkWrap.hs#L785][g528] (`splitFun`: `Just stable_unf <- certainlyWillInline uf_opts fn_info opt_wwd_rhs` returns the binding unsplit with that unfolding), [compiler/GHC/Core/Unfold/Make.hs#L383][g529] (`certainlyWillInline`: `src' = StableSystemSrc` unless compulsory, line 400; `tmpl' | isStableSource src = uf_tmpl fn_unf | otherwise = occurAnalyseExpr rhs'`, line 403; the size test in `do_cunf`), [Make.hs#L461][g530] (Note [certainlyWillInline: INLINABLE]: a large INLINABLE function must be split instead), [WorkWrap.hs#L369][g531] (Note [Don't w/w inline small non-loop-breaker things]), [WorkWrap.hs#L736][g532] (Note [Inline pragma for certainlyWillInline]).

**Seen.** Orthotope's commit "Give the generic arrays' rnf one form", replacing DynamicG's Generic-default `rnf` with RankedG's INLINE form, recorded rnf of a Dynamic Storable or Unboxed array running 5 fewer instructions a call, of 151 and 213. In `~/r/horde-ad/dist-inlcat/cases/U07-rnf-generic-default` (variants `generic` and `one`, the latter the INLINE form, by `-DONE`) the default method, given no pragma, gets a `StableSystem <2,TrueFalse>` unfolding, as this entry's small function does, whose template calls the module's own loop over the shape, `case $fNFDataArray_go1 g1 of wild1 { () -> $fNFDataArray_$crnf1 @k @v @a $dNFData g2 } }]` (`G.iface`, whitespace collapsed), so the Storable wrapper's `rnf` calls that loop's worker, `case $wgo4 g1 of { (# #) -> case $wgo4 g4 of { (# #) -> () } }`; the INLINE form's template, `StableUser <2,FalseFalse>`, carries the loop, which the wrapper gets as a join point, `jump go4 sh`. Both run 22.00 instructions a call (`measure.sh 2000000`), so the recorded 5 do not reproduce small.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/U07-small-function-stable-unfolding`, variant `base`): a small function calling a large one that worker/wrapper splits, and an importer of the small one.

```haskell
module A (big, small) where

-- Split by worker/wrapper: strict in both arguments, an Int result.
big :: Int -> Int -> Int
big x y
  | x > 1000 = x * y + 7 * x - y
  | x > 500 = x - y * 3 + 11
  | x > 300 = (x + y) * (x - y) + 5
  | x > 200 = x * x * y - 13
  | x > 100 = x * y * y + 17 * x - 3 * y
  | x > 50 = (x - 7) * (y + 9) - x * 21
  | x > 10 = x * 31 + y * 37 - x * y * 41
  | otherwise = (x + 43) * (y - 47) * (x - y)

-- Small: given a stable unfolding instead of a split.
small :: Int -> Int
small x = big x x + 1
```

```haskell
module B (useSmall) where

import A

useSmall :: Int -> Int
useSmall n = small n * 2
```

`small` has no worker (`$wsmall` is absent) and its interface entry ends `Strictness: <S!P(L)>, CPR: 1, Unfolding: Core: StableSystem <1,TrueFalse> \ (x['GHC.Internal.Types.Many] :: GHC.Internal.Types.Int) -> case big x x of wild ...`: a call of `big`'s wrapper, whose own entry reads `Inline: [2], Unfolding: Core: StableSystem <2,TrueFalse>`. `small`'s right-hand side calls the worker:

```
small
  = \ x ->
      case x of { I# ww ->
      case $wbig ww ww of ww1 { __DEFAULT -> I# (+# ww1 1#) }
      }
```

B inlines `small` and then `big` (`Inlining done: small`, `Inlining done: big`) and ends with `case $wbig ww ww of ww2 { __DEFAULT -> I# (+# 2# (*# 2# ww2)) }`, the same call as the right-hand side's.

**Reproduces small:** yes.

### U08. Worker/wrapper splits an INLINABLE function and moves its stable unfolding to the worker, so importers can still specialise it

**Rule.** Unless it is small enough for U07, an INLINABLE function is split like any other. The wrapper gets the usual wrapper unfolding and activation (A26); the worker gets the INLINABLE unfolding, the original template applied to the worker's arguments by the worker/wrapper's own transformation and run through the simple optimiser, with its guidance recomputed, and both wrapper and worker keep the INLINABLE pragma (the user's `InlineSpec`), the worker with the wrapper's activation. A self-recursive INLINABLE function is split too, the worker becoming the loop breaker that carries the stable unfolding. Because the specialiser specialises an imported function on the strength of a user INLINABLE or INLINE pragma and an unfolding, stable or not, an importer specialises the worker as well as the wrapper. Source: [compiler/GHC/Core/Opt/WorkWrap.hs#L862][g533] (`mkWWBindPair`: the worker gets `mkWorkerUnfolding simpl_opts work_fn fn_unfolding`), [WorkWrap.hs#L840][g534] (`work_prag`: `inl_inline = fn_inline_spec`), [compiler/GHC/Core/Unfold/Make.hs#L126][g535] (`mkWorkerUnfolding`: for a stable source, `new_tmpl = simpleOptExpr opts (work_fn tmpl)`, guidance from `calcUnfoldingGuidance`), [WorkWrap.hs#L186][g536] (Note [Worker/wrapper for INLINABLE functions], GHC [#6056](https://gitlab.haskell.org/ghc/ghc/-/work_items/6056)).

**Seen.** `docs/perf-checklist.md` I2: "INLINABLE does not [block worker/wrapper], and moves its stable unfolding to the worker". Orthotope's commit "Inline update in the wrapper modules" recorded INLINE in place of INLINABLE on the wrappers' `update` running 0.76 to 0.77 times the instructions and allocating 0.70 to 0.71 times as much at Storable and Unboxed elements and in boxed Shaped, and 0.97 to 0.98 times the instructions in boxed Dynamic and Ranked, an update of a [50, 40] array of Doubles by 2000 pairs. In `~/r/horde-ad/dist-inlcat/cases/U08-update-inlinable-wrapper` (variants `inlinable` and `inline`, the latter by `-DINL`; `measure.sh N`), under INLINABLE the Storable wrapper's worker is specialised at the client from the unfolding it carries, `"SPEC/Main $wupdateS @Double" [2] forall $dIP14 $dStorable. $wupdateS $dIP14 $dStorable = $s$wupdateS $dIP14`, and the boxed wrapper, with no dictionary to specialise on, is called out of line, `case $wupdateB (C:IP $dIP13) ww3 ww4 (go2 0#) of` (`Main.dump-simpl`, whitespace collapsed). Under INLINE the boxed call runs 0.976 times the instructions, as recorded, and the Storable one 0.996, allocating the same, so the Storable, Unboxed and Shaped gain does not reproduce small; nor did it in a client of orthotope's library built with an INLINABLE copy of the wrapper (0.992; no case kept). The gain came from the measuring probe, not from `update`: the probe's list producer `pairs` is INLINE, HEAD inlines it from an unfolding left unfused, and with `pairs` given no pragma the gain is gone (section 6, item 10).

**Repro** (`~/r/horde-ad/dist-inlcat/cases/U08-inlinable-worker`, variants `base`, with `-ddump-rule-firings`, and `idinfo`, the latter `-O -ddump-simpl -dsuppress-uniques -dsuppress-module-prefixes` to show the pragmas): a self-recursive INLINABLE overloaded function strict in an `Int`, and an importer at `Double`.

```haskell
module A (sumTo) where

-- Self-recursive, overloaded, strict in its Int.
sumTo :: Num a => Int -> a -> a
{-# INLINABLE sumTo #-}
sumTo n acc = if n == 0 then acc else sumTo (n - 1) (acc + fromIntegral n)
```

```haskell
module B (useSum) where

import A

useSum :: Int -> Double
useSum n = sumTo n 0
```

The wrapper's entry reads `sumTo [InlPrag=INLINABLE[2]]` and its interface unfolding `Inline: [2], Unfolding: Core: StableSystem <3,TrueFalse> ... case n of wild { GHC.Internal.Types.I# ww -> $wsumTo @a $dNum ww acc }`. The worker's entry reads `$wsumTo [InlPrag=INLINABLE[2], Occ=LoopBreaker]`, and its unfolding is the INLINABLE source applied to the unboxed `Int#`, still comparing boxed values:

```
Inline: [2],
Unfolding(loop-breaker): Core: StableUser
  \ @a ($dNum ...) (ww ... :: GHC.Internal.Prim.Int#) (acc ... :: a) ->
  case GHC.Internal.Classes.eqInt
         (GHC.Internal.Types.I# ww)
         (GHC.Internal.Types.I# 0#) of wild { ...
```

B specialises both (`Rule fired: SPEC/B $wsumTo @Double (B)`, `Rule fired: SPEC/B sumTo @Double (B)`), and its loop runs on `Double#`: `__DEFAULT -> $w$s$wsumTo (-# wild 1#) (+## ww1 (int2Double# wild));`.

**Reproduces small:** yes.

### U09. INLINE stops worker/wrapper, even on a self-recursive function that, as its own loop breaker, is not inlined

**Rule.** `tryWW` leaves a function whole when `hasInlineUnfolding` holds, that is, when it has a stable unfolding with `UnfWhen` guidance or a DFun unfolding, as every INLINE function has (Note [Don't w/w INLINE things]: splitting would overwrite the stable unfolding with the wrapper's). `hasInlineUnfolding` tests `realUnfoldingInfo`, the unfolding a loop breaker keeps though `idUnfolding` hides it, so this holds for a self-recursive INLINE function as well, which as its own loop breaker is not inlined (A11): it gets neither a worker nor its strictness and CPR benefits, and its recursive calls box their arguments and its result. A non-recursive INLINE function loses nothing by this, its callers inlining its unfolding instead (U03, where `$wsumSq` is absent). The comment on `hasInlineUnfolding` calls returning True for a loop breaker with an INLINE pragma "very important", citing (CWW4) of Note [Cast worker/wrapper] and GHC [#26903](https://gitlab.haskell.org/ghc/ghc/-/work_items/26903), which concern cast worker/wrapper; GHC [#27868](https://gitlab.haskell.org/ghc/ghc/-/work_items/27868) reports the effect on strictness worker/wrapper. Source: [compiler/GHC/Core/Opt/WorkWrap.hs#L561][g537] (`tryWW`: `| hasInlineUnfolding fn_info = return [(new_fn_id, rhs)]`), [WorkWrap.hs#L167][g538] (Note [Don't w/w INLINE things]), [compiler/GHC/Types/Id/Info.hs#L633][g539] (`hasInlineUnfolding info = isInlineUnfolding (realUnfoldingInfo info)` and its comment), [compiler/GHC/Core.hs#L2042][g540] (`isInlineUnfolding`: a stable unfolding with `UnfWhen`, or a DFun unfolding), [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L521][g541] ((CWW4) in Note [Cast worker/wrapper]).

**Seen.** GHC [#27868](https://gitlab.haskell.org/ghc/ghc/-/work_items/27868) (`docs/ghc-issue-inline-blocks-ww.md`), found on horde-ad's tensor-kind dispatchers; `docs/perf-checklist.md` I2 ("INLINE blocks worker/wrapper even where it cannot be honoured"), whose Read gives the remedies: INLINABLE (U08) or NOINLINE (A24) instead, or a non-recursive INLINE wrapper over the recursive worker, and records dropping orthotope's INLINE on `getStridesT`.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/U09-inline-blocks-ww`, variant `base`, `run` = `inline 10000000`): the filed reproducer of GHC [#27868](https://gitlab.haskell.org/ghc/ghc/-/work_items/27868), unchanged: the same self-recursive function with and without INLINE, side by side.

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

`$wsumCountInline` does not exist; `sumCountInline` recurses on boxed values, `sumCountInline (I# (-# wild 1#)) (I# (+# ipv1 wild)) (I# (+# ipv2 1#));`, while the function without the pragma loops on `Int#` and returns an unboxed pair, `$wsumCountPlain (-# wild 1#) (+# ww1 wild) (+# ww2 1#);`. Run with `inline 10000000`, it prints `(50000005000000,10000000)` and reports `480,058,624 bytes allocated in the heap`, 48 bytes an iteration.

**Reproduces small:** yes.

### U10. A stable unfolding is simplified at every simplifier pass, but only with the inlinings and rules active throughout its own activation, and without eta-expansion

**Rule.** Each time the simplifier processes a binding with a stable unfolding it simplifies the unfolding too, in the current pass's mode with three changes: the phase becomes the range from the unfolding's activation, widened to include the current phase, and an inlining or rule applies inside only if it is active throughout that range (Note [What is active in the RHS of a RULE or unfolding?], (WAR1) and (WAR2)); eta-expansion is off (the template is eta-expanded only at its top, to the binding's arity, Note [Eta-expand stable unfoldings]); and inlining is on whatever the mode says. So an always-active INLINE or INLINABLE unfolding never takes anything with a phase on it: a function `INLINE [n]` or `NOINLINE [n]`, a rule active only from or until a phase, a worker/wrapper wrapper (active from phase 2, U07, A26), while an unfolding with the same activation takes it from that phase on. So a [~1] function called inside an INLINE [1] function is not inlined into the latter's unfolding, and once that unfolding is inlined in phase 1, the [~1] function is inactive and its call stays for good (`outer` in A10's repro). SpecConstr relies on this: it makes its rules for a function active one phase after the function's own activation, so that they never fire in the function's stable unfolding and an importer can still specialise the unfolding's recursive calls by type class ([compiler/GHC/Core/Opt/SpecConstr.hs#L2132][g542], Note [SpecConstr: rule activation]). No other pass rewrites the template: float-out, exitification, SpecConstr and CSE transform right-hand sides only, though CSE can drop the unfolding altogether (U02); worker/wrapper moves it to the worker (U08) or keeps its template under always-inline guidance (U07), passing it through the simple optimiser only; demand analysis uses it (U16); and the specialiser copies it into a specialised binding (U12). The mode it inherits from the pass includes the first, "gentle" pass's `sm_case_case = False`, under which on this branch no continuation holds a `Select`, a `StrictBind` or a `StrictArg` ((COC-INV) in Note [sm_case_case: switching off case continuations], [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L2168][g543]; the scrutinee's case in `simplExprF1`, [#L1286][g544]), so a `case` around a `let` stays outside it there, inside stable unfoldings as elsewhere, and a `letrec` in the scrutinee can still become a join point (GHC [#27737](https://gitlab.haskell.org/ghc/ghc/-/work_items/27737), the second repro). An occurrence in a stable unfolding counts as many, so a binding used once there is not pre-inlined into it (A16). Source: [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4897][g545] (`simplStableUnfolding`, with `unf_env = updMode (updModeForStableUnfoldings act) env` at line 4951 and `eta_expand` below it), [compiler/GHC/Core/Opt/Simplify/Utils.hs#L1207][g260] (`updModeForStableUnfoldings`: `sm_phase = phaseForRuleOrUnf ...`, `sm_eta_expand = False`, `sm_inline = True`), [Utils.hs#L1246][g546] (`phaseForRuleOrUnf`), [Utils.hs#L1371][g547] (Note [What is active in the RHS of a RULE or unfolding?]), [Utils.hs#L1449][g134] (Note [Simplifying inside stable unfoldings]), [Iteration.hs#L4964][g272] (Note [Eta-expand stable unfoldings]) and [Iteration.hs#L2168][g543] (Note [sm_case_case: switching off case continuations]).

**Seen.** `docs/perf-checklist.md` P, the thin-wrapper paragraph: what an INLINE unfolding stores depends on what is inlined into it (U06); `docs/perf-checklist.md` P, "Common principles", on a phase control, `INLINE [n]`, kept to order inlining against rules or specialisation (horde-ad's `tscatterZRDict` and `tscatterZSDict`).

**Repro** (`~/r/horde-ad/dist-inlcat/cases/U10-simplifying-stable-unfoldings`, variant `base`): an INLINE [1] function called by an always-active INLINE function and by one active from phase 1.

```haskell
module A (fAlways, fPhase1) where

g :: Int -> Int
{-# INLINE [1] g #-}
g x = x * 3 + 1

-- Always active: g is not active throughout, so stays a call.
fAlways :: Int -> Int
{-# INLINE fAlways #-}
fAlways x = g x + 1

-- Active from phase 1, as g is: from phase 1 on, g is inlined into it.
fPhase1 :: Int -> Int
{-# INLINE [1] fPhase1 #-}
fPhase1 x = g x + 2
```

`fAlways`'s unfolding keeps the call, `Inline: (sat-args=1), Unfolding: Core: StableUser <1,FalseFalse> \ (x['GHC.Internal.Types.Many] :: GHC.Internal.Types.Int) -> case g x of wild ...`; `fPhase1`'s has it inlined:

```
Inline: [1] (sat-args=1),
Unfolding: Core: StableUser <1,FalseFalse>
  \ (x['GHC.Internal.Types.Many] :: GHC.Internal.Types.Int) ->
  case x of wild { GHC.Internal.Types.I# x1 ->
  GHC.Internal.Types.I#
    (GHC.Internal.Prim.+# 3# (GHC.Internal.Prim.*# x1 3#)) }
```

Both right-hand sides have `g` inlined: `fAlways = \ x -> case x of { I# x1 -> I# (+# 2# (*# x1 3#)) }` and `fPhase1 = \ x -> case x of { I# x1 -> I# (+# 3# (*# x1 3#)) }`.

A second repro (`~/r/horde-ad/dist-inlcat/cases/U10-gentle-case-unfolding`, variants `base`, `-ddump-ds`, and `v2c`, `-dverbose-core2core`): GHC [#27737](https://gitlab.haskell.org/ghc/ghc/-/work_items/27737)'s shape, `fScrut`, a `letrec` inside a `case` scrutinee that is a join point once `id` is inlined, and `fPushed`, the shape a gentle run pushing the `Select` into the `let` makes of it, as the parent of commit 0f0d5c45c8 does by its source (`git show 0f0d5c45c8^`, its `simplExprF1` pushing the `Select` whatever the mode), written out; both INLINE.

```haskell
module A (fScrut, fPushed) where

{-# INLINE fScrut #-}
fScrut :: Int -> Int
fScrut n = case (let go :: Int -> Int -> (Int, Int)
                     go 0 acc = (acc, n)
                     go k acc = go (k - 1) (acc + k)
                 in id (go n 0)) of (a, b) -> a + b

{-# INLINE fPushed #-}
fPushed :: Int -> Int
fPushed n = let go :: Int -> Int -> (Int, Int)
                go 0 acc = (acc, n)
                go k acc = go (k - 1) (acc + k)
            in case id (go n 0) of (a, b) -> a + b
```

The gentle run keeps the `case` outside, `go` becoming a join point there, `fScrut = \ n -> case joinrec { go ds acc` (`v2c`), and the stored unfoldings in `A.iface` differ: `fScrut`'s `go :: GHC.Internal.Types.Int -> GHC.Internal.Types.Int -> GHC.Internal.Types.Int JoinPoint(2) [Arity: 2, Strictness: <L><L>]`, against `fPushed`'s `go :: GHC.Internal.Types.Int -> GHC.Internal.Types.Int -> (GHC.Internal.Types.Int, GHC.Internal.Types.Int) NotJoinPoint [Arity: 2]` and its `case go n (GHC.Internal.Types.I# 0#) of wild { (,) a b -> GHC.Internal.Num.$fNumInt_$c+ a b }]`.

**Reproduces small:** yes, for the phase range, and for the gentle run's mode inside a stable unfolding: `fScrut`'s stored unfolding keeps `go` a join point, where `fPushed`'s, the shape a pushed `Select` gives, stores a closure returning a pair; and GHC 9.14.1 and 9.12.4, without commit 0f0d5c45c8, store `fPushed`'s shape for `fScrut` too, their gentle run having pushed the `case` into the `letrec`, 9.14.1's `A.iface` giving `go :: GHC.Internal.Types.Int -> GHC.Internal.Types.Int -> (GHC.Internal.Types.Int, GHC.Internal.Types.Int) NotJoinPoint [Arity: 2]` (`~/r/horde-ad/dist-inlcat/cases/U10-gentle-without-commit`). SpecConstr's rule activation is from the source.

### U11. A class's default method gets a compulsory unfolding, so every instance taking the default gets its whole body, as lazy as written, whatever its size and at any optimisation level, and with it the default's INLINE or INLINABLE

**Rule.** The desugarer gives every default method, `$dm...`, a `CompulsorySrc` unfolding of its right-hand side, whatever pragma it carries (`makeCorePair`, the `is_default_method` case, [compiler/GHC/HsToCore/Binds.hs#L444][g548]; set for the default's binding by `abe_prags = IsDefaultMethod`, [compiler/GHC/Tc/TyCl/Class.hs#L310][g549]), with guidance `ALWAYS_IF(arity=0,unsat_ok=True,boring_ok=True)` (`mkCompulsoryUnfolding`, [compiler/GHC/Core/Unfold/Make.hs#L69][g550]). An instance that takes the default has the method `$c... = $dm... @T $dfT`, and the unfolding replaces the call by the default's body at that instance, as if written in the instance: inlined unsaturated, in any context, in every phase (`activeUnfolding` is True for a compulsory unfolding, even when the mode switches inlining off, [compiler/GHC/Core/Opt/Simplify/Inline.hs#L123][g551]), exposed under `-fomit-interface-pragmas` and loaded under `-fignore-interface-pragmas`, so at `-O0` as well ([compiler/GHC/Iface/Tidy.hs#L707][g552] in `addExternal`, [compiler/GHC/IfaceToCore.hs#L1849][g525] in `need_prag`; U05). Note [INLINE and default methods] ([compiler/GHC/Tc/TyCl/Instance.hs#L2533][g553]) gives the reasons: the default method behaves "rather like macros", and the inlining breaks the recursion between the instance's dictionary and its methods. The instance's method also takes the default's pragma, `mkDefMethBind` copying any pragma for which `isAnyInlinePragma` holds, INLINE or INLINABLE ([#L2262][g554]; [compiler/Language/Haskell/Syntax/Binds/InlinePragma.hs#L248][g555]). A point-free default such as `convertE = Right . convert` becomes `\x -> Right (convert x)` once `(.)` is inlined, at the default and at each instance, and the conversion stays a lazy argument of `Right`, a thunk at every call; GHC does not make it strict, since that would change `convertE undefined` from `Right undefined` to `undefined`. A default written strict, `convertE x = Right $! convert x`, converts first at every instance that takes it. So the eta form of a default does not decide its laziness; its strictness, as written, is copied to every instance. The other compulsory unfoldings are GHC's own: newtype constructors' workers and wrappers (Note [Compulsory newtype unfolding], [compiler/GHC/Types/Id/Make.hs#L246][g556]), the wired-in `nullAddr#`, `seq`, `oneShot`, `leftSection`, `rightSection`, `coerce` and `void#` ([compiler/GHC/Builtin/WiredIn/Ids.hs#L169][g557]), and the `unsafeCoerce#` the desugarer makes ([compiler/GHC/HsToCore.hs#L799][g558]).

**Seen.** horde-ad keeps INLINE on the class defaults `tappend` and `tunravelToListShare` (commit 8b78b6566, its comment at `tappend`); and the `rsize` family, reached through `tsize`'s default, cost a micro-benchmark 78% when the unfolding the default carried changed (`docs/pragmas-and-flags.md`, "Pitfalls met"). Orthotope's default `convertE = Right . convert` built `Right` around a thunk at every instance taking it; the strict default gained at most instances and cost bytes at boxed-to-Storable conversions, 8 a call at Dynamic and Ranked arrays and 16 at Shaped ones, there a thunk that tag inference's rewrite makes (E18); made strict in the eleven instances where it gained, the default left lazy, every gain stayed and every cost went: 24 bytes a call fewer and 3 to 10% fewer instructions forced (orthotope's "Build no thunk under Right where a conversion gains by it"); INLINE against INLINABLE on those methods, equal bytes and instructions within 0.02%. And the pragma copied: in the orthotope build of 2026-10-12 that O07 names, the boxed `Vector` instance took the class default of `vUnsafeConcatN` and with it the default's INLINABLE.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/U11-default-method-compulsory`, variants `base` `-O` and `O0` `-O0`): a class with a large default method and no pragma, and an instance in another module taking the default.

```haskell
module A (C (..)) where

class C a where
  op :: a -> Int
  -- A default method too large to inline by size, with no pragma.
  big :: a -> Int -> Int
  big x n
    | n > 1000 = op x * n + 7 * n
    | n > 500 = op x - n * 3 + 11
    | n > 300 = (op x + n) * (op x - n) + 5
    | n > 200 = op x * op x * n - 13
    | n > 100 = op x * n * n + 17 * n
    | n > 50 = (n - 7) * (op x + 9) - n * 21
    | n > 10 = n * 31 + op x * 37 - n * op x * 41
    | otherwise = (n + 43) * (op x - 47) * (n - op x)
```

```haskell
module B (T (..)) where

import A

data T = T Int

-- big comes from the default method.
instance C T where
  op (T k) = k
```

`$dmbig`'s interface entry carries `Unfolding: Core: Compulsory <0,TrueTrue>` at `-O`, and at `-O0`, where nothing else is exposed, `$dmbig :: C a => a -> GHC.Internal.Types.Int -> GHC.Internal.Types.Int [Unfolding: Core: Compulsory <0,TrueTrue> ...`. B never calls `$dmbig`: at `-O0` its method is the default body over the class's dictionaries, `$cbig = \ x n -> case > $fOrdInt n (I# 1000#) of ...`, and at `-O` the body specialised to `T` and split, `$w$cbig = \ ww ww1 -> case ># ww1 1000# of ...`.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/U11-default-method-laziness`, variants `base` and `ds`, `-O -ddump-ds -dsuppress-uniques -dsuppress-module-prefixes`, dumping the desugarer's output): one conversion class with the composition default and one with the strict default, an instance of each taking the default, and a client applying each.

```haskell
{-# LANGUAGE MultiParamTypeClasses #-}
module M where

data V = V !Int [Int]

class Convert a b where
  convert :: a -> b
  convertE :: a -> Either String b
  convertE = Right . convert

class ConvertS a b where
  convertS :: a -> b
  convertES :: a -> Either String b
  convertES x = Right $! convertS x

instance Convert [Int] V where
  convert xs = V (length xs) (reverse xs)

instance ConvertS [Int] V where
  convertS xs = V (length xs) (reverse xs)
```

```haskell
{-# LANGUAGE MultiParamTypeClasses #-}
module C where
import M

useE :: [Int] -> Either String V
useE xs = convertE xs

useES :: [Int] -> Either String V
useES xs = convertES xs
```

The desugarer's default, `Unf=Unf{Src=Compulsory, ... Guidance=ALWAYS_IF(arity=0,unsat_ok=True,boring_ok=True) Tmpl= \ (@a) (@b) ($dConvert [Occ=Once1] :: Convert a b) -> . @b ...`, and instance method, `$cconvertE = $dmconvertE @[Int] @V $fConvertListV`; the interface's `Unfolding: Core: Compulsory <0,TrueTrue>`. The optimised Core (CSE makes the two `convert` methods one):

    $dmconvertE = \ @a @b $dConvert eta -> Right (convert $dConvert eta)
    $fConvertListV_$cconvertE = \ eta -> Right ($fConvertListV_$cconvertS eta)
    $fConvertSListV_$cconvertES = \ x -> case $wlenAcc x 0# of ww1 { __DEFAULT -> Right (V ww1 (reverse x)) }

and in the client `useE = $fConvertListV_$cconvertE`.

**Reproduces small:** yes, the body copied, at `-O0` too; and the thunk a point-free default leaves and a strict default removes. The 16 bytes the strict default cost at orthotope's Shaped boxed-to-Storable conversions are E18's, not looked for here.

### U12. A specialised copy keeps the INLINE unfolding of what it specialises and drops an INLINABLE one; a SPECIALISE pragma's copy, made by the desugarer, gets no stable unfolding at all, so it loses the INLINE unfolding

**Rule.** A specialised copy, made by the specialiser at a call with known dictionaries or by the desugarer for a SPECIALISE pragma, inherits the original's pragma (or the SPECIALISE pragma's own, when it carries one; NOINLINE for an imported function that is a strong loop breaker) and gets `specUnfolding` of the original's unfolding: a stable unfolding with `UnfWhen` guidance (INLINE, a wrapper) is specialised, whatever its size, with its arity reduced by the arguments the specialisation removes; a DFun unfolding is specialised as a DFun unfolding; any other unfolding, an INLINABLE one included, is dropped, the copy then getting a vanilla unfolding from its own right-hand side (Note [Specialising unfoldings], citing GHC [#4874](https://gitlab.haskell.org/ghc/ghc/-/work_items/4874): the optimised specialised right-hand side is usually smaller, and is no longer overloaded). The specialiser takes the binding's unfolding as it stands; but the desugarer specialises for a SPECIALISE pragma before `makeCorePair` has given the function its INLINE or INLINABLE unfolding, and takes the Id the pragma names, which has none: so on this tree a SPECIALISE pragma's copy of an INLINE function in the same module gets no stable unfolding, contrary to Note [Specialising unfoldings]. Such a copy, INLINE in its pragma and vanilla in its unfolding, is then split by worker/wrapper like any function (A26, `INLINE[2]` on the wrapper). Because the specialisation rule is tried before the INLINE unfolding, an importer calling the function at the specialised type gets the copy, and with it no fusion. Source: [compiler/GHC/Core/Unfold/Make.hs#L178][g559] (`specUnfolding`: the `isStableSource src` and `UnfWhen { ug_arity = old_arity } <- old_guidance` case, `noUnfolding` otherwise) and [Make.hs#L223][g560] (Note [Specialising unfoldings]); [compiler/GHC/Core/Opt/Specialise.hs#L1629][g561] (`fn_unf = realIdUnfolding fn`) and [Specialise.hs#L1739][g562] (`spec_unf = specUnfolding ...`), [Specialise.hs#L2413][g446] (Note [Inline specialisations]); [compiler/GHC/HsToCore/Binds.hs#L302][g563] (`dsSpecs rhs prags` runs before `makeCorePair` at line 305 sets the unfolding), [Binds.hs#L1044][g564] (`dsSpec_help`: `fn_unf = realIdUnfolding poly_id`, `poly_id` taken from the pragma), [Binds.hs#L1218][g565] (`specFunInlinePrag`); [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L2579][g102] (Note [tryRules: plan (BEFORE)]: for an Id with an unfolding, specialisation rules are tried before inlining, so "the rewrite rule ... win[s] over inlining when both are active at once").

**Seen.** Not measured as such: `docs/pragmas-and-flags.md` records `SPECIALISE` pragmas in `example/MnistData.hs` and at `afcnnMnistLoss2` that cost allocation, by a mechanism it does not give, this rule a candidate. And S2's INLINE over type-level keys, making one copy per `KnownNat` pair, is the specialiser's route, keeping INLINE.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/U12-specialised-copy-unfolding`, variants `base` with `-ddump-rule-firings`, `idinfo` `-O -ddump-spec -ddump-simpl -dsuppress-uniques -dsuppress-module-prefixes`, and `ectrace` `-O -ddump-ec-trace -dsuppress-uniques`, whose `dsSpec(new route)` trace prints the unfolding the desugarer has): INLINE and INLINABLE functions specialised at `Int` by a SPECIALISE pragma, and twins specialised by the specialiser at an unsaturated call; an importer calling both INLINE functions saturated.

```haskell
module A (sumSqI, sumSqN, sumSqI2, sumSqN2, useI2, useN2) where

-- Specialised by a SPECIALISE pragma.
sumSqI :: Num a => [a] -> a
{-# INLINE sumSqI #-}
{-# SPECIALISE sumSqI :: [Int] -> Int #-}
sumSqI xs = foldr (\x acc -> x * x + acc) 0 xs

sumSqN :: Num a => [a] -> a
{-# INLINABLE sumSqN #-}
{-# SPECIALISE sumSqN :: [Int] -> Int #-}
sumSqN xs = foldr (\x acc -> x * x + acc) 1 xs

-- Specialised by the specialiser, at an unsaturated call.
sumSqI2 :: Num a => [a] -> a
{-# INLINE sumSqI2 #-}
sumSqI2 xs = foldr (\x acc -> x * x + acc) 2 xs

-- Self-recursive, so never inlined instead.
sumSqN2 :: Num a => [a] -> a
{-# INLINABLE sumSqN2 #-}
sumSqN2 [] = 3
sumSqN2 (x : xs) = x * x + sumSqN2 xs

useI2 :: [[Int]] -> [Int]
useI2 = map sumSqI2

useN2 :: [[Int]] -> [Int]
useN2 = map sumSqN2
```

```haskell
module B (totalI, totalI2) where

import A

-- sumSqI has a SPECIALISE pragma at Int, sumSqI2 none.
totalI :: Int -> Int
totalI n = sumSqI [1 .. n]

totalI2 :: Int -> Int
totalI2 n = sumSqI2 [1 .. n]
```

Right after specialisation (`A.dump-spec`), the specialiser's copy of the INLINE function keeps its unfolding, `$ssumSqI2 [InlPrag=INLINE (sat-args=1)] :: [Int] -> Int [LclId, Arity=1, Unf=Unf{Src=StableUser, ... Guidance=ALWAYS_IF(arity=1,unsat_ok=False,boring_ok=False) Tmpl= \ (xs [Occ=Once1] :: [Int]) -> foldr ...`, and its copy of the INLINABLE one has none, `$ssumSqN2 [InlPrag=INLINABLE] :: [Int] -> Int [LclId, Arity=1]`. Both SPECIALISE copies have vanilla unfoldings, `$ssumSqI [InlPrag=INLINE (sat-args=1)] :: [Int] -> Int [LclId, Arity=1, Unf=Unf{Src=<vanilla>, ...` and `$ssumSqN [InlPrag=INLINABLE] ... Unf=Unf{Src=<vanilla>, ...`; the desugarer's trace for `sumSqI` reads `poly_id sumSqI`, `unfolding No unfolding`; and the INLINE copy ends split, `sumSqI_$ssumSqI [InlPrag=INLINE[2]] :: [Int] -> Int`. In B, `Rule fired: USPEC sumSqI @Int (A)` gives `totalI` a list built and consumed:

```
go2
  = \ x ->
      : (I# x)
        (case ==# x ww of {
           __DEFAULT -> go2 (+# x 1#);
           1# -> []
         }); } in
$wgo1 (go2 1#);
```

while `Rule fired: SPEC sumSqI2 @Int (A)` gives `totalI2` the specialised INLINE unfolding, fused into one loop with `join { $j y = +# (*# x x) y } in`.

**Reproduces small:** yes.

### U13. An optimised unfolding carries what the defining module's later passes did at the abstract types, such as an exit join point, which no client inlines; an INLINABLE unfolding, taken before optimisation, carries none of it

**Rule.** A function without a pragma exposes the unfolding of its optimised right-hand side (U01), here its worker's, so an importer that inlines or specialises it gets the code as the defining module's later passes left it, at that module's types and dictionaries: here exitification, which abstracted the loop's last iteration into an exit join point over the boxed loop variables, because the methods, unknown there, take them boxed. An exit join point is never inlined, and is recognised by its occurrence alone, as any join point occurring once inside a lambda (A20), so in the importer, where the methods are known and unbox their arguments in one branch only, the exit join point stays out of the loop, lazy in those variables, and the loop keeps them boxed. An INLINABLE unfolding, taken before optimisation (U04) and moved to the worker by the split (U08), has no exit join point; the importer specialises it and runs its own exitification after its own optimisation, and the loop is unboxed. `-fno-exitification` in the defining module does the same. Within the defining module the specialiser runs before exitification, so a copy made there has no exit join point either (GHC [#27893](https://gitlab.haskell.org/ghc/ghc/-/work_items/27893): "nor when `copyStrided` and the instance are in one module, where the specialiser, which runs before Exitify, copies code that has no exit join point yet"). Source: A20's for the exit join point; the rest as in the filed issue.

**Seen.** GHC [#27893](https://gitlab.haskell.org/ghc/ghc/-/work_items/27893) (`docs/ghc-issue-exit-join-point-boxed-loop.md`), found in orthotope's strided fill; `docs/perf-checklist.md` P, the half with `-fexpose-overloaded-unfoldings`: INLINABLE's unfolding "escaped GHC [#27893](https://gitlab.haskell.org/ghc/ghc/-/work_items/27893)'s boxed loop".

**Repro** (`~/r/horde-ad/dist-inlcat/cases/U13-exit-join-point-in-unfolding`, variants `base` `-O`, `noexit` `-O -fno-exitification` and `inlinable` `-O -DPRAGMA_INLINABLE`; `run` empty): the filed reproducer of GHC [#27893](https://gitlab.haskell.org/ghc/ghc/-/work_items/27893), its `Lib.hs` given CPP and three lines putting INLINABLE on `copyStrided` under `PRAGMA_INLINABLE`, its `Repro.hs` saved as `Main.hs`.

```haskell
{-# LANGUAGE BangPatterns, CPP #-}
module Lib (Store (..), copyStrided) where

class Store f where
  rd :: f -> Int -> IO Int
  wr :: f -> Int -> Int -> IO ()

-- out[o] = inp[o * t] for 0 <= o < n, unrolled by two.
copyStrided :: Store f => f -> f -> Int -> Int -> IO ()
#ifdef PRAGMA_INLINABLE
{-# INLINABLE copyStrided #-}
#endif
copyStrided inp out !n !t = go 0 0
  where
    go !o !src
      | o + 1 >= n = if o >= n then return () else rd inp src >>= wr out o
      | otherwise = do
          rd inp src >>= wr out o
          let !s2 = src + t
          rd inp s2 >>= wr out (o + 1)
          go (o + 2) (s2 + t)
```

```haskell
module Main (main) where
import Control.Monad (forM_)
import Foreign
import Lib

newtype P = P (Ptr Int)
instance Store P where
  rd (P p) i = peekElemOff p i
  wr (P p) i x = pokeElemOff p i x

main :: IO ()
main =
  allocaArray 2000 $ \a -> allocaArray 1000 $ \b -> do
    pokeArray a [0 .. 1999]
    forM_ [1 .. 10000 :: Int] $ \_ -> copyStrided (P a) (P b) 999 2
    xs <- peekArray 999 b
    print (sum xs)
```

In `base`, the worker's interface unfolding is the optimised one, with the exit join point, `exit :: GHC.Internal.Prim.State# GHC.Internal.Prim.RealWorld ...`, `JoinPoint(4) [Arity: 4, Strictness: <L><L><L><L>]`; Main inlines it and its loop jumps with boxed values, `jump go (I# (+# ipv 2#)) (I# (+# s3 2#)) s4`, and the run reports `159,921,808 bytes allocated in the heap`. In `inlinable`, the worker carries `Inline: [2], Unfolding: Core: StableUser` with no `exit`; Main's loop is `jump $wgo (+# ww1 2#) (+# s3 2#) s4`, its own exit join point taking `Int#`s, and the run reports `241,808 bytes allocated in the heap`, as `noexit` does.

**Reproduces small:** yes.

### U14. A join point without a stable unfolding gets none at birth, nor ever if it is taken for an exit join point, so it is not inlined even where inlining would restore a tail call

**Rule.** Unless a join point has a stable unfolding, `simplLetUnfolding` gives it none in two cases, so that it is never inlined at its jumps. A freshly born join point, one made by the simplifier itself (by `mkDupableAlt`, for instance), gets none in the iteration of its birth, to stop join points multiplying when nested cases are duplicated (Note [Do not add unfoldings to join points at birth], GHC [#15360](https://gitlab.haskell.org/ghc/ghc/-/work_items/15360), and its wrinkle (JU1), GHC [#15630](https://gitlab.haskell.org/ghc/ghc/-/work_items/15630)); the test for "freshly born" is the point of GHC [#27885](https://gitlab.haskell.org/ghc/ghc/-/work_items/27885). The checked-in test, `isManyOccs`, also matches a join point the occurrence analyser has analysed and found used many times, for instance through a stable unfolding whose occurrences are all many (U10), so such a join point never gets an unfolding in any iteration. This tree carries the fix proposed in GHC [#27885](https://gitlab.haskell.org/ghc/ghc/-/work_items/27885) as an uncommitted patch to [compiler/GHC/Core/Opt/Simplify/Iteration.hs][g2]: `freshly_born_join_point id = is_join_point && isNoOccInfo (idOccInfo id)`, a newly made join point having no occurrence information at all, which an analysed one always has. The Note's text, wrinkle (JU1) included, still describes the `ManyOccs` test. An exit join point gets no unfolding either (A20), and is recognised by its occurrence, not by its having been made by exitification, so a join point the simplifier made can be taken for one; the patch does not touch that route. Source: [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4846][g507] (`simplLetUnfolding`: `freshly_born_join_point id = return noUnfolding` at line 4850, `isExitJoinId id = return noUnfolding` at line 4855, the test at line 4864) and [Iteration.hs#L4387][g566] (Note [Do not add unfoldings to join points at birth]).

**Seen.** GHC [#27885](https://gitlab.haskell.org/ghc/ghc/-/work_items/27885) (`docs/ghc-issue-freshly-born-join-point.md`), found in horde-ad built with `-flate-dmd-anal`, where the loop of its backward pass lost its tail call; the filed body carries both the patch above and its variant `MinExit`, which takes the exit-join-point route.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/U14-join-points-without-unfolding`, variants `base` `-O`, `late` `-O -flate-dmd-anal` and `lateminexit` `-O -flate-dmd-anal -DMINEXIT`, the last two with `-ddump-stg-final`; `run` = `+RTS -K1m -RTS`; `bin/run-case` exits 1 here, `lateminexit`'s run failing as its `expect` line says): the filed reproducer of GHC [#27885](https://gitlab.haskell.org/ghc/ghc/-/work_items/27885), its `Lib.hs` given CPP to make `MinExit`'s second strict field, its `Repro.hs` saved as `Main.hs`.

```haskell
{-# LANGUAGE CPP #-}
module Lib (S (..), T (..), loop) where

#ifdef MINEXIT
data T = Tip | Bin !Int !Int T T
#else
data T = Tip | Bin !Int Int T T
#endif

data S = S !Int !T

find :: Int -> T -> Int
find k = go
  where
    go Tip = 0
    go (Bin k' v l r)
      | k < k' = go l
      | otherwise = v

loop :: S -> S
loop s@(S n t) = case t of
  Bin k _ l r -> loop (S (n + find k l) r)
  Tip -> s
```

```haskell
import Lib

main :: IO ()
main = do
  let t = foldr (\k r -> Bin k k Tip r) Tip [1 .. 1000000]
      S n _ = loop (S 0 t)
  print n
```

With the patch, `late`'s worker makes its self call a tail call, `__DEFAULT -> $w$wloop $w$wloop_sat wild;` in the final STG, and the run finishes in a 1 MB stack (`exit 0`, no overflow), as `base` does. In `lateminexit` the join point `$j` is not inlined, the call is `case $w$wloop $w$wloop_sat wild of ww3 {` followed by `__DEFAULT -> $j ww3 Tip;`, and the run fails with `Main: Stack space overflow`; the filed issue traces this variant to `$j` getting `OnceL2` and so being taken for an exit join point.

**Reproduces small:** yes, on this tree with its patch; that the unpatched test gives the overflow in `late` as well is from the filed issue, which measured it on HEAD before the patch.

### U15. A bang on an INLINE function's argument stays in the unfolding inlined at every caller, though the argument's demand already makes it strict, and changes the callers' Core

**Rule.** An INLINE unfolding is the right-hand side as written, simplified only as a stable unfolding is (U03, U10), so a bang pattern on an argument, which the desugarer turns into a `case` on it, stays in the unfolding even where demand analysis of the optimised right-hand side finds the argument strict anyway and the bang changes nothing there. Every caller that inlines the unfolding gets the `case`: the argument is evaluated at the call, before the body, where without the bang a computed argument is bound lazily and evaluated where the body first needs it. The bang can also decide whether the unfolding is inlined at all: without it, a wrapper whose body is one call under newtype coercions simplifies to a coercion of the callee, for which `inlineBoringOk` returns `True` and which `simplStableUnfolding` then records as `boring_ok`, so it is inlined even with trivial arguments in a lazy position; with it, the template stays a lambda with two `case`s, `boring_ok` stays False, and there the caller keeps a call of the out-of-line function. Where the banged argument is a literal list, as in orthotope's rows, the `case` meets a `build` not yet evaluated in the gentle run and stays in the caller as a `DEFAULT` case, which the first float-out does not float: `lvlCase` floats only a case with one constructor alternative on an evaluated scrutinee, and never to top level ([compiler/GHC/Core/Opt/SetLevels.hs#L444][g423]). The length the body computes from the list floats to a top-level constant all the same, but a `case` on that constant, a top-level thunk, stays in the caller, and with it the guard on the length and the list the body builds from it; all three run at every call, where with the argument named all three float to top-level constants (second repro). Where the code after the bang takes a vector apart, as a walk over a slice does, case-of-case pushes the bang's `case` on the vector that a selection returns into the selection's branches, and the code after it becomes a join point over the constructor's fields and the case binder, which A18's rule inlines at each jump passing that binder as a constructor, so the code is copied into every branch; without the bang the vector is an argument of the strict `stream`, and the code is a join point taking the vector itself, which no jump passes as a value, so A18 inlines it at none of the jumps (third repro). Source: [compiler/GHC/HsToCore/Binds.hs#L466][g269] (the INLINE unfolding is made from the desugared right-hand side), [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4926][g22] (`simplStableUnfolding`: `new_boring_ok = boring_ok || inlineBoringOk expr'`), [compiler/GHC/Core/Unfold.hs#L293][g13] (`inlineBoringOk`), [compiler/GHC/Core/Opt/Simplify/Inline.hs#L310][g5] (`tryUnfolding`, the `UnfWhen` branch).

**Seen.** Orthotope's Ranked `transpose is = A . G.transpose is . unA`, INLINE, cost 136 bytes a call more when written `transpose !is !a = A (G.transpose is (unA a))`, both arguments strict by its demand (NB against N, NB2 showing the cost to be that wrapper's bang), and nothing when written with the arguments named but not banged. In the two builds' `OpsRanked.dump-simpl` (NB and N) the row's workers, NB's `$wlvl153` and N's `$wlvl155`, differ only at their head: N's tests a top-level constant guard, `case lvl258 of {`, its permutation extended by the untouched dimensions, `is'`, a top-level constant too, where NB's runs `case lvl906 of { ghc-internal:GHC.Internal.Types.I# v1 -> case ghc-internal:GHC.Internal.Prim.># v1 2# of {` and builds `is' = ++ @Int lvl248 (case ghc-internal:GHC.Internal.Prim.># v1 1# of {` at every call (whitespace collapsed); the length is a top-level constant in both, NB's `lvl906` and N's `l`. Their binaries allocate 216 and 352 bytes a call at both small boxed views; the 136 fit the thunk of `[l .. n-1]` and two steps of `++`, not checked in STG. And code copied into branches, moving instructions both ways at equal bytes: orthotope's LN is N2 with `vToList !a = V.toList a` for `vToList = V.toList` in the boxed and Unboxed instances, both INLINE. In N2's row worker for forced Dynamic Storable `ravel` large (`$wlvl615`, `OpsDynamic.dump-simpl`) each branch of the case on the slice jumps to one join point, `case bx3 of wild19 { __DEFAULT -> jump $w$j16 (+# ww10 wild19) ds28 ww12; 0# -> case ==# ww11 ds28 of { __DEFAULT -> jump $w$j16 ww10 ds28 ww12; 1# -> jump $w$j16 ww10 ww11 ww12 } }`, and in LN's the walk is copied into the branches, `case bx3 of { __DEFAULT -> jump $j29; 0# -> case ==# ww11 ds28 of { __DEFAULT -> jump $j29; 1# -> joinrec { $wgo26 ...` (qualifiers dropped, whitespace collapsed). LN runs about 1600 instructions a call fewer of 308753 there, keeping three values fewer on the stack a subarray; 8 fewer (1.1 to 1.6%) at the folds' small cells, where a top-level slice loop called from two branches of the row's worker is inlined into both; and 3 more (0.3 to 0.5%) at Shaped `ravel.one`, whose copied fill function swaps two registers through a C-stack slot (`mov %rbx,0x40(%rsp); mov %rax,%rbx; mov 0x40(%rsp),%rax`, O24's kind). R1N's `vForce !a = genericForce a` copies the slice copy's `runRW#` block into each branch the same way, boxed `force` small 7 to 8 instructions a call fewer in every family.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/U15-bang-in-inline-unfolding`, variants `named` `-O`, `bang` `-O -DBANG`, `ginl` `-O -DGINLINE` and `ginlbang` `-O -DGINLINE -DBANG`, each with `-dinline-check transpose`): a newtype wrapper's INLINE `transpose` over a generic one, out of line or (`GINLINE`) INLINE as orthotope's is, named or banged; and callers in a lazy position and with a computed argument.

```haskell
{-# LANGUAGE CPP, BangPatterns #-}
module A (Arr (..), G (..), transpose, gtranspose) where

data G = G ![Int] ![Int]

gtranspose :: [Int] -> G -> G
#ifdef GINLINE
{-# INLINE gtranspose #-}
#endif
gtranspose is (G sh st) = G (perm sh) (perm st)
  where perm xs = map (xs !!) is

newtype Arr = Arr {unA :: G}

transpose :: [Int] -> Arr -> Arr
{-# INLINE transpose #-}
#ifdef BANG
transpose !is !a = Arr (gtranspose is (unA a))
#else
transpose is a = Arr (gtranspose is (unA a))
#endif
```

```haskell
module B (f1, f2, f3) where

import A

f1 :: Arr -> Arr
f1 a = transpose [1, 0] a

f2 :: [Int] -> Arr -> Int
f2 is a = case transpose (reverse is) a of Arr (G sh _) -> length sh

f3 :: Arr -> [Int] -> (Arr, Int)
f3 a is = (transpose is a, length is)
```

Named, the unfolding is a coercion of the callee, ``Strictness: <SL><1!P(1L,1L)>, CPR: 1, Inline: (sat-args=2), Unfolding: Core: StableUser <2,FalseTrue> gtranspose `cast` ...``; banged, both arguments are as strict, `Strictness: <1L><1!P(L,L)>`, and the unfolding is `StableUser <2,FalseFalse>` beginning ``case is of is1 { DEFAULT -> case a `cast` N:Arr of nt { G ipv ipv1 -> ...``, `gtranspose` inlined into it. In `f3`'s lazy pair, with trivial arguments, `-dinline-check` prints `boring_ok=True ... ANSWER = YES` named and `boring_ok=False ... ANSWER = NO` banged, so the first component is ``((gtranspose is (a `cast` <Co:1>)) `cast` <Co:2>,`` named and `(transpose is a,` banged. In `f2`, the computed argument is `let { is1 = reverse is } in` named and `case reverse is of is1 { __DEFAULT ->` banged. With `gtranspose` INLINE, both forms' unfoldings are lambdas (``case a `cast` N:Arr of wild { G sh st -> ...`` named, ``case is of is1 { DEFAULT -> case a `cast` N:Arr of nt { G sh st -> ...`` banged), `f3` keeps `(transpose is a,` in both, and only `f2`'s `let` against `case` differs.

A second repro (`~/r/horde-ad/dist-inlcat/cases/U15-bang-transpose-float`, variants `named`; `bang`, `-DBANG`; `v2c`, `bang` with `-dverbose-core2core`): orthotope's RankedG shape, a generic `transpose` checking the permutation's length against the rank and extending it by the untouched dimensions, under the wrapper, and a row applying it to a literal permutation.

```haskell
{-# LANGUAGE CPP, BangPatterns #-}
module A (Arr (..), G (..), transpose, gtranspose) where

data G = G ![Int] ![Int]

{-# INLINE gtranspose #-}
gtranspose :: Int -> [Int] -> G -> G
gtranspose n is (G sh st)
  | l > n = error "transpose: rank exceeded"
  | otherwise = G (perm sh) (perm st)
  where l = length is
        is' = is ++ [l .. n - 1]
        perm xs = map (xs !!) is'

newtype Arr = Arr {unA :: G}

transpose :: [Int] -> Arr -> Arr
{-# INLINE transpose #-}
#ifdef BANG
transpose !is !a = Arr (gtranspose 2 is (unA a))
#else
transpose is a = Arr (gtranspose 2 is (unA a))
#endif
```

```haskell
module B (Row (..), row) where

import A

data Row = Row String (Arr -> Arr)

row :: Row
row = Row "transpose" (\ a -> transpose [1, 0] a)
```

The gentle run's output in `v2c` holds the bang's `case` on the literal, ``case build (\ @a c n -> c (I# 1#) (c (I# 0#) n)) of is1 { __DEFAULT -> case a `cast` <Co:1> of { G sh st -> let { l = foldr lengthFB idLength is1 (I# 0#) } in``, and the first float-out's floats the literal and keeps the case, `case lvl of is1 { __DEFAULT ->` (whitespace collapsed). In the final Core of `named`, the guard and `is'` are top-level constants, `row7 = case row_l of { I# x -> tagToEnum# (># x 2#) }` and `row_is' = ++ row_is row3`; in `bang`'s the length is one, `row7 = case $wlenAcc row3 0# of v { __DEFAULT -> I# v }`, while the row's worker runs `case row7 of { I# v1 -> case ># v1 2# of {` and `let { is' = ++ row3 (case ># v1 1# of {` at every call.

A third repro (`~/r/horde-ad/dist-inlcat/cases/U15-bang-method-duplicates`, variants `pf` and `bang` (`-DBANG`); `pfj` and `bangj`, with `-dinline-check $j`, a prefix matching every join point so named; `pfwj` and `bangwj`, with `-dinline-check $w$j`; `pfv` and `bangv`, with `-dverbose-core2core`; `run` is `100000`): orthotope's `wholeOrSliceT` and the slice route of its `toListT`, the list consumed by a fused fold whose step is big enough to keep the walk out of line, in `Lib`; the boxed instance, `vToList` point-free or banged, in `Inst`; and a row summing a whole vector.

```haskell
{-# LANGUAGE Haskell2010, BangPatterns #-}
module Lib (Vector (..), wholeOrSliceT, sumSlice) where

class Vector v where
  vLength :: v a -> Int
  vUnsafeSlice :: Int -> Int -> v a -> v a
  vToList :: v a -> [a]

{-# INLINE wholeOrSliceT #-}
wholeOrSliceT :: Vector v => Int -> Int -> v a -> v a
wholeOrSliceT ao l v
  | ao == 0 && vLength v == l = v
  | otherwise = vUnsafeSlice ao l v

{-# INLINE sumSlice #-}
sumSlice :: Vector v => Int -> Int -> v Double -> Double
sumSlice ao l v = foldr (\ x k !acc -> k (acc + x * x + sin x * cos x + x / 3 + exp (x - acc) + tan (x * acc) + atan (x + 1) * log (x + 2))) id
                         (vToList (wholeOrSliceT ao l v)) 0
```

```haskell
{-# LANGUAGE CPP, BangPatterns #-}
module Inst () where

import qualified Data.Vector as V
import Lib

instance Vector V.Vector where
  {-# INLINE vLength #-}
  vLength = V.length
  {-# INLINE vUnsafeSlice #-}
  vUnsafeSlice = V.unsafeSlice
  {-# INLINE vToList #-}
#if defined(BANG)
  vToList !a = V.toList a
#else
  vToList = V.toList
#endif
```

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import qualified Data.Vector as V
import Inst ()
import Lib
import System.Environment (getArgs)

{-# NOINLINE row #-}
row :: Int -> Int -> V.Vector Double -> Double
row ao l v = sumSlice ao l v

{-# OPAQUE input #-}
input :: Int -> V.Vector Double
input i = V.fromList [fromIntegral i, 1, 2, 3, 4]

main :: IO ()
main = do
  [n] <- map read <$> getArgs
  let go :: Int -> Double -> Double
      go !i !acc | i == n = acc
                 | otherwise = go (i + 1) (acc + row 0 5 (input i))
  print (go 0 0)
```

`Main.verbose-core2core`, the first main Simplifier, whitespace collapsed: `pfv` has `join { $j arg = toListFB lvl breakpoint (stream $fVectorVectora arg) lvl }`; `bangv` has `join { $j = case unsafeSlice $fVectorVectora ao l v of a2 { Vector ipv ipv1 ipv2 -> toListFB lvl breakpoint (stream $fVectorVectora a2) lvl } }` and `True -> case v of a2 { Vector ipv ipv1 ipv2 -> toListFB lvl breakpoint (stream $fVectorVectora a2) lvl }`. `build.log`: `bangj` has, at `case depth = 0` and again at `2`, `Considering inlining: $j arg infos [TrivArg, TrivArg, TrivArg, ValueArg] interesting continuation BoringCtxt some_benefit True is exp: True is work-free: True guidance IF_ARGS [0 0 0 20] 90 0 case depth = 0 inline depth = 1 join (lvl, True, Just True, False) (lvl, True, Just True, False) depth based penalty = 0 adjusted size = 20 ANSWER = YES`, the case binder a value; `pfj` has `Considering inlining: $j arg infos [NonTrivArg] ... guidance IF_ARGS [0] 80 0 case depth = 0 ... adjusted size = 50 ANSWER = NO` and, at a lambda-bound variable, `$j arg infos [TrivArg] interesting continuation BoringCtxt some_benefit False ... case depth = 2 ... adjusted size = 60 ANSWER = NO`. `Main.dump-simpl`: `pf` has `0# -> case ==# ww3 ww1 of { __DEFAULT -> $w$j ww2 ww1 ww4; 1# -> $w$j ww2 ww3 ww4 } }`, two branches calling the walk's worker; `bang` has the walk in all three, `0# -> case ==# ww3 ww1 of { __DEFAULT -> joinrec { $wgo ww5 ww6 = case >=# ww5 ww1 of { __DEFAULT ->`.

**Reproduces small:** yes, as a difference in the callers' Core, and orthotope's per-call guard and `is'`; the allocation was not measured here. The third repro gives the copying under the bang and A18's decision behind it; point-free, the walk's join point takes all three jumps until the late float-out, which levels it, closed, to top level (Note [Floating join point bindings], [compiler/GHC/Core/Opt/SetLevels.hs#L871][g406]), and the final Core inlines it at one call and calls it from the other two, as orthotope's folds have it. With the walk's step using an argument of the row (`~/r/horde-ad/dist-inlcat/cases/U15-walk-free-variable`) the final Core keeps all three jumps to one join point, `case ww of wild { __DEFAULT -> jump $w$j (+# ww2 wild) ww1 ww4; 0# -> case ==# ww3 ww1 of { __DEFAULT -> jump $w$j ww2 ww1 ww4; 1# -> jump $w$j ww2 ww3 ww4 } }`, as orthotope's `ravel` row does, and the banged form copies the walk into all three; that a free variable is what holds orthotope's `$w$j16` in place was not read.

### U16. A binding's demand signature combines the demands of its stable unfolding with those of its right-hand side, so an argument the right-hand side no longer uses stays used, and a boxed use in the unfolding keeps it boxed

**Rule.** When a binding has a stable unfolding, demand analysis analyses the unfolding as well as the right-hand side and combines the two demand types: for each argument and free variable it takes the stronger strictness and the larger usage, because a caller that inlines the unfolding gets the unfolding's behaviour. So an argument that the optimised right-hand side has dropped, for instance by a rule active only from a later phase than the unfolding's (U10), is not absent in the signature if the unfolding still uses it; worker/wrapper then keeps it, and callers compute and pass it. Boxity combines the same way: an argument the unfolding passes boxed to a call stays boxed in the signature, so the worker takes it boxed. Source: [compiler/GHC/Core/Opt/DmdAnal.hs#L1185][g567] (`addUnfoldingDemands`: for a stable unfolding, `maxDmdType rhs_dmd_ty unf_dmd_ty`; used at line 1116), [DmdAnal.hs#L1515][g568] (Note [Absence analysis for stable unfoldings and RULES], GHC [#18638](https://gitlab.haskell.org/ghc/ghc/-/work_items/18638), GHC [#23208](https://gitlab.haskell.org/ghc/ghc/-/work_items/23208)), [compiler/GHC/Types/Demand.hs#L869][g569] (Note [Combining demands for stable unfoldings], GHC [#26416](https://gitlab.haskell.org/ghc/ghc/-/work_items/26416): the maximum of lower bounds, strictness, and of upper bounds, usage).

**Seen.** Not in our record.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/U16-unfolding-demands`, variant `base` with `-ddump-rule-firings`): the same function with and without INLINABLE, calling a NOINLINE function lazy in its last argument through a call that a phase-1 rule, true of that function, rewrites to drop the argument; and an importer of both.

```haskell
module A (g, fPlain, fInlb) where

-- Lazy in y; a rule from phase 1, true of g, drops y at True.
g :: Bool -> Int -> Int -> Int
{-# NOINLINE g #-}
g b x y = if b then x else y
{-# RULES "g/True" [1] forall x y. g True x y = x #-}

-- After phase 1 the right-hand side no longer uses y; the always-active
-- INLINABLE unfolding keeps the call of g, which does (U10).
fPlain :: Int -> Int -> Int
fPlain x y = big (g True x y) 2

fInlb :: Int -> Int -> Int
{-# INLINABLE fInlb #-}
fInlb x y = big (g True x y) 3

-- Large enough that worker/wrapper splits fPlain and fInlb.
big :: Int -> Int -> Int
{-# INLINE big #-}
big r k
  | r > 1000 = r * k + 7 * r
  | r > 500 = r - k * 3 + 11
  | r > 300 = (r + k) * (r - k) + 5
  | r > 200 = r * r * k - 13
  | r > 100 = r * k * k + 17 * r
  | r > 50 = (r - 7) * (k + 9) - r * 21
  | otherwise = (r + 43) * (k - 47) * r
```

```haskell
module B (use) where

import A

use :: Int -> Int
use n = fPlain n (n * 7) + fInlb n (n * 9)
```

`-ddump-rule-firings` prints `Rule fired: g/True (A)` for both right-hand sides. Without a stable unfolding, `fPlain` is `Strictness: <1!P(L)><A>`, `y` absent and `x` unboxed, and its worker is `$wfPlain :: GHC.Internal.Prim.Int# -> GHC.Internal.Prim.Int#`; with INLINABLE, `fInlb` is `Strictness: <1L><MS>`, `y` used and `x` boxed, and its worker is `$wfInlb :: GHC.Internal.Types.Int -> GHC.Internal.Types.Int -> GHC.Internal.Prim.Int#`. B never computes `fPlain`'s `y` and builds `fInlb`'s, though `fInlb`'s code does not use it: `case $wfPlain ww of ww1 { __DEFAULT -> case $wfInlb wild (I# (*# ww 9#)) of ww2 ...`.

**Reproduces small:** yes.

### U17. Cast worker/wrapper moves a stable unfolding to the cast worker, leaving the binding a trivial vanilla unfolding, a coercion of the worker

**Rule.** When the simplifier finds a binding whose right-hand side is a value under a coercion, `x = e |> co` (every function in `IO`, or returning a newtype, once its lambdas are under the cast), it makes a cast worker `$wx = e`, here named `x1`, and rebinds `x = $wx |> co`. A stable unfolding of `x` moves to the worker, composed with the inverse coercion; the binding keeps its name and its pragma (the activation adjusted by `mkCastWrapperInlinePrag`) and gets a vanilla unfolding of the trivial cast, which is inlined everywhere, unsaturated and in boring contexts. The worker is then split by demand worker/wrapper like any function, so an INLINABLE unfolding goes on to the strictness worker (U08) and a small one becomes a `StableSystem` one (U07). Cast worker/wrapper skips an INLINE function (`hasInlineUnfolding`, (CWW4), U09), an OPAQUE one, and a right-hand side that is already a coercion of a variable (CWW1). Source: [compiler/GHC/Core/Opt/Simplify/Iteration.hs#L613][g570] (`tryCastWorkerWrapper`; the guard `not (hasInlineUnfolding info)`, the wrapper's `mkLetUnfolding env top_lvl VanillaSrc bndr False triv_rhs`, and at line 679 `mk_worker_unfolding`: a stable unfolding becomes `unf { uf_tmpl = mkCast unf_rhs (mkSymCo co) }`), [Iteration.hs#L690][g571] (`mkCastWrapperInlinePrag`), [Iteration.hs#L447][g572] (Note [Cast worker/wrapper], (CWW2) on NOINLINE moving to the worker and (CWW3) on the stable unfolding moving to the worker).

**Seen.** Our record has the shape, not a case: GHC [#27893](https://gitlab.haskell.org/ghc/ghc/-/work_items/27893)'s `copyStrided`, in `IO`, is ``copyStrided = copyStrided1 `cast` ...`` in its interface with its INLINABLE unfolding on the strictness worker (U13, variant `inlinable`).

**Repro** (`~/r/horde-ad/dist-inlcat/cases/U17-cast-worker-wrapper`, variants `base` and `idinfo`, the latter `-O -ddump-simpl -dsuppress-uniques -dsuppress-module-prefixes -dsuppress-coercions`): the same overloaded `IO` function with and without INLINABLE, large enough not to be inlined whole.

```haskell
module A (stepInlb, stepPlain) where

import Data.IORef

-- In IO, so the optimised right-hand side is a lambda under a cast.
stepInlb :: (Ord a, Num a) => IORef a -> a -> IO ()
{-# INLINABLE stepInlb #-}
stepInlb r x = do
  v <- readIORef r
  if v > x then writeIORef r (v - x)
  else if v > 2 * x then writeIORef r (v * x - 7)
  else if v > 3 * x then writeIORef r (v + x * x)
  else writeIORef r (v * v + x + 3)

stepPlain :: (Ord a, Num a) => IORef a -> a -> IO ()
stepPlain r x = do
  v <- readIORef r
  if v > x then writeIORef r (v - x)
  else if v > 2 * x then writeIORef r (v * x - 8)
  else if v > 3 * x then writeIORef r (v + x * x)
  else writeIORef r (v * v + x + 4)
```

`stepInlb [InlPrag=INLINABLE] :: forall a. (Ord a, Num a) => IORef a -> a -> IO ()` keeps the pragma with a vanilla unfolding of the cast, ``Unf=Unf{Src=<vanilla>, ... Guidance=ALWAYS_IF(arity=0,unsat_ok=True,boring_ok=True)}] stepInlb = stepInlb1 `cast` ...``, in the interface ``CPR: 1(, 1), Inline:, Unfolding: Core: <vanilla> stepInlb1 `cast` ...``. The cast worker `stepInlb1 [InlPrag=INLINABLE[2]]` is then split, and the INLINABLE source ends on `$wstepInlb [InlPrag=INLINABLE[2]]`, whose interface unfolding is `Inline: [2], Unfolding: Core: StableUser`. Without the pragma the chain is the same with vanilla unfoldings: ``CPR: 1(, 1), Unfolding: Core: <vanilla> stepPlain1 `cast` ...`` and `$wstepPlain [InlPrag=[2]]`.

**Reproduces small:** yes.

### U18. At commit 6913545fd3, CSE merges two identical bindings holding a non-recursive `let` only while no third such binding differs from them, so inlined copies that float out alike stay separate; the tree's patch merges them

**Rule.** CSE finds a binding equal to an earlier one by looking its right-hand side up in a `CoreMap`. At commit 6913545fd3 `xtE` stores `Let (NonRec b r) e` keyed first on the body `e`, then on the right-hand side `r`, while `lkE` looks it up keyed first on `r`, then on `e`; while a trie level holds one entry the lookup compares whole keys and succeeds, and once it holds two, an identical expression is looked up under a path it was never stored under. So two identical top-level bindings holding a non-recursive `let` or join point are merged only while no third such binding differs from them. Its bearing on inlining: the copies an INLINE body leaves at each call site, floated out as identical top-level bindings, are exactly what CSE is meant to merge, and stay apart. The working tree carries the fix proposed in GHC [#27892](https://gitlab.haskell.org/ghc/ghc/-/work_items/27892) as an uncommitted patch to [compiler/GHC/Core/Map/Expr.hs][g1], storing in `lkE`'s order, and on it the reproducer's twins merge. Source: [compiler/GHC/Core/Map/Expr.hs#L376][g573] (`xtE`, the `Let (NonRec b r) e` equation, patched) and [#L346][g574] (`lkE`'s `go (Let (NonRec b r) e)`).

**Seen.** GHC [#27892](https://gitlab.haskell.org/ghc/ghc/-/work_items/27892) (`docs/ghc-issue-cse-let-keys.md`): one test module of orthotope at `-O` kept 80 identical top-level copies per element type of a floated `Data.Vector.Unboxed.concat []`, each holding a non-recursive join point.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/U18-cse-let-keys`, variant `base`, `-O -ddump-cse -dsuppress-all -dsuppress-uniques`): the filed reproducer, unchanged.

```haskell
module Repro where

f, g, h :: Int -> Int -> Int
f x y = case (if x > y then x * 3 else y * 5) of m -> m * m + x * y
h x y = case (if x > y then x * 7 else y * 9) of m -> m * m + x * y
g x y = case (if x > y then x * 3 else y * 5) of m -> m * m + x * y

f2, g2 :: Int -> Int -> Int
f2 x y = x * y + 1
g2 x y = x * y + 1
```

On this tree `Repro.dump-cse` has both `f2 = g2` and `f = g`. The filed issue records the unpatched HEAD keeping `f` and `g` apart, each holding `I# (let { x = *# y 5# } in ...)`, and merging them once `h` is removed.

**Reproduces small:** yes, the filed reproducer; on this tree it shows the fix, the unpatched behaviour resting on the filed issue.

### U19. A join point that receives an already built value hides how it was built from CPR analysis, so a worker returns the nested constructor boxed

**Rule.** CPR analysis gives a lambda-bound binder, a join point's parameter among them, a CPR property only from its demand, anticipating the unboxing worker/wrapper will do ([compiler/GHC/Core/Opt/CprAnal.hs#L250][g464], `cprAnal'` on a lambda, `extendSigEnvForArg`; `argCprType`, [CprAnal.hs#L762][g466], Note [CPR for binders that will be unboxed]); it does not analyse the arguments of the jumps. A parameter that the join point only stores in a constructor field has a demand used boxed, here `SL` (variant `joindmd`, below), not an unboxed product demand, so its CPR is top, and a result built as `A sh arg` in the join point has the CPR `1` without the nested `1` its field would have had if built in place. When `A sh (if c then T .. else T ..)` with `A`'s field strict is simplified, case-of-case puts the continuation `A sh` into a join point and each branch jumps to it with its finished `T` (Core at CPR analysis below), so the function's worker returns `(# sh, T .. #)` with `T` boxed and a caller that takes the result apart pays for the box. Choosing the vector in the branches and building `T` once keeps `T` in the code CPR analysis processes, and the worker returns `T`'s fields unboxed.

**Seen.** A probe of orthotope's `forceT` of 2026-10-13, its `T.dump-cpranal` showing `$j (arg :: T Vector Double) = (A @(*) @Vector @Double sh arg)` and `jump $j (T @(*) @Vector @Double xs1 0# arg)`, and its reading then: "`forceT` calls `fromVectorT` in two branches, so GHC shares `A sh` through a join point that receives a finished `T`. CPR cannot see how a join point's argument was built, so it drops the nested result, and the `T` is returned boxed." The fix is orthotope's commit "Build forceT's result in one place", 32 bytes less a call for boxed Ranked and Dynamic `force` with the result summed.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/U19-join-point-blocks-nested-cpr`, variants `join`, `T` built in each branch by `-DJOIN`, as `forceT` was; `joindmd`, `join` with `-ddump-dmdanal` and, in place of the two suppression flags, `-dsuppress-uniques -dsuppress-module-prefixes -dsuppress-type-applications`, for the join point's demands; `once`, `T` built once on the vector the branches choose, the fix; `run` holds 100000): orthotope's `forceT` reduced to its shape, `A` the shape-carrying wrapper and `T` strides, offset and vector, with a list for the vector.

```haskell
{-# LANGUAGE CPP #-}
module Lib (T (..), A (..), force) where

-- As orthotope's representation: the array T, strides, offset and vector,
-- under the wrapper A holding the shape.
data T = T ![Int] !Int ![Double]
data A = A ![Int] !T

strides :: [Int] -> [Int]
strides = scanr (*) 1 . drop 1

-- As orthotope's forceT: a fresh T with zero offset, on the vector as it is
-- or on a copy.  JOIN builds T in each branch, as forceT calling
-- fromVectorT in two branches did; otherwise the branches choose the vector
-- and T is built once, the fix.
force :: Bool -> A -> A
{-# NOINLINE force #-}
force c (A sh (T _ o v)) =
#if defined(JOIN)
  A sh (if c then T (strides sh) 0 v else T (strides sh) 0 (map (* 2) (drop o v)))
#else
  A sh (T (strides sh) 0 (if c then v else map (* 2) (drop o v)))
#endif
```

```haskell
module Main (main) where
import Lib
import System.Environment (getArgs)

main :: IO ()
main = do
  [n] <- map read <$> getArgs
  let a0 = A [2, 3] (T [3, 1] 0 [1 .. 6])
      sumA (A sh (T st o v)) = sum sh + sum st + o + length v
  print (sum [sumA (force (even i) a0) | i <- [1 .. n :: Int]])
```

`join`, `Lib.dump-cpranal`: `A sh` shared through a join point, each branch jumping to it with a finished `T`:

```
      join { $j arg = A sh arg } in
      case c of {
        False ->
          jump $j
```

```
        True -> jump $j (T (strides sh) 0# v)
```

`joindmd`, `Lib.dump-dmdanal`: the join point's parameter used boxed:

```
        $j (arg [Dmd=SL, OS=OneShot] :: T) = A sh arg } in
```

`Lib.dump-cpr-signatures`, `join` and `once`:

```
force: 1
```

```
force: 1(, 1)
```

`join`, `Lib.dump-simpl`: the worker returns `T` boxed:

```
        True ->
          case scanr $fNumInt_$c* f ($wunsafeDrop 1# ww3) of wild1
          { __DEFAULT ->
          (# ww3, T wild1 0# ww4 #)
          }
```

`once`: `T`'s fields unboxed:

```
            case arg of wild1 { __DEFAULT -> (# ww3, wild, 0#, wild1 #) }
```

Bytes in the heap (the run's `+RTS -s` report, 100000 calls): `join` 51,256,912, `once` 48,056,912. `measure.sh 100000`, a call: `join` 512 bytes and 780 instructions, `once` 480 bytes and 769 instructions, the 32 bytes of `T`'s box, as orthotope's commit measured.

**Reproduces small:** yes.

### U20. A worker that returns a result's fields unboxed makes every caller that keeps the result rebuild its boxes, a box the worker needed itself included

**Rule.** CPR analysis gives a function whose result is a constructor application the CPR property, nested into the constructor's strict fields when they are constructed too ([compiler/GHC/Core/Opt/CprAnal.hs#L90][g575], Note [Nested CPR]), and worker/wrapper then makes a worker that returns those fields unboxed and a wrapper that rebuilds the constructors ([compiler/GHC/Core/Opt/WorkWrap/Utils.hs#L645][g576], `canUnboxResult`). The wrapper is inlined at the callers. A caller that takes the result apart saves the boxes; a caller that keeps the result, by storing it, allocates them, where the function called out of line without a split would have returned the boxes it built. Most of that is a move rather than a cost, the worker no longer building what the wrapper builds; but a box the worker still needs for itself is built twice. A Storable vector's `PlainPtr` is one: the fill loop keeps it alive with `touch#`, so the worker allocates it, returns the `MutableByteArray#` under it unboxed, and the keeping caller allocates a second `PlainPtr`, 16 bytes a call.

**Seen.** Orthotope's benchmark, as recorded on 2026-10-14: "Dynamic `constant` saves 64 to 88 bytes summed, but costs 16 forced at Storable. The cause is GHC's unboxing of the result: `constant`'s worker returns the fields unboxed, and a client that keeps the result re-boxes the vector's `PlainPtr`." The same kind of cost at the pragma commit "Give each binding the pragma its kind calls for" against its parent, "Probe whether a client's call builds a Route, a Range or an Axes", forced, read in the two builds' dumps, the bytes not accounted object by object: at Storable `concatOuter` small and empty, 8 bytes a call in Dynamic and Ranked and 16 in Shaped, the parent's row calls `concatOuter` out of line, and the commit's calls a worker returning the result's fields unboxed and builds `A`, `T`, `Vector` and `PlainPtr` again; Shaped boxed `traverse` small, 8 bytes, the same; at Shaped Storable `update2000` empty, 32 bytes, the parent's worker returns the `T` whole, and the commit's returns its fields, which the row builds into a `T` again.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/U20-unboxed-result-reboxed`, variants `ww`, `constant` NOINLINE, split by worker/wrapper (A24); `opaque`, `constant` OPAQUE, not split, by `-DOPQ`; `run` holds `keep 100000`; `measure.sh N` runs both clients, `keep` storing each result in an `IORef`, `sum` summing its vector): orthotope's Dynamic `constant` reduced to a shape and a Storable vector, the element taken boxed from an `IORef` so that neither variant boxes it.

```haskell
{-# LANGUAGE CPP #-}
module Lib (D (..), constant) where

import qualified Data.Vector.Storable as VS

-- As orthotope's Dynamic array over a Storable vector: shape and vector.
data D = D ![Int] !(VS.Vector Double)

-- As Dynamic constant: a vector of the shape's size, every element x.
constant :: [Int] -> Double -> D
#if defined(OPQ)
{-# OPAQUE constant #-}
#else
{-# NOINLINE constant #-}
#endif
constant sh x = D sh (VS.replicate (product sh) x)
```

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where
import Data.IORef
import qualified Data.Vector.Storable as VS
import Lib
import System.Environment (getArgs)

main :: IO ()
main = do
  [mode, n] <- getArgs
  ref <- newIORef (constant [1] 0)
  -- The element, read boxed from an IORef, so no variant boxes it.
  xref <- newIORef (1.5 :: Double)
  let go :: Int -> Double -> IO Double
      go !i !acc
        | i > read n = return acc
        | mode == "keep" = do
            -- The client keeps the result: it is stored, to be read back.
            x <- readIORef xref
            writeIORef ref $! constant [2, 3] x
            go (i + 1) acc
        | otherwise = do
            -- The client takes the result apart and sums its vector.
            x <- readIORef xref
            case constant [2, 3] x of
              D _ v -> go (i + 1) (acc + VS.sum v)
  s <- go 1 0
  D _ v <- readIORef ref
  print (s + VS.sum v)
```

`Lib.dump-cpr-signatures`: `ww` nested down to the `PlainPtr`, the fourth constructor of `ForeignPtrContents` ([libraries/ghc-internal/src/GHC/Internal/ForeignPtr.hs#L165][g577]); `opaque` with none:

```
constant: 1(, 1(, , 4))
```

`ww`, `Lib.dump-simpl`: the worker allocates its own `PlainPtr`, which the fill loop's `touch#` keeps alive, and returns the array under it unboxed; the wrapper rebuilds all three boxes:

```
                                       let { ipv2 = PlainPtr ipv1 } in
```

```
                                                             case touch# ipv2 ds8 of s'
```

```
                                                     case sh of wild { __DEFAULT ->
                                                     (# wild, ww1, ipv5, ipv1 #)
                                                     }
```

```
constant
  = \ sh x ->
      case x of { D# ww ->
      case $wconstant sh ww of { (# ww1, ww2, ww3, ww4 #) ->
      D ww1 (Vector ww2 ww3 (PlainPtr ww4))
      }
      }
```

`ww`, `Main.dump-simpl`, the keeping client: the inlined wrapper's boxes stored:

```
                                        case writeMutVar#
                                               ipv3 (D wild10 (Vector ww5 ww6 (PlainPtr ww7))) ipv7
```

Bytes in the heap (the run's `+RTS -s` report, `keep 100000`): `ww` 15,302,256, `opaque` 13,702,256. `measure.sh 100000`, a call: `keep`, `ww` 152 bytes and 374 instructions, `opaque` 136 bytes and 362 instructions; `sum`, `ww` 112 bytes and 409 instructions, `opaque` 152 bytes and 412 instructions. The keeping client pays the second `PlainPtr`'s 16 bytes; the summing one saves the `D` and `Vector` boxes less that `PlainPtr`, which `VS.sum`'s own `touch#` makes it rebuild too.

**Reproduces small:** yes, the 16 bytes of the record's forced client; the record's 64 to 88 bytes saved summed are those of naming `constant`'s arguments ("Name the arguments of the generic arrays' functions" against "Name the arguments of the vector instances' methods"), the repro's summing client saving 40.

### U21. Worker/wrapper unboxes a given equality but not the argument whose type it fixes, so a worker over `a ~# Int` takes and returns `a` boxed

**Rule.** Worker/wrapper unboxes a strict argument only if `normSplitTyConApp_maybe` splits its type into a data type with one constructor (`canUnboxArg`, [compiler/GHC/Core/Opt/WorkWrap/Utils.hs#L624][g203], Note [Which types are unboxed?] at [#L761][g578]), and a constructed result likewise (`canUnboxResult`, [#L645][g576]). `normSplitTyConApp_maybe` ([compiler/GHC/Core/Utils.hs#L3146][g579]) normalises type families and newtypes, but uses no given equality: for a type variable it returns `Nothing`, whatever coercion is in scope. So for `f :: forall a. (a ~ Int) => a -> a` the equality's box is unboxed, the wrapper taking it apart by `case $d~ of { Eq# ww -> ...`, and the worker takes the coercion `a ~# Int` as a parameter, while the argument and the result, of type `a`, stay boxed. In the worker the argument appears only as `` eta `cast` co ``, a trivial argument of unknown form, so `Int`'s `+`, whose unfolding needs a benefit, finds none in a boring context and stays a call of `$fNumInt_$c+` (A01, A03). The same body at `Int -> Int` gets an `Int#` worker in which `+` is inlined, the argument being known as `I# ww`. Specialisation does not take the equality's coercion apart either (O06).

**Seen.** `docs/ghc-issue-equality-cast-dictionary-14941-comment.md`, the body's third paragraph, a comment posted on GHC [#14941](https://gitlab.haskell.org/ghc/ghc/-/work_items/14941) on 2026-10-10 for GHC [#27920](https://gitlab.haskell.org/ghc/ghc/-/work_items/27920) (the specialisation half, O06): "On 9.8.4, 9.10.3, 9.12.4, 9.14.1 and HEAD, `f :: forall a. (a ~ Int) => a -> a` with `NOINLINE` gets a worker of type `forall a. (a ~# Int) => a -> a`. But the worker still takes `a` boxed, and it adds with `$fNumInt_$c+`." The example is the GHC [#14941](https://gitlab.haskell.org/ghc/ghc/-/work_items/14941) comment of 2018-09-14. A29's out-of-line dispatcher boxes its accumulator plausibly for the same reason, the accumulator's type there being a type variable known equal to `Double` only through a coercion; that case was not taken apart.

**Repro** (`~/r/horde-ad/dist-inlcat/cases/U21-equality-worker-boxed`, variants `base` and `check`; `run` is `f 100000`; `measure.sh N`): the ticket's `f`, `NOINLINE`, beside its twin `g` at `Int`, and a loop calling either.

```haskell
{-# LANGUAGE ScopedTypeVariables, TypeFamilies #-}
-- GHC #14941's example of 2018-09-14, f, beside its twin at Int, g.
module Lib (f, g) where

-- The type through an equality given.
{-# NOINLINE f #-}
f :: forall a. (a ~ Int) => a -> a
f x = x + x

-- Its twin at Int.
{-# NOINLINE g #-}
g :: Int -> Int
g x = x + x
```

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import Lib
import System.Environment (getArgs)

main :: IO ()
main = do
  [what, repss] <- getArgs
  let reps = read repss :: Int
      loop :: (Int -> Int) -> Int -> Int -> Int
      loop h = go
        where go 0 !acc = acc
              go r !acc = go (r - 1) (acc + h r)
  print $ if what == "f" then loop f reps 0 else loop g reps 0
```

`Lib.dump-simpl`: `` $wf = \ @a ww eta -> ($fNumInt_$c+ (eta `cast` <Co:2>) (eta `cast` <Co:2>)) `cast` <Co:3> `` (whitespace collapsed), with the wrapper `f = \ @a $d~ eta -> case $d~ of { Eq# ww -> $wf @~<Co:1> eta }`, against `$wg = \ ww -> *# 2# ww`; `Lib.iface`: `$wf :: (a GHC.Internal.Prim.~# GHC.Internal.Types.Int) => a -> a` and `$wg :: GHC.Internal.Prim.Int# -> GHC.Internal.Prim.Int#`. Variant `check` (`-dinline-check $fNumInt_$c+`), in `build.log`: `Considering inlining: $fNumInt_$c+ arg infos [TrivArg, TrivArg] interesting continuation BoringCtxt some_benefit False is exp: True is work-free: True guidance ALWAYS_IF(arity=2,unsat_ok=True,boring_ok=False) case depth = 0 inline depth = 2 ANSWER = NO` (whitespace collapsed). `Main`'s loop over `f` keeps its counter boxed to pass it: `case $wf @~<Co:1> wild of { I# y -> $wgo (I# (-# wild1 1#)) (+# ww y)`.

By `measure.sh 1000000` (1000000 and 2000000 calls differenced, twice, the same figures): `f` 49.7 instructions and 32.0 bytes a call, `g` 16.0 and 0.0. The Core accounts for the bytes as the `I#` of `Main`'s counter and the `I#` returned by `$fNumInt_$c+`.

**Reproduces small:** yes.

## 5. Rules read but given no entry

Read in the source and given no entry; where a case shows the rule, its paragraph names the case.

### R01. Rule left-hand sides and GHCi expressions get no inlining

No inlining happens on a rule's left-hand side, which `simplRules` simplifies with inlining and rules off, its right-hand side with inlining on in the rule's activation ([compiler/GHC/Core/Opt/Simplify/Iteration.hs#L5073][g580]; `updModeForRuleLHS` and `updModeForRuleRHS`, [compiler/GHC/Core/Opt/Simplify/Utils.hs#L1220][g581] and [#L1232][g582]), nor in an expression GHCi evaluates ([compiler/GHC/Driver/Config/Core/Opt/Simplify.hs#L31][g583]), which this harness does not run. In `~/r/horde-ad/dist-inlcat/cases/R01-rule-lhs-no-inlining` the INLINE `g` stays on the left of a rule for the NOINLINE `f` and is inlined on its right, `"f/g" forall x. f (g x) = case x of { I# x1 -> I# (+# 3# (*# 3# x1)) }` (`M.dump-simpl`, whitespace collapsed).

### R02. No flag bypasses `tryUnfolding`'s tests: `unfoldingVeryAggressive`, which they check, is set by nothing on HEAD

No flag bypasses `tryUnfolding`'s tests: it tests `unfoldingVeryAggressive` ([compiler/GHC/Core/Opt/Simplify/Inline.hs#L311][g6] and [#L322][g584]), which takes an `UnfWhen` unfolding with enough arguments and any `UnfIfGoodArgs` one, but nothing sets it on HEAD, `updateVeryAggressive` ([compiler/GHC/Core/Unfold.hs#L142][g585]) having no caller and no flag reaching it.

### R03. Inlining decisions do not depend on `-funfolding-keeness-factor`, though it is accepted

Inlining decisions do not depend on `-funfolding-keeness-factor`, which is accepted and ignored, "no longer respected as of GHC 9.0" ([compiler/GHC/Driver/Session.hs#L1885][g586]). In `~/r/horde-ad/dist-inlcat/cases/R03-keeness-factor-ignored`, A04's module built with `-fno-worker-wrapper` and `-dinline-check inlSz`, at `-funfolding-keeness-factor=0` and `=100` and without the flag, makes the same decisions about `inlSz` and the same Core, by its `post` script, which compares each variant's decisions, condensed to argument infos, context, adjusted size and answer, and its `M.dump-simpl` with those of the build without the flag, and the build at 100 warns `-funfolding-keeness-factor=100 is deprecated: -funfolding-keeness-factor is no longer respected as of GHC 9.0`.

### R04. The `inline depth` that `-dinline-check` prints decides no inlining

The `inline depth` that `-dinline-check` prints decides nothing about inlining: `callSiteInline` uses `seInlineDepth` only to print it ([compiler/GHC/Core/Opt/Simplify/Inline.hs#L361][g587], [#L379][g588]), and otherwise it only stops `optCoercion` on coercions met while re-simplifying an inlined body ([compiler/GHC/Core/Opt/Simplify/Env.hs#L169][g589]). In `~/r/horde-ad/dist-inlcat/cases/R04-inline-depth-decides-nothing`, built with `-fno-worker-wrapper`, A04's `inlSz` with its default branch `y + 7`, called in a `case` directly and through a pragma-free `v` is decided at inline depth 1 and 2 with the same size and answer, `case depth = 0 inline depth = 2 depth based penalty = 0 adjusted size = 84 ANSWER = YES` and the same at `inline depth = 1` (`build.log`).

### R05. CorePrep's eta-expansion of arguments comes after all inlining

CorePrep's eta-expansion of arguments runs after all inlining and so decides none: CorePrep runs during code generation on the tidied program (`corePrepPgm`, [compiler/GHC/Driver/Main/Compile.hs#L790][g590]), let-binding a non-trivial argument and eta-expanding it (`cpeArg`, [compiler/GHC/CoreToStg/Prep.hs#L1543][g591]). In `~/r/horde-ad/dist-inlcat/cases/R05-coreprep-arg-eta`, `k = \ b c -> f c (case b of { False -> g2; True -> g1 })` in `M.dump-simpl` is `k = \ b c -> let { k_sat = \ eta -> case b of { False -> g2 eta; True -> g1 eta } } in f c k_sat` in `M.dump-prep` (whitespace collapsed).

### R06. Recursive bindings' arities and trimmed arities change no inlining beyond E08's

The arity fixpoint for recursive bindings, the trimming of an arity to the type's, and the arity of recursive join points change no inlining beyond E08's ([compiler/GHC/Core/Opt/Arity.hs][g325]).

### R07. Ordinary source gives every INLINE unfolding a saturation count; `mkInlineUnfoldingNoArity` serves only a fallback

Ordinary source gives every INLINE unfolding a saturation count: `mkInlineUnfoldingNoArity` is reached only from a fallback in `makeCorePair` ([compiler/GHC/HsToCore/Binds.hs#L472][g592]), and foreign-import stubs call `mkInlineUnfoldingWithArity` ([compiler/GHC/HsToCore/Foreign/C.hs#L323][g593]).

### R08. After specialisation, a local dictionary binder's unfolding is remade from its specialised right-hand side

After specialisation, a local dictionary binder's unfolding is remade from its specialised right-hand side, the only case Note [Update unfolding after specialisation] ([compiler/GHC/Core/Opt/Specialise.hs#L3281][g594]) concerns.

## 6. Inlining, not specialisation: GHC's text against its code, and behaviour that may be unintended

Each item is filed as a GHC issue or an item of one, or posted as a comment, and names where; the filed or posted text is the source of what an item says of releases.

1. Note [Eta-expanding at let bindings] ([compiler/GHC/Core/Opt/Simplify/Utils.hs#L2204][g595]) says the INLINE alias `myMap = genMap` keeps an unexpanded template so that `genMap` is not inlined; HEAD expands it and inlines `genMap` (E06). Note [Eta-expand stable unfoldings] ([compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4964][g272]), which adopts the expansion, cites a `Historical-note [Eta-expansion in stable unfoldings]` in `GHC.Core.Opt.Simplify.Utils` ([Iteration.hs#L4986][g596], also [compiler/GHC/Core/Opt/OccurAnal.hs#L2230][g597]) that exists nowhere under `compiler/`. Filed as items 5 and 6 of GHC [#27973](https://gitlab.haskell.org/ghc/ghc/-/work_items/27973), `docs/ghc-issue-doc-slips.md` in horde-ad.
2. Note [inl_inline and inl_act] ([compiler/Language/Haskell/Syntax/Binds/InlinePragma.hs#L121][g598]) says `NOINLINE[1]` sets `ActiveBefore 1`; the parser sets `ActiveAfter 1`, and the repro behaves accordingly (A10). Filed as item 3 of GHC [#27973](https://gitlab.haskell.org/ghc/ghc/-/work_items/27973), `docs/ghc-issue-doc-slips.md` in horde-ad.
3. Note [Inlining in gentle mode] ([compiler/GHC/Core/Opt/Simplify/Utils.hs#L1334][g599]) says only things with an INLINE pragma are inlined in the gentle run; a function without a pragma is inlined there too (A10), and so is an INLINABLE one whose interface unfolding is the always-inline `StableSystem` form of U07, as orthotope's `toVector` at R4 (O13). Filed as item 4 of GHC [#27973](https://gitlab.haskell.org/ghc/ghc/-/work_items/27973), `docs/ghc-issue-doc-slips.md` in horde-ad.
4. CSE zaps a user INLINE or INLINABLE unfolding when it replaces the binding's right-hand side by an earlier binder ([compiler/GHC/Core/Opt/CSE.hs#L455][g600]), where Note [CSE for stable unfoldings] ([CSE.hs#L233][g514]) says the user's unfolding should be kept ("we promised to inline foo as what the user wrote") and justifies the zap only for an unfolding "added by strictness analysis, say"; an importer then loses fusion (U02). Filed as GHC [#27974](https://gitlab.haskell.org/ghc/ghc/-/work_items/27974), `docs/ghc-issue-cse-drops-inline-unfolding.md` in horde-ad.
5. A stable unfolding's boxed use of an argument keeps the worker from unboxing it (U16), where 9.14.1 and 9.12.4 unbox it: Note [Combining demands for stable unfoldings] (GHC [#26416](https://gitlab.haskell.org/ghc/ghc/-/work_items/26416)) argues the combination for strictness and usage only, and boxity is combined inside `maxSubDmd` by `lubBoxity = boxedWins`; the cause is suspected, not bisected, to be 870243e4, the merge of GHC [!15238](https://gitlab.haskell.org/ghc/ghc/-/merge_requests/15238). Filed as GHC [#27976](https://gitlab.haskell.org/ghc/ghc/-/work_items/27976), `docs/ghc-issue-unfolding-boxity-worker.md` in horde-ad.
6. A default method that recurses through a dictionary its method takes is in no recursive group (`occAnalRecBind`, [compiler/GHC/Core/Opt/OccurAnal.hs#L1239][g205]), so it is no loop breaker, and an importer calling it at known dictionaries inlines an INLINE default without end, until the simplifier's ticks are exhausted (A30). An instance of GHC [#5722](https://gitlab.haskell.org/ghc/ghc/-/work_items/5722) and its declared duplicate GHC [#9235](https://gitlab.haskell.org/ghc/ghc/-/work_items/9235), new in that the dictionary reaches the class through another class's superclass. Posted as a comment on GHC [#9235](https://gitlab.haskell.org/ghc/ghc/-/work_items/9235), `docs/ghc-issue-superclass-method-loop-9235-comment.md` in horde-ad.
7. `interestingCallContext` returns `ValAppCtxt` only behind a `TickIt` continuation, and the two places that would build one for a tick are commented out in `simplTick` ([compiler/GHC/Core/Opt/Simplify/Iteration.hs#L1469][g50] and [#L1546][g51]), so that branch is unreachable on this tree (A08). An instance of GHC [#27141](https://gitlab.haskell.org/ghc/ghc/-/work_items/27141), whose description says that no code path creates a `TickIt` continuation. Posted as a comment on GHC [#27141](https://gitlab.haskell.org/ghc/ghc/-/work_items/27141), `docs/ghc-issue-valappctxt-dead-27141-comment.md` in horde-ad.
8. A one-use dictionary of a single-method class stays out of line in orthotope's build, its worker `$w$dSummed` called on a `Right` built just before the call, where a small model inlines that one call unconditionally once CSE leaves it (O26): the call also occurs in a stable unfolding, and an occurrence there counts as many, by design, as simonpj ruled on GHC [#26571](https://gitlab.haskell.org/ghc/ghc/-/work_items/26571). Posted as a comment on GHC [#26571](https://gitlab.haskell.org/ghc/ghc/-/work_items/26571), `docs/ghc-issue-stable-unfolding-keeps-call-26571-comment.md` in horde-ad, giving this program for simonpj's question on GHC [#26570](https://gitlab.haskell.org/ghc/ghc/-/work_items/26570), "would there be any benefit in a real program?".
9. `isExitJoinId` classifies any join point with one occurrence inside a lambda as an exit join point (Note [Do not inline exit join points]), and since 9.10 the occurrence analyser, which replays the occurrences in a join point's right-hand side at each jump to it (`occ_join_points`, from GHC [!9614](https://gitlab.haskell.org/ghc/ghc/-/merge_requests/9614) for GHC [#22404](https://gitlab.haskell.org/ghc/ghc/-/work_items/22404)), marks one jumped to only from join points that a loop jumps to as occurring inside a lambda; so that join point, without a stable unfolding, gets none and its jumps are never inlined, though inlining them would put nothing back into the loop. A summing join point of a worker/wrapper wrapper's shape then stays at the jumps, each fill building a Storable vector's box to jump to it (E14, reproduced in part in a small model; the filed reproducer shows it on 9.10.3 and later, and 9.8.4 inlines its join point). Filed as GHC [#27982](https://gitlab.haskell.org/ghc/ghc/-/work_items/27982), `docs/ghc-issue-join-point-replay-inside-lambda.md` in horde-ad. A comment with a base-only reproducer of the wider form, which the issue says it lacks, its unused box 16 bytes a call on 9.10.3 to HEAD and absent on 9.6.7 and 9.8.4 (O28), is posted, `docs/ghc-issue-replay-wider-form-27982-comment.md` in horde-ad.
10. An always-active INLINE unfolding takes no rule active only until a phase (U10), so the INLINE unfolding of a list producer keeps `foldr` over `eftInt`, `"eftInt" [~1]` never firing in it, and where the producer is inlined only in phase 0, its argument a variable until then, the caller builds the list, where without the pragma it is fused; 9.14.1's unfolding is fused, 9.14.1 and 9.12.4 giving both forms the same cost, and the cause is inferred, not bisected, to be 2da84b7a83 ("Only use active rules when simplifying rule RHSs", for GHC [#26323](https://gitlab.haskell.org/ghc/ghc/-/work_items/26323)). Orthotope's recorded gain from INLINE `update` at Storable, Unboxed and Shaped came of this, in the probe that measured it (U08). Filed as GHC [#27977](https://gitlab.haskell.org/ghc/ghc/-/work_items/27977), `docs/ghc-issue-inline-unfolding-unfused.md` in horde-ad.
11. The users' guide entry for `-funfolding-use-threshold` gives two defaults, `*default: 90.*` in its `:shortdesc:` and `:default: 80` in its body ([docs/users_guide/using-optimisation.rst#L1815][g601]), where the threshold is 90 (`unfoldingUseThreshold`, [compiler/GHC/Core/Unfold.hs#L103][g379]); GHC [#24653](https://gitlab.haskell.org/ghc/ghc/-/work_items/24653) fixed the `:shortdesc:` alone. Filed as item 1 of GHC [#27973](https://gitlab.haskell.org/ghc/ghc/-/work_items/27973), `docs/ghc-issue-doc-slips.md` in horde-ad.
12. Note [Simplifying inside stable unfoldings] ([compiler/GHC/Core/Opt/Simplify/Utils.hs#L1449][g134]) names `OccurAnal.addRuleUsage`, `inline_me` and an `ArgOf` continuation, none of which the code under `compiler/` defines, and its section "A note about wrappers" says that the `inline_me` keeps a worker from being inlined back into its wrapper, where orthotope's build, by its dumps, inlines the worker back (O26). Filed as item 8 of GHC [#27973](https://gitlab.haskell.org/ghc/ghc/-/work_items/27973), `docs/ghc-issue-doc-slips.md` in horde-ad.
13. A worker that worker/wrapper splits off an INLINABLE function carries the function's INLINABLE unfolding, so that importers can still specialise it (U08; Note [Worker/wrapper for INLINABLE functions], [compiler/GHC/Core/Opt/WorkWrap.hs#L186][g536]); where that source-form unfolding shrinks enough, the simplifier inlines the worker back into its wrapper, and at `-O` no later worker/wrapper splits the loop it rebuilds, so orthotope's `Data.Array.Internal.Dynamic.scalar1` loops by a boxed counter, an `I#` a call, where its worker's loop took an `Int#` (O25, reproduced small; `-flate-dmd-anal` splits the rebuilt loop again). The section "A note about wrappers" of the Note that item 12 cites says that this inlining is prevented; no text states the cost. Filed as GHC [#27984](https://gitlab.haskell.org/ghc/ghc/-/work_items/27984), `docs/ghc-issue-inlinable-worker-inlined-back.md` in horde-ad, whose reproducer, needing only base, shows it on HEAD, 9.6.7, 9.8.4, 9.10.3, 9.12.4 and 9.14.1 (allocating 640 MB against 58 KB for the same function without the pragma).

## Appendix. How inlining meets specialisation

Prose only: each paragraph states a rule of GHC HEAD's specialiser as it touches unfoldings and inlining, read in the working tree (with its uncommitted patches, named where they bear), and the observation of ours that met it, where one did. The entries cited carry repros.

**Which imported functions are specialised.** An importing module specialises an imported overloaded function at a call with known dictionaries only if the function has an unfolding in the interface and carries a user INLINE or INLINABLE pragma; data-constructor wrappers never, DFuns and functions without a pragma only under `-fspecialise-aggressively` in the importing module, under which any unfolding qualifies, vanilla, DFun or a loop breaker's. So exposing unfoldings (`-fexpose-overloaded-unfoldings`, `-fexpose-all-unfoldings`, U05) makes a function without a pragma specialisable only at importers built `-fspecialise-aggressively`, and makes a function with a pragma but no stable unfolding (a partial specialisation of an INLINABLE function, below) specialisable at every importer. Worker/wrapper copies a user INLINABLE pragma onto the worker together with the stable unfolding (U08) so that the worker passes this test; a worker of a function without a pragma has neither, and no importer can specialise it without `-fspecialise-aggressively` and an exposed unfolding. Source: [compiler/GHC/Core/Opt/Specialise.hs#L911][g330] (`canSpecImport`: `CoreUnfolding` and `isAnyInlinePragma`, else `gopt Opt_SpecialiseAggressively` and `maybeUnfoldingTemplate`, from `realIdUnfolding` "even for loop breakers"), [Specialise.hs#L703][g602] (Note [Specialising imported functions], points (1) and (2)), [Specialise.hs#L995][g603] (Note [Do not specialise imported DFuns]). Met: `docs/perf-checklist.md` P's two halves, which turn on exactly this; S1's `DynamicS.toVector`, without a pragma, "split into a wrapper and a worker with no unfolding, which no client could specialise" (O30), and `index`, `scalar` and `unScalar` called with `$fUnboxDouble` at run time; and the class's default `<` that orthotope's `Ord` instances took with `compare` alone defined, which no client specialises (their `INLINE throughout:` comments at "Take the vector strict in the boxed and Unboxed vToList").

**Cross-module specialisation can be switched off.** `-fcross-module-specialise`, on at `-O` and `-O2`, gates the specialisation of imported functions as a whole; with `-fno-cross-module-specialise` only the module's own functions are specialised. Source: [Specialise.hs#L761][g604] (`specImports`: `not $ gopt Opt_CrossModuleSpecialise ...` returns no rules), [Specialise.hs#L685][g605] (Note [Disabling cross-module specialisation], GHC [#10491](https://gitlab.haskell.org/ghc/ghc/-/work_items/10491)), [compiler/GHC/Driver/DynFlags.hs#L1339][g606]. Met: not in our record.

**Polymorphic specialisation is on by default.** With `-fpolymorphic-specialisation` a call whose dictionary mentions type variables bound outside it, such as `wimwam @(ST s) (dMST @s)`, keeps floating as a call and is specialised with those variables quantified in the copy and its rule; without it, such a call is dropped at the binder of the variable and the callee runs overloaded. HEAD turns the flag on at `-O` and `-O2` (GHC [#23559](https://gitlab.haskell.org/ghc/ghc/-/work_items/23559)). It also makes partial specialisations, keyed on some arguments and abstract in others, which interact with the unfolding rules below. Source: [compiler/GHC/Driver/DynFlags.hs#L1338][g607] (`([1,2], Opt_PolymorphicSpecialisation) -- Now on by default (#23559)`), [Specialise.hs#L2775][g608] (Note [Specialising polymorphic dictionaries], (MP1) to (MP3)), [Specialise.hs#L3003][g609] (`singleCall`: with the flag, a call's free variables are its local Ids only, not its type variables). Met: S1, "`-fpolymorphic-specialisation` is on by default only on HEAD, and orthotope's boxed modules ran up to 8 times slower on 9.12.4 without it", and orthotope's commits turning it on in the boxed modules and off in the Storable and Unboxed ones; the comment on GHC [#23050](https://gitlab.haskell.org/ghc/ghc/-/work_items/23050) (`docs/ghc-issue-partial-specialisation-no-unfolding-comment.md`), "With `-fpolymorphic-specialisation` now on by default, this is triggered more often"; GHC [#27880](https://gitlab.haskell.org/ghc/ghc/-/work_items/27880), where the flag's auto rule is what kept a recursive specialisation clear of the recursion guard.

**What a call is specialised on.** A call's key consists of those of its type arguments that its constraints mention and those dictionary arguments for which `interestingDict` returns `True`, a dictionary constructor application seen through casts and unfoldings; trailing unspecialised arguments are dropped, and every other argument is a parameter of the copy (`UnspecType`, `UnspecArg`): value arguments (O08), and equality evidence, so that a dictionary cast by it cannot float to the callee's specialisation (O06). Every type the constraints mention is part of the key, a type-level `KnownNat` included, while a constraint the specialiser cannot resolve to a dictionary constructor, such as an associated type family's, stays abstract. Source: [Specialise.hs#L2462][g610] (`data SpecArg`, `UnspecArg` for "Value arguments that should not be specialised" at [#L2477][g611]), [Specialise.hs#L3026][g506] (`mkCallUDs'`: `ci_key`, `SpecDict` only if `interestingDict env arg`, else `UnspecArg` by `mk_spec_arg`, [#L3059][g393]), [Specialise.hs#L3086][g390] (`interestingDict`) and [Specialise.hs#L3164][g612] (Note [Interesting dictionary arguments]). Met: GHC [#27920](https://gitlab.haskell.org/ghc/ghc/-/work_items/27920) and orthotope's `Convert`, O06's; S2's Ranked `rotate`, INLINE over ranks, 48 copies in one test module, INLINABLE one per rank pair; S1's rules keyed on the vector type alone with the element's `VecElem` constraint `irred`, sending clients to element-polymorphic copies, Storable `pad` 43 times as slow per element (O30); and a pattern-bound `Num Int` dictionary, which the simplifier does not replace by `$fNumInt`, short-cut solving being the typechecker's alone (GHC [#26816](https://gitlab.haskell.org/ghc/ghc/-/work_items/26816), as `docs/ghc-issue-floatin-duplicate-values-appendix-d-session-notes.md` records it).

**A specialised copy's unfolding.** A copy keeps an INLINE unfolding and drops an INLINABLE one, and a SPECIALISE pragma's copy of an INLINE function in its own module gets none (U12). A copy dropping an INLINABLE unfolding keeps its INLINABLE pragma and gets only a vanilla unfolding of its optimised right-hand side, which the defining module exposes only if U05's tests allow; so a partial specialisation cannot be specialised further by an importer unless its vanilla unfolding is exposed, which the exposure flags do. Source: U12's. Met: GHC [#23050](https://gitlab.haskell.org/ghc/ghc/-/work_items/23050)'s comment, the partial specialisation `SPEC astTimesK @_ @(PrimalStepSpan FullSpan)` in horde-ad's `AstSimplify` (built `-fno-expose-overloaded-unfoldings`) costing 2 to 3% of allocation, its workaround the exposure flags; S2, "A specialised worker with no unfolding cannot be specialised further"; and O10's INLINE body under INLINABLE callers too big to inline, copied once per caller and type into their specialisations.

**SPECIALISE pragmas and their rules.** A SPECIALISE pragma makes, in the desugarer, a copy and a rule `USPEC f @T = f_$sf`; the rule's activation is the pragma's own phase if it gives one, else the function's inline activation, and the copy's inline pragma is the pragma's `SPECIALISE INLINE` if given, else the function's, NOINLINE for an imported function that is a strong loop breaker. Source: [compiler/GHC/HsToCore/Binds.hs#L999][g613] (`dsSpec_help`), [Binds.hs#L1218][g565] (`specFunInlinePrag`), [Binds.hs#L1247][g614] (Note [Activation pragmas for SPECIALISE]). Met: GHC [#27921](https://gitlab.haskell.org/ghc/ghc/-/work_items/27921) (`docs/ghc-issue-specialise-hidden-by-worker.md`), below.

**SPECIALISE instance.** A `SPECIALISE instance` pragma makes, in the defining module, a specialised dictionary function and a specialised copy of each method from its right-hand side, each with a rule from the overloaded one, so that a call at the instance's type reaches the copies whichever of the class-op and specialisation rules fires first; a method marked INLINE inherits no specialisation from the instance, being inlined instead. A client's call is rewritten by the exported rules and needs no unfolding of its own to specialise, where an importer's own specialisation of a dictionary function needs `-fspecialise-aggressively` (the first paragraph above). Source: [compiler/GHC/Tc/TyCl/Instance.hs#L2603][g615] (Note [SPECIALISE instance pragmas]), [#L2239][g616] (`mk_meth_spec_prags`). Met: horde-ad's `SPECIALIZE instance` in `Adaptor`, kept because without it rank-2 VTC compilation took 1.8 to 2.3 times the allocation (`docs/pragmas-and-flags.md`, "What stays, and why"); no small repro was made.

**Auto-specialisation rules follow the function's activation, and NOINLINE functions get none.** A rule the specialiser makes for `f` is active when `f`'s inlining is, so that a rule mentioning `f` can fire before `f` is rewritten to a copy; consequently a NOINLINE or OPAQUE function, never active, is not specialised at all, and an INLINABLE [n] function's auto rule is inactive until phase n. Source: [Specialise.hs#L2336][g617] (Note [Specialise: rule activation], (SRA1)). Met: GHC [#27880](https://gitlab.haskell.org/ghc/ghc/-/work_items/27880) (`docs/ghc-issue-specimport-recursion-guard.md`): with `INLINABLE [1]` on a recursive function, its auto rule was inactive when an importer's specialiser ran, which exposed the recursion guard below; orthotope's phase-free INLINABLE pragmas, P's "a phase control, `INLINE [n]` ... stays for that order"; and the phase gap of GHC [#26827](https://gitlab.haskell.org/ghc/ghc/-/work_items/26827) on horde-ad's recursive interpreter, every pragma without a phase equally fast and every phased one equally slow, in tasty totals, which are anecdotal (`docs/ghc-issue-floatin-duplicate-values-appendix-d-session-notes.md`, its section 3).

**Rules against inlining and wrappers.** A specialisation rule wins over an INLINE unfolding active at the same time (A12; in U12 that loses fusion), and a wrapper is not inlined before phase 2 and the function's rules (A26), so that a specialisation rule, in the module or an importer, meets the wrapper's call before it becomes a call of the worker. The delay protects importers only for calls that reach them: a stable unfolding active from phase 2, as the INLINABLE unfolding a worker carries is, has the callee's wrapper inlined into it in the defining module from phase 2 on (U10), and then the importer's specialised copy calls the callee's worker, unspecialised. Source: A12's and A26's. Met: GHC [#27921](https://gitlab.haskell.org/ghc/ghc/-/work_items/27921), the SPECIALISE rule for `helper` unused because `f`'s bangs gave it a worker whose INLINABLE unfolding called `$whelper`, "Item 4 of Note [Wrapper activation] wants to prevent exactly this". And horde-ad's `simplifyUserCode` (`docs/pragmas-and-flags.md`, "What stays, and why", the `grad` row), the same route with a vanilla unfolding in place of a stable one. Without its INLINE the interface carries its optimised right-hand side (U01), in which `AstEngine` has inlined `simplifyAst`'s wrapper. So `OpsAst`'s FullSpan copy `$w$s$wsimplifyUserCode` calls `AstTraverse.$wsimplifyAst` and `AstInline.$winlineAst` at `C:KnownSpan @FullSpan $WSFullSpan`, which `"SPEC simplifyAst @FullSpan @_"`, keyed on the wrapper, does not match, and which the importer cannot specialise either, `$wsimplifyAst` having no unfolding (`OtherCon []`): it is an overloaded loop breaker in a module built `-fno-expose-overloaded-unfoldings` (U05). Every `grad` row of shortProdForCI then allocates 0.1 to 4.1% more, `1000/grad k L` the most. With AstTraverse's and AstInline's `-fno-expose-overloaded-unfoldings` lines removed as well, `OpsAst` specialises the workers itself, by rules such as `"SPEC/HordeAd.Core.OpsAst $wsimplifyAst @FullSpan @_"`, and every `grad` row allocates within 0.22% of the baseline, and removing those lines alone moves allocation by no more than 0.03%. `simplifyInlineContract` escapes this, `AstEngine` specialising it at FullSpan itself for `simplifyArtifactRev`; removing its INLINE and `forwardPassByInterpretation`'s as well moves allocation by no more than 0.021%.

**Already covered.** The specialiser makes no copy for a call that an existing rule already covers, except that a call more specific than an existing auto rule gets a copy and rule of its own (SC2), so that the order of calls does not decide the copies. The checked-in `alreadyCovered` tests the instance relation the wrong way round; this tree carries the fix of GHC [#27873](https://gitlab.haskell.org/ghc/ghc/-/work_items/27873) as an uncommitted patch to [Specialise.hs][g3] (`rule_is_instance`, which matches the call's pattern, as the template, against the rule's left-hand side, so that only a rule at least as specific as the call covers it). Source: [Specialise.hs#L1794][g618] (`alreadyCovered`), [Specialise.hs#L2314][g619] (Note [Specialisations already covered]). Met: GHC [#27873](https://gitlab.haskell.org/ghc/ghc/-/work_items/27873) (`docs/ghc-issue-already-covered-direction.md`), one call at a partly known type in a library sending clients to a less specialised copy, a horde-ad test 1.33x slower; S2's three library copies of `rotate` where eight were needed; and a partial user `SPECIALISE interpretAst @Concrete` in horde-ad's `AstInterpret`, which stopped importers making the full known-span specialisations they had made ("user rules dominate" in `alreadyCovered`, `docs/ghc-issue-floatin-duplicate-values-appendix-d-session-notes.md`).

**The recursion guard of imported specialisation.** Specialising an imported function's unfolding can meet calls of the same function, and to avoid an endless chain the specialiser keeps a stack of the imported functions it is specialising. The checked-in guard drops every call of a function on the stack, including one strictly less specialised than the call being specialised (a recursive call at a type bound by a pattern match), which then runs overloaded; this tree carries the fix proposed in GHC [#27880](https://gitlab.haskell.org/ghc/ghc/-/work_items/27880) as an uncommitted patch to [Specialise.hs][g3], which specialises such a call when its key specialises strictly fewer arguments than every key on the stack (`strictlyMoreGeneral`, and the added paragraph of Note [Avoiding recursive specialisation]). Source: [Specialise.hs#L837][g620] (`spec_import`, its first guard `isIn "specImport" fn callers` returning no specialisation, for which the patch puts `good_calls = filter not_on_stack ...`), [Specialise.hs][g3] line 917 in the tree's patch (`strictlyMoreGeneral`), [Specialise.hs#L1127][g621] (Note [specImport call stack]), [Specialise.hs#L1155][g622] (Note [Avoiding recursive specialisation]). Met: GHC [#27880](https://gitlab.haskell.org/ghc/ghc/-/work_items/27880), `INLINABLE [1]` on horde-ad's recursive interpreter, 46.1 s against 31.8 s without the phase in the test of GHC [#26895](https://gitlab.haskell.org/ghc/ghc/-/work_items/26895), 31.5 s with the fix.

**Where the specialiser sits in the pipeline.** The specialiser runs once after the initial gentle simplification and before the first float-out, so a fresh specialised copy meets full laziness unsimplified (O09). With `-flate-specialise` it runs again near the end, after the last float-out, and no float-out follows it. Source: [compiler/GHC/Core/Opt/Pipeline.hs#L202][g419] (the gentle pass), [Pipeline.hs#L206][g493] (`runWhen do_specialise CoreDoSpecialising`), [Pipeline.hs#L209][g319] (the first float-out), [Pipeline.hs#L271][g623] (the last float-out), [Pipeline.hs#L309][g624] (`runWhen late_specialise $ CoreDoPasses [ CoreDoSpecialising, simplify "post-late-spec"]`). Met: GHC [#27894](https://gitlab.haskell.org/ghc/ghc/-/work_items/27894) and I3's join point, O09's; GHC [#27879](https://gitlab.haskell.org/ghc/ghc/-/work_items/27879) (`docs/ghc-issue-late-specialise-no-float-out.md`), `-flate-specialise` specialising the stable unfolding of an imported worker in which a `Typeable` constant stayed inside the loop, 8x to 11x slower, the defining module's float-out having moved it in the right-hand side only (U10).

**Dictionaries must not be scrutinised.** A `case` on a dictionary inside a function stops the specialisation of the calls under it; the specialiser's special case for such a `case` was removed on the premise that GHC never scrutinises a dictionary, worker/wrapper having stopped unboxing dictionaries ((DNB1)), as GHC [#27874](https://gitlab.haskell.org/ghc/ghc/-/work_items/27874)'s account traces it; but the call-by-value evaluation that `-fworker-wrapper-cbv` adds for strict worker arguments put a `case` on a strict dictionary argument back. This tree carries the fix of GHC [#27874](https://gitlab.haskell.org/ghc/ghc/-/work_items/27874) as an uncommitted patch to [compiler/GHC/Core/Utils.hs][g4], which skips dictionaries in `mkStrictFieldSeqs`. Source: [compiler/GHC/Core/Utils.hs#L3341][g625] (`mkStrictFieldSeqs`, the patched guard `not (isDictId arg_id)` at line 3353), [compiler/GHC/Core/Opt/WorkWrap/Utils.hs#L727][g626] ((DNB1) of Note [Do not unbox class dictionaries]). Met: GHC [#27874](https://gitlab.haskell.org/ghc/ghc/-/work_items/27874) (`docs/ghc-issue-cbv-dictionary-case.md`), a client specialising `f` but calling `g`'s worker with `$fNumDouble` when `Lib` was built `-fworker-wrapper-cbv`; P's noise-margin example, where removing `-fworker-wrapper-cbv` cost up to 3.8% in instructions.

**Auto rules and their copies are dropped unless kept.** A binding kept alive only by an auto-generated rule, for instance the copy of an INLINE function that has since been inlined everywhere, is dropped from the module's output together with its rule, unless `-fkeep-auto-rules` is on; an importer then cannot reuse it. Source: [compiler/GHC/Iface/Tidy.hs#L949][g627] (Note [Trimming auto-rules], GHC [#18532](https://gitlab.haskell.org/ghc/ghc/-/work_items/18532)), [compiler/GHC/Driver/Config/Tidy.hs#L54][g628] (`opt_keep_auto_rules`). Met: horde-ad builds `-fkeep-auto-rules`, as the comment on GHC [#23050](https://gitlab.haskell.org/ghc/ghc/-/work_items/23050) records, and that comment notes that `ghc --make` does not recompile a module when only this flag or `-fpolymorphic-specialisation` changes.

**Missed specialisations are warned about.** When an importer specialises an imported INLINE or INLINABLE function and finds inside it a call of another imported overloaded function it cannot specialise (no pragma, no `-fspecialise-aggressively`), `-Wmissed-specialisations` reports it, for calls reached through functions all carrying such pragmas; `-Wall-missed-specialisations` reports every one; class methods are never reported. Source: [Specialise.hs#L938][g629] (`tryWarnMissingSpecs`), [Specialise.hs#L1138][g630] (Note [Warning about missed specialisations]). Met: horde-ad's builds, whose loudest warning class is these "Could not specialise" lines, set aside as unfixable in its `CLAUDE.md`; S1's audit, which finds the same calls in the Core; and horde-ad's `astLetFun`, NOINLINE in part because INLINE "would also trigger specialization of many other functions from this module, which would fail, because their unfolding is not exposed" (its comment, commit 8af6df9ac).

[g1]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Map/Expr.hs
[g2]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs
[g3]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs
[g4]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Utils.hs
[g5]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L310
[g6]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L311
[g7]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L394
[g8]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L418
[g9]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L977
[g10]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold/Make.hs#L157
[g11]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold/Make.hs#L169
[g12]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold/Make.hs#L317
[g13]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold.hs#L293
[g14]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold.hs#L305
[g15]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold.hs#L312
[g16]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold.hs#L328
[g17]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold.hs#L326
[g18]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold.hs#L224
[g19]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold.hs#L327
[g20]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold.hs#L324
[g21]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold.hs#L331
[g22]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4926
[g23]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold.hs#L349
[g24]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold.hs#L502
[g25]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold.hs#L445
[g26]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold.hs#L353
[g27]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L318
[g28]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L320
[g29]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L392
[g30]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L433
[g31]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L337
[g32]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L709
[g33]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold.hs#L603
[g34]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold.hs#L780
[g35]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold.hs#L829
[g36]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold.hs#L373
[g37]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold.hs#L94
[g38]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L308
[g39]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold.hs#L1076
[g40]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L323
[g41]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold/Make.hs#L372
[g42]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold/Make.hs#L267
[g43]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Utils.hs#L1937
[g44]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1146
[g45]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1072
[g46]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L593
[g47]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L725
[g48]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L1670
[g49]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Pipeline.hs#L152
[g50]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L1469
[g51]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L1546
[g52]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L1620
[g53]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L1952
[g54]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4155
[g55]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L1522
[g56]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L1556
[g57]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Types/Tickish.hs#L294
[g58]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1000
[g59]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L984
[g60]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L887
[g61]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L874
[g62]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1059
[g63]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L474
[g64]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L2524
[g65]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L2490
[g66]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L1285
[g67]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L2004
[g68]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Driver/Config/Core/Opt/Simplify.hs#L79
[g69]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Pipeline.hs#L189
[g70]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Pipeline.hs#L261
[g71]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L2028
[g72]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/DmdAnal.hs#L314
[g73]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Iface/Syntax.hs#L470
[g74]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L331
[g75]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L153
[g76]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4097
[g77]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4108
[g78]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold.hs#L119
[g79]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L110
[g80]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L113
[g81]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L122
[g82]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Env.hs#L331
[g83]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Types/InlinePragma.hs#L443
[g84]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Types/InlinePragma.hs#L354
[g85]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Types/InlinePragma.hs#L382
[g86]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Parser.y#L2861
[g87]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Parser/PostProcess.hs#L3094
[g88]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Types/Id.hs#L781
[g89]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Types/Id/Info.hs#L611
[g90]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L103
[g91]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/IfaceToCore.hs#L1868
[g92]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/OccurAnal.hs#L1982
[g93]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/OccurAnal.hs#L1318
[g94]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/OccurAnal.hs#L2101
[g95]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/OccurAnal.hs#L2126
[g96]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/OccurAnal.hs#L1648
[g97]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/OccurAnal.hs#L2111
[g98]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/OccurAnal.hs#L1438
[g99]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/HsToCore.hs#L470
[g100]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L2433
[g101]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L2513
[g102]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L2579
[g103]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L2622
[g104]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1505
[g105]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/HsToCore/Errors/Ppr.hs#L236
[g106]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/WorkWrap/Utils.hs#L685
[g107]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/WorkWrap/Utils.hs#L754
[g108]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/ConstantFold.hs#L2196
[g109]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/ConstantFold.hs#L2665
[g110]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/ConstantFold.hs#L2703
[g111]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Rules.hs#L730
[g112]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Driver/Config/Core/Rules.hs#L19
[g113]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1521
[g114]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/libraries/ghc-internal/src/GHC/Internal/Magic.hs#L58
[g115]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Builtin/WiredIn/Ids.hs#L520
[g116]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/HsToCore/Expr.hs#L798
[g117]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Types/Id/Make.hs#L367
[g118]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L117
[g119]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Tc/TyCl/Instance.hs#L190
[g120]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Types/Id/Make.hs#L403
[g121]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Types/Id/Make.hs#L447
[g122]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold/Make.hs#L86
[g123]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/TyCon.hs#L1458
[g124]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold.hs#L855
[g125]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Types/InlinePragma.hs#L236
[g126]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1657
[g127]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1698
[g128]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1733
[g129]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1745
[g130]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1610
[g131]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1598
[g132]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Driver/Config/Core/Opt/Simplify.hs#L69
[g133]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/OccurAnal.hs#L2388
[g134]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1449
[g135]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1831
[g136]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1832
[g137]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1815
[g138]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1866
[g139]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1890
[g140]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1954
[g141]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1984
[g142]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L62
[g143]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L321
[g144]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L349
[g145]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L424
[g146]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L455
[g147]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold.hs#L507
[g148]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4474
[g149]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Exitify.hs
[g150]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1670
[g151]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L3063
[g152]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4855
[g153]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Pipeline.hs#L263
[g154]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L412
[g155]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L618
[g156]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L684
[g157]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L597
[g158]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L3268
[g159]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L3939
[g160]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/SimpleOpt.hs#L1553
[g161]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Rules.hs#L1137
[g162]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Rules.hs#L1715
[g163]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Utils.hs#L1947
[g164]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/Language/Haskell/Syntax/Binds/InlinePragma.hs#L138
[g165]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold.hs#L358
[g166]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold.hs#L438
[g167]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4887
[g168]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1668
[g169]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Parser/PostProcess.hs#L3113
[g170]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/WorkWrap.hs#L261
[g171]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/WorkWrap.hs#L835
[g172]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Types/InlinePragma.hs#L392
[g173]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/WorkWrap.hs#L585
[g174]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/Language/Haskell/Syntax/Binds/InlinePragma.hs#L174
[g175]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Types/Id/Make.hs#L870
[g176]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Types/Id/Make.hs#L1156
[g177]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Types/Id/Make.hs#L785
[g178]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Types/Id/Make.hs#L939
[g179]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Types/Id/Make.hs#L943
[g180]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Types/Id/Make.hs#L964
[g181]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Types/Id/Make.hs#L804
[g182]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold/Make.hs#L103
[g183]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/SimpleOpt.hs#L1314
[g184]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold/Make.hs#L116
[g185]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/WorkWrap.hs#L889
[g186]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/WorkWrap.hs#L817
[g187]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/WorkWrap.hs#L902
[g188]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/WorkWrap.hs#L452
[g189]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/WorkWrap.hs#L333
[g190]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/CoreToIface.hs#L657
[g191]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/CoreToIface.hs#L704
[g192]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Tc/Deriv/Generics.hs#L351
[g193]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Tc/Deriv/Generics.hs#L1064
[g194]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Driver/DynFlags.hs#L1340
[g195]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/libraries/ghc-internal/src/GHC/Internal/Data/Typeable/Internal.hs#L692
[g196]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/HsToCore/Binds.hs#L1785
[g197]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/libraries/ghc-internal/src/GHC/Internal/Data/Typeable/Internal.hs#L435
[g198]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/libraries/ghc-internal/src/GHC/Internal/Data/Typeable/Internal.hs#L444
[g199]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/libraries/ghc-internal/src/GHC/Internal/Fingerprint.hs#L48
[g200]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Utils.hs#L1094
[g201]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L2637
[g202]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4008
[g203]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/WorkWrap/Utils.hs#L624
[g204]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Utils.hs#L3154
[g205]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/OccurAnal.hs#L1239
[g206]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/OccurAnal.hs#L1817
[g207]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Iface/Tidy.hs#L704
[g208]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Driver/Session.hs#L3956
[g209]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Exitify.hs#L111
[g210]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Exitify.hs#L195
[g211]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/CSE.hs#L560
[g212]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/CSE.hs#L888
[g213]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/CSE.hs#L684
[g214]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/CSE.hs#L439
[g215]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/CSE.hs#L527
[g216]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/CSE.hs#L487
[g217]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/CSE.hs#L509
[g218]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L617
[g219]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L685
[g220]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Types/Tickish.hs#L293
[g221]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L1457
[g222]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L338
[g223]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/libraries/ghc-internal/src/GHC/Internal/Classes.hs#L342
[g224]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/libraries/ghc-internal/src/GHC/Internal/Classes.hs#L563
[g225]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Tc/Types/Evidence.hs#L1114
[g226]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/FloatOut.hs#L153
[g227]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/FloatOut.hs#L197
[g228]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/CSE.hs#L400
[g229]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/CSE.hs#L334
[g230]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/CSE.hs#L422
[g231]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Types/Demand.hs#L1597
[g232]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Types/Demand.hs#L1950
[g233]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Types/Demand.hs#L1848
[g234]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/libraries/ghc-internal/src/GHC/Internal/Err.hs#L44
[g235]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Builtin/primops.txt.pp#L2841
[g236]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Types/Demand.hs#L1610
[g237]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Tc/Gen/Sig.hs#L615
[g238]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Tc/Gen/Sig.hs#L622
[g239]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/HsToCore/Binds.hs#L474
[g240]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/HsToCore/Binds.hs#L441
[g241]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold/Make.hs#L165
[g242]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Iface/Syntax.hs#L495
[g243]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/HsToCore/Binds.hs#L487
[g244]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/HsToCore/Binds.hs#L495
[g245]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L402
[g246]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L414
[g247]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L408
[g248]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Iface/Tidy.hs#L745
[g249]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L2041
[g250]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L2771
[g251]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L2781
[g252]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L2040
[g253]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Driver/DynFlags.hs#L1303
[g254]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L2702
[g255]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L2763
[g256]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L2553
[g257]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L2613
[g258]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Utils.hs#L2380
[g259]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L2789
[g260]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1207
[g261]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4920
[g262]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L2192
[g263]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L2228
[g264]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L2247
[g265]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L2267
[g266]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L1005
[g267]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold.hs#L362
[g268]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold.hs#L505
[g269]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/HsToCore/Binds.hs#L466
[g270]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/HsToCore/Binds.hs#L468
[g271]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4957
[g272]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4964
[g273]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4939
[g274]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Iface/Syntax.hs#L494
[g275]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L2046
[g276]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L2049
[g277]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L2085
[g278]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Env.hs#L279
[g279]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L896
[g280]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L1272
[g281]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L1297
[g282]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L1623
[g283]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L1527
[g284]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L832
[g285]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L1262
[g286]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L253
[g287]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L255
[g288]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L1604
[g289]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L466
[g290]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L1304
[g291]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L1316
[g292]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Driver/Config/Core/Opt/Arity.hs#L13
[g293]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L1531
[g294]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L1414
[g295]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L1435
[g296]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Predicate.hs#L247
[g297]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L1625
[g298]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L1632
[g299]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L1611
[g300]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L1594
[g301]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Utils.hs#L1972
[g302]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L986
[g303]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L928
[g304]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L960
[g305]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L1090
[g306]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/DmdAnal.hs#L206
[g307]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/DmdAnal.hs#L145
[g308]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/CallArity.hs#L449
[g309]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/WorkWrap.hs#L766
[g310]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/WorkWrap/Utils.hs#L291
[g311]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/WorkWrap.hs#L699
[g312]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/WorkWrap.hs#L880
[g313]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/OccurAnal.hs#L3881
[g314]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/OccurAnal.hs#L632
[g315]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4847
[g316]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4850
[g317]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L897
[g318]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L1143
[g319]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Pipeline.hs#L209
[g320]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Pipeline.hs#L255
[g321]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/SetLevels.hs#L1545
[g322]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/SetLevels.hs#L1607
[g323]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/CallArity.hs#L371
[g324]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/FloatIn.hs#L819
[g325]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs
[g326]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/CallArity.hs#L569
[g327]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/CallArity.hs#L577
[g328]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/SetLevels.hs#L701
[g329]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/HsToCore/Binds.hs#L1064
[g330]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs#L911
[g331]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1212
[g332]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1214
[g333]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Driver/Config/Core/Opt/Simplify.hs#L84
[g334]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Utils.hs#L1928
[g335]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Utils.hs#L1967
[g336]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L1618
[g337]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L916
[g338]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L1555
[g339]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Pipeline.hs#L212
[g340]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/SetLevels.hs#L403
[g341]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Pipeline.hs#L274
[g342]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/SetLevels.hs#L1592
[g343]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Tc/Solver/Dict.hs#L568
[g344]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Tc/Solver/Dict.hs#L494
[g345]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Stg/EnforceEpt/Rewrite.hs#L332
[g346]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Runtime/Heap/Layout.hs#L366
[g347]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Stg/EnforceEpt.hs#L403
[g348]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Stg/EnforceEpt.hs#L417
[g349]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Stg/EnforceEpt.hs#L426
[g350]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Stg/EnforceEpt.hs#L263
[g351]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Stg/EnforceEpt/Types.hs#L48
[g352]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/CallArity.hs#L441
[g353]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/DmdAnal.hs#L116
[g354]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Arity.hs#L1010
[g355]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs#L1716
[g356]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Pipeline.hs#L257
[g357]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L2167
[g358]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1824
[g359]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1855
[g360]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1665
[g361]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L1914
[g362]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Rename/Expr.hs#L720
[g363]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Rename/Expr.hs#L725
[g364]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Rename/Expr.hs#L737
[g365]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Builtin/WiredIn/Ids.hs#L335
[g366]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Pipeline.hs#L180
[g367]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Pipeline.hs#L321
[g368]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/WorkWrap.hs#L438
[g369]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/WorkWrap.hs#L543
[g370]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L788
[g371]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L853
[g372]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs#L771
[g373]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Cmm/LayoutStack.hs#L139
[g374]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Driver/DynFlags.hs#L1351
[g375]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/CmmToAsm/Reg/Linear/JoinToTargets.hs#L154
[g376]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Types/Unique.hs#L195
[g377]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/CmmToAsm/Reg/Linear/JoinToTargets.hs#L130
[g378]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4859
[g379]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold.hs#L103
[g380]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/CmmToAsm/Reg/Linear.hs#L877
[g381]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/CmmToAsm/Reg/Linear/JoinToTargets.hs#L334
[g382]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/libraries/ghc-internal/src/GHC/Internal/Base.hs#L1862
[g383]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core.hs#L2007
[g384]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/ConstantFold.hs#L423
[g385]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/CoreToStg/Prep.hs#L1524
[g386]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/CmmToAsm/Reg/Linear/JoinToTargets.hs#L144
[g387]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L3307
[g388]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/libraries/ghc-internal/src/GHC/Internal/Magic.hs#L86
[g389]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/CoreToStg/Prep.hs#L1074
[g390]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs#L3086
[g391]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs#L3101
[g392]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs#L3203
[g393]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs#L3059
[g394]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/SetLevels.hs#L588
[g395]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/SetLevels.hs#L1584
[g396]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs#L3096
[g397]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs#L3117
[g398]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4890
[g399]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/CSE.hs#L724
[g400]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/CSE.hs#L144
[g401]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/WorkWrap/Utils.hs#L642
[g402]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Types/Cpr.hs#L55
[g403]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Types/Cpr.hs#L64
[g404]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/SetLevels.hs#L620
[g405]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/SetLevels.hs#L943
[g406]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/SetLevels.hs#L871
[g407]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/SetLevels.hs#L1267
[g408]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/SetLevels.hs#L1313
[g409]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L2389
[g410]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Monad.hs#L112
[g411]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Monad.hs#L95
[g412]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify.hs#L250
[g413]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Monad.hs#L232
[g414]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L2456
[g415]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L2807
[g416]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Monad.hs#L240
[g417]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L722
[g418]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Types/Id/Make.hs#L782
[g419]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Pipeline.hs#L202
[g420]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/SetLevels.hs#L615
[g421]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/SetLevels.hs#L611
[g422]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/SetLevels.hs#L381
[g423]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/SetLevels.hs#L444
[g424]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4325
[g425]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs#L3043
[g426]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs#L3029
[g427]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L2390
[g428]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/CoreToStg/Prep.hs#L1379
[g429]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/CmmToAsm/Reg/Linear.hs#L672
[g430]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/CmmToAsm/Reg/Linear.hs#L1019
[g431]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/CmmToAsm/Reg/Linear/JoinToTargets.hs#L286
[g432]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Pipeline.hs#L581
[g433]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/SimpleOpt.hs#L738
[g434]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/OccurAnal.hs#L4176
[g435]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/OccurAnal.hs#L4189
[g436]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/OccurAnal.hs#L4168
[g437]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/OccurAnal.hs#L4057
[g438]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/OccurAnal.hs#L871
[g439]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/OccurAnal.hs#L832
[g440]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core.hs#L964
[g441]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/OccurAnal.hs#L2688
[g442]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L2040
[g443]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L2097
[g444]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core.hs#L1167
[g445]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold/Make.hs#L205
[g446]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs#L2413
[g447]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4250
[g448]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4322
[g449]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/SetLevels.hs#L1880
[g450]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L302
[g451]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/StgToCmm/Expr.hs#L619
[g452]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/StgToCmm/Expr.hs#L608
[g453]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/StgToCmm/Expr.hs#L629
[g454]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/StgToCmm/Expr.hs#L212
[g455]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/StgToCmm/Expr.hs#L217
[g456]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/StgToCmm/Layout.hs#L143
[g457]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/StgToCmm/Expr.hs#L1190
[g458]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/StgToCmm/Expr.hs#L225
[g459]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L334
[g460]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4181
[g461]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4658
[g462]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold.hs#L772
[g463]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold.hs#L351
[g464]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/CprAnal.hs#L250
[g465]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/CprAnal.hs#L751
[g466]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/CprAnal.hs#L762
[g467]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/CprAnal.hs#L796
[g468]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/CprAnal.hs#L258
[g469]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/CprAnal.hs#L549
[g470]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/CprAnal.hs#L553
[g471]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold/Make.hs#L119
[g472]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1148
[g473]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1196
[g474]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L3806
[g475]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1189
[g476]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Types/Id/Make.hs#L791
[g477]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L2494
[g478]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L3258
[g479]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Cmm/LayoutStack.hs#L726
[g480]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Cmm/LayoutStack.hs#L732
[g481]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Cmm/Expr.hs#L342
[g482]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Cmm/Reg.hs#L127
[g483]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/CmmToAsm/Reg/Linear.hs#L935
[g484]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/CmmToAsm/Reg/Linear/JoinToTargets.hs#L246
[g485]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/CmmToAsm/Reg/Linear/JoinToTargets.hs#L247
[g486]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Types/Unique.hs#L456
[g487]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/StgToCmm.hs#L150
[g488]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1701-1703
[g489]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1733-1741
[g490]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1734
[g491]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L282
[g492]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L291
[g493]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Pipeline.hs#L206
[g494]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Pipeline.hs#L208
[g495]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/SetLevels.hs#L447
[g496]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/SetLevels.hs#L448
[g497]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/OccurAnal.hs#L783
[g498]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Pipeline.hs#L286
[g499]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/FloatIn.hs#L740
[g500]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Pipeline.hs#L276
[g501]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Pipeline.hs#L288
[g502]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/SetLevels.hs#L1098
[g503]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/SetLevels.hs#L360
[g504]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/WorkWrap/Utils.hs#L384
[g505]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/WorkWrap/Utils.hs#L415
[g506]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs#L3026
[g507]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4846
[g508]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4871
[g509]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Types/Basic.hs#L1086
[g510]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/CoreToIface.hs#L536
[g511]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/IfaceToCore.hs#L1906
[g512]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/CSE.hs#L437
[g513]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/CSE.hs#L514
[g514]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/CSE.hs#L233
[g515]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core.hs#L2139
[g516]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/HsToCore/Binds.hs#L458
[g517]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold/Make.hs#L172
[g518]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4938
[g519]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/IfaceToCore.hs#L1911
[g520]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L319
[g521]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Iface/Tidy.hs#L762
[g522]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Iface/Tidy.hs#L1313
[g523]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Driver/Config/Tidy.hs#L47
[g524]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Driver/DynFlags.hs#L1307
[g525]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/IfaceToCore.hs#L1849
[g526]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold.hs#L96
[g527]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Driver/Session.hs#L1872
[g528]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/WorkWrap.hs#L785
[g529]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold/Make.hs#L383
[g530]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold/Make.hs#L461
[g531]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/WorkWrap.hs#L369
[g532]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/WorkWrap.hs#L736
[g533]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/WorkWrap.hs#L862
[g534]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/WorkWrap.hs#L840
[g535]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold/Make.hs#L126
[g536]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/WorkWrap.hs#L186
[g537]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/WorkWrap.hs#L561
[g538]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/WorkWrap.hs#L167
[g539]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Types/Id/Info.hs#L633
[g540]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core.hs#L2042
[g541]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L521
[g542]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/SpecConstr.hs#L2132
[g543]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L2168
[g544]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L1286
[g545]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4897
[g546]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1246
[g547]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1371
[g548]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/HsToCore/Binds.hs#L444
[g549]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Tc/TyCl/Class.hs#L310
[g550]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold/Make.hs#L69
[g551]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L123
[g552]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Iface/Tidy.hs#L707
[g553]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Tc/TyCl/Instance.hs#L2533
[g554]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Tc/TyCl/Instance.hs#L2262
[g555]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/Language/Haskell/Syntax/Binds/InlinePragma.hs#L248
[g556]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Types/Id/Make.hs#L246
[g557]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Builtin/WiredIn/Ids.hs#L169
[g558]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/HsToCore.hs#L799
[g559]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold/Make.hs#L178
[g560]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold/Make.hs#L223
[g561]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs#L1629
[g562]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs#L1739
[g563]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/HsToCore/Binds.hs#L302
[g564]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/HsToCore/Binds.hs#L1044
[g565]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/HsToCore/Binds.hs#L1218
[g566]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4387
[g567]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/DmdAnal.hs#L1185
[g568]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/DmdAnal.hs#L1515
[g569]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Types/Demand.hs#L869
[g570]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L613
[g571]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L690
[g572]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L447
[g573]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Map/Expr.hs#L376
[g574]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Map/Expr.hs#L346
[g575]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/CprAnal.hs#L90
[g576]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/WorkWrap/Utils.hs#L645
[g577]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/libraries/ghc-internal/src/GHC/Internal/ForeignPtr.hs#L165
[g578]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/WorkWrap/Utils.hs#L761
[g579]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Utils.hs#L3146
[g580]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L5073
[g581]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1220
[g582]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1232
[g583]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Driver/Config/Core/Opt/Simplify.hs#L31
[g584]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L322
[g585]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Unfold.hs#L142
[g586]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Driver/Session.hs#L1885
[g587]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L361
[g588]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Inline.hs#L379
[g589]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Env.hs#L169
[g590]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Driver/Main/Compile.hs#L790
[g591]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/CoreToStg/Prep.hs#L1543
[g592]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/HsToCore/Binds.hs#L472
[g593]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/HsToCore/Foreign/C.hs#L323
[g594]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs#L3281
[g595]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L2204
[g596]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4986
[g597]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/OccurAnal.hs#L2230
[g598]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/Language/Haskell/Syntax/Binds/InlinePragma.hs#L121
[g599]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1334
[g600]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/CSE.hs#L455
[g601]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/docs/users_guide/using-optimisation.rst#L1815
[g602]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs#L703
[g603]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs#L995
[g604]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs#L761
[g605]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs#L685
[g606]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Driver/DynFlags.hs#L1339
[g607]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Driver/DynFlags.hs#L1338
[g608]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs#L2775
[g609]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs#L3003
[g610]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs#L2462
[g611]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs#L2477
[g612]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs#L3164
[g613]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/HsToCore/Binds.hs#L999
[g614]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/HsToCore/Binds.hs#L1247
[g615]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Tc/TyCl/Instance.hs#L2603
[g616]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Tc/TyCl/Instance.hs#L2239
[g617]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs#L2336
[g618]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs#L1794
[g619]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs#L2314
[g620]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs#L837
[g621]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs#L1127
[g622]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs#L1155
[g623]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Pipeline.hs#L271
[g624]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Pipeline.hs#L309
[g625]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Utils.hs#L3341
[g626]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/WorkWrap/Utils.hs#L727
[g627]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Iface/Tidy.hs#L949
[g628]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Driver/Config/Tidy.hs#L54
[g629]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs#L938
[g630]: https://gitlab.haskell.org/ghc/ghc/-/blob/6913545fd388ad9e9258b7c8b33b23d2f86f4640/compiler/GHC/Core/Opt/Specialise.hs#L1138
