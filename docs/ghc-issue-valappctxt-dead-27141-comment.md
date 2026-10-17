# GHC issue comment: `ValAppCtxt` and its consumers are dead together with the `TickIt` continuation

Posted 2026-10-17 as a comment on GHC [#27141](https://gitlab.haskell.org/ghc/ghc/-/work_items/27141) ("Clean up tick handling in the simplifier"); this file stays as the record of the comment, the text from "A consequence" down being the body as posted. No reproducer: this is a reading of the code, cited by permalinks to master f93d523c (2026-10-15), whose Simplify/Utils.hs, Simplify/Iteration.hs and Simplify/Inline.hs were read for it; the HEAD build's tree has the same single caller of `interestingCallContext` (grep of its compiler/). Rechecked before posting on master 7dedcf13 (2026-10-16): the only code that builds a `TickIt` rebuilds one it was given, `interestingCallContext` has one caller, and the uses of `ValAppCtxt` are the same. The issue's description and all its notes were read on 2026-10-17. The premise, that no code makes a `TickIt` continuation, is already in the description and in simonpj's note on GHC MR [!15494](https://gitlab.haskell.org/ghc/ghc/-/merge_requests/15494); a search of the tracker's issues, notes and merge requests found none that says `ValAppCtxt` is unreachable. The body states one caveat: the `pushTick` plan of the issue could make `ValAppCtxt` live again. The prose is ASD-STE100 Simplified Technical English. Nothing is stated as open.

A consequence of `TickIt` being dead: `ValAppCtxt` is dead too, with the code that consumes it.

1. `interestingCallContext` has one caller, `tryInlining`, which gives it the continuation that `contArgs` leaves ([Simplify/Iteration.hs, lines 2502-2503][try-inlining]).
2. `contArgs` consumes each `ApplyToVal`, `ApplyToTy` and `CastIt`, and stops at the first other continuation ([Simplify/Utils.hs, lines 593-610][cont-args]).
3. Thus `interesting (ApplyToVal {}) = ValAppCtxt` ([Simplify/Utils.hs, lines 1001-1004][val-app]) is reached only through `interesting (TickIt _ k) = interesting k` ([line 1010][tick-it]), when a `TickIt` stands between the call and a value argument. No code makes such a continuation.
4. The example in the comment at that line, `(f Int |> co) y`, does not reach it, because `contArgs` consumes the cast and the argument.
5. The consumers of `ValAppCtxt` are dead with it: the `interesting_call` alternative ([Simplify/Inline.hs, lines 407-413][inline-413]), the result discount ([lines 733-736][inline-736]), and Note [Cast then apply] ([lines 590-598][note-cast]), which explains the first of them.

So `ValAppCtxt` can go together with `TickIt`. If `pushTick` makes a `TickIt` between a function and its value argument, for example for `(tick f) x`, then `ValAppCtxt` is live again, and it stays.

[try-inlining]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L2502-2503
[cont-args]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Simplify/Utils.hs#L593-610
[val-app]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1001-1004
[tick-it]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1010
[inline-413]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Simplify/Inline.hs#L407-413
[inline-736]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Simplify/Inline.hs#L733-736
[note-cast]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Simplify/Inline.hs#L590-598
