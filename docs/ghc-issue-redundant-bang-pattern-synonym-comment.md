# GHC issue comment: -Wredundant-bang-patterns inherits the strict pattern-synonym assumption, and following it changes the program

Staged 2026-09-29 as a comment on GHC [#17357](https://gitlab.haskell.org/ghc/ghc/-/work_items/17357) and posted the same day as [a comment](https://gitlab.haskell.org/ghc/ghc/-/work_items/27862#note_701165) on GHC [#27862](https://gitlab.haskell.org/ghc/ghc/-/work_items/27862), under a preface not carried here; this file stays as the record of the comment, the text from "`-Wredundant-bang-patterns` (#17340)" down being the body. The prose is ASD-STE100 Simplified Technical English. Found while answering whether #27862, whose filed record is [ghc-issue-redundant-bang-splits-match.md](ghc-issue-redundant-bang-splits-match.md), can change semantics: it cannot, because its defect is in the grouping of equations and both groupings are correct, but the warning that it is about can be wrong, and this is the case. The tracker search of 2026-09-29 for "redundant-bang-patterns" and "redundant bang" found no report with a reproducer. The risk is named in the discussion of #17340, in two notes of 2020-07-03: "a good example where we'd give unsound advice (see #17357 for why)", about a bang directly on a lazy synonym, `f !(Con _)` with `pattern Con x <- ~[x]`. The warning as implemented reports only dead bangs (`Note [Dead bang patterns]` in `GHC.HsToCore.Pmc.Check`), and on HEAD it does not warn on that example.

`-Wredundant-bang-patterns` (#17340) still inherits the assumption of this ticket, and gives unsound advice with it. The discussion of #17340 expected this for a bang directly on a lazy pattern synonym, and the implemented warning does not report such a bang. But it reports a bang in a later equation, and there the same assumption applies. Below is a reproducer where the program changes if you follow the warning.

`isPmAltConMatchStrict` in `GHC.HsToCore.Pmc.Solver.Types` returns `True` for a pattern synonym, with a reference to this ticket. Thus, after an equation with a pattern synonym fails, the checker knows that the argument is not bottom, and it reports a bang on that argument in a later equation as redundant. If the matcher of the synonym does not force its argument, the bang is not redundant.

`Repro.hs`:

```haskell
{-# LANGUAGE BangPatterns, PatternSynonyms, ViewPatterns #-}
module Main (main) where

import Control.Exception (ErrorCall, evaluate, try)

-- Never matches, and does not force its argument.
pattern F :: Bool
pattern F <- (const False -> True)

withBang :: Bool -> Int
withBang F = 1
withBang !_ = 2

-- The same function, with the warning followed.
withoutBang :: Bool -> Int
withoutBang F = 1
withoutBang _ = 2

run :: Int -> IO String
run v = either (\e -> const "bottom" (e :: ErrorCall)) show <$> try (evaluate v)

main :: IO ()
main = do
  a <- run (withBang undefined)
  b <- run (withoutBang undefined)
  print (a, b)
```

`ghc -Wredundant-bang-patterns Repro.hs` reports the bang in `withBang` as redundant, at line 12, column 11. Then `./Repro` prints `("bottom","2")`: `withoutBang` is `withBang` with the warning followed, and its result for `undefined` is different. The result is the same at `-O0` and `-O`, on GHC 9.8.4, 9.10.3, 9.12.4, 9.14.1 and HEAD (10.1.20260918, 6913545fd3). On HEAD, when the view pattern `(const False -> True)` is written directly in the equation, GHC gives no warning.

The decision in this ticket (2019-10-18) was to treat such synonyms as degenerate and not to bother about them. The description already shows that, for `f`, the deletion of a clause that GHC reports as redundant is unsound. The bang warning (731c8d3bc5, 2020-05-22, first in 9.2.1) adds a second warning with the same risk.

Two possible changes. The check for dead bangs can ignore the strictness assumption for pattern synonyms, and the coverage checks can keep it. Or, if the assumption stays for all checks, the documentation of `-Wredundant-bang-patterns` can tell that the warning assumes that each match on a pattern synonym forces its argument.
