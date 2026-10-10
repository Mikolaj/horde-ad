# GHC issue comment: equality constraints do affect the automatic specialisation, one level down

Posted 2026-10-10 as a comment on GHC [#23798](https://gitlab.haskell.org/ghc/ghc/-/work_items/23798), pointing to GHC [#27920](https://gitlab.haskell.org/ghc/ghc/-/work_items/27920), filed from `docs/ghc-issue-equality-cast-dictionary.md`; this file stays as the record of the comment. It answers the last comment there, Mikolaj's of 2024-02-06. The text from "On 2024-02-06" down is the body as drafted. The example at its end, `g` from the comment of 2023-08-09 with an argument added so that it can have a body, was verified on 2026-10-10 on HEAD 10.1.20260918, 9.14.1, 9.12.4 and 9.6.7. The prose is ASD-STE100 Simplified Technical English.

On 2024-02-06, I wrote that Simon thinks this problem does not affect the automatic specialisation, and that I would examine this. The automatic specialisation of a function with an equality constraint works. But it does not continue to the overloaded functions that the function calls at the other side of the equality. #27920 has a reproducer and the cause. Both problems start at the same step: the typechecker takes the coercion out of the given equality and casts with it. Here, that cast is in the left-hand side of the rule. There, it is in the dictionary of the call, and the specialiser leaves the call overloaded.

Also, a version of `g` from the comment of 2023-08-09 still gives "RULE left-hand side too complicated to desugar" with `ghc -O -c Repro.hs`, on 9.6.7, 9.12.4, 9.14.1 and HEAD (10.1.20260918):

```haskell
{-# LANGUAGE TypeFamilies #-}
module Repro (g) where

g :: (a ~ b, Eq c) => (a, b) -> c -> Bool
g (_, _) z = z == z
{-# SPECIALISE g :: (a ~ b) => (a, b) -> Int -> Bool #-}
```
