# GHC issue comment: a join point made by case-of-case, with two jumps, also hides a nested CPR

Posted 2026-10-17 as a comment on GHC [#21148](https://gitlab.haskell.org/ghc/ghc/-/work_items/21148) ("Exit join points inhibit CPR", open again since Mikolaj's comment of 2026-10-03); this file stays as the record of the comment, the text from "Here is a form" down being the body as posted. Verified with GHC HEAD 10.1.20260918 and ghc-9.14.1, which give the same result. The issue's description and all its notes were read on 2026-10-17. They already have the gap itself (sgraf812: "the single jump to `$j_s15t` passes the integer boxed. Unfortunately, we don't see that in the join body"), the remedy of inlining the join point, and, in Mikolaj's comment, the `isExitJoinId` route that stops that inlining; this comment repeats none of them. New here: a join point that is not an exit join point, two jumps, the cost, and `-flate-dmd-anal`. The prose is ASD-STE100 Simplified Technical English. Stated as open: whether `-flate-dmd-anal` also recovers on master, which was not built.

Here is a form of the same gap with no loop and no exit join point, so `isExitJoinId` has no part in it. Case-of-case makes a join point with two jumps. The simplifier does not inline it before CPR analysis, because no argument of the join point is scrutinised (Note [Inlining join points]). CPR analysis then gives the strict parameter `arg` no CPR property, and the nested `P` stays boxed.

```haskell
module ReproLib (P (..), Q (..), f) where

data P = P !Int !Int
data Q = Q !Int !P

f :: Bool -> Int -> Q
{-# NOINLINE f #-}
f c x = Q x (if c then P x 1 else P 2 x)
```

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import ReproLib
import System.Environment (getArgs)

main :: IO ()
main = do
  [n] <- map read <$> getArgs
  let go :: Int -> Int -> Int
      go !acc i
        | i > n = acc
        | otherwise = case f (even i) i of
            Q a (P b c) -> go (acc + a + b + c) (i + 1)
  print (go 0 1)
```

Save them as `ReproLib.hs` and `Repro.hs`, then `ghc -O -rtsopts -ddump-cpr-signatures -ddump-cpranal -ddump-simpl -dsuppress-all -dsuppress-uniques -ddump-to-file Repro.hs` and `./Repro 100000 +RTS -s`. On HEAD (10.1.20260918) and 9.14.1, CPR analysis sees the join point (`ReproLib.dump-cpranal`):

```
f = \ c x ->
      join { $j arg = $WQ x arg } in
      case c of {
        False -> jump $j (case x of { I# unbx -> P 2# unbx });
        True -> jump $j (case x of { I# unbx -> P unbx 1# })
      }
```

Both jumps pass a `P`, but the signature is `f: 1`, and the worker returns `P` boxed:

```
$wf
  = \ c ww ->
      case c of {
        False -> (# ww, P 2# ww #);
        True -> (# ww, P ww 1# #)
      }
```

On HEAD, the program allocates 2,456,256 bytes; 9.14.1 gives the same signatures and the same differences below. With `f c x = Q x (P (if c then x else 2) (if c then 1 else x))`, which makes no join point, the signature is `f: 1(, 1)`, the worker returns `(# ww, ww, 1# #)`, and the program allocates 56,256 bytes. The difference is 24 bytes a call, one `P`.

With `-fforce-recomp -dinline-check '$j'` added, of the twelve decisions in `ReproLib` the first ten say `ANSWER = NO`, the first of them with `guidance IF_ARGS [0] 30 0`, and the last two say `ANSWER = YES`, with `guidance IF_ARGS [20] 10 10`. So the simplifier inlines `$j` after CPR analysis has fixed the signature. Thus `-flate-dmd-anal` recovers it: the second analysis gives `f: 1(, 1)`, and the program allocates 56,256 bytes.

A possible remedy: CPR analysis gives a strict join point parameter the least upper bound of the CPR of the arguments at its jumps.
