# GHC issue comment: a partial specialisation of an INLINABLE function has no unfolding, so importers cannot specialise it further

Posted 2026-09-29 as a comment on GHC [#23050](https://gitlab.haskell.org/ghc/ghc/-/work_items/23050), whose description predicts this effect and which had no reproducer of its cost; this file stays as the record of the comment, the text from "With `-fpolymorphic-specialisation` now on by default" down being the body as posted. It was first drafted as a new issue, before the tracker search of 2026-09-29 found #23050. The prose is ASD-STE100 Simplified Technical English. The loss of the unfolding is intended: Note [Specialising unfoldings] in `GHC.Core.Unfold.Make` drops the stable unfolding of an INLINABLE function when it is specialised, because "the specialised function (probably) isn't overloaded any more", and `specUnfolding` does this for `SPECIALISE` pragmas and for the specialiser alike. Found in horde-ad's `AstSimplify`, whose header carries `-fno-expose-overloaded-unfoldings` while the package compiles with `-fpolymorphic-specialisation -fkeep-auto-rules`: the rule `SPEC astTimesK @_ @(PrimalStepSpan FullSpan)` sends importers to a copy that is not specialised on the element type, and ticky counts put the loss on the `grad` benchmarks of `shortProdForCI` at 2 to 3% of allocation. A side observation, maybe for GHC [#27667](https://gitlab.haskell.org/ghc/ghc/-/work_items/27667): `ghc --make` does not recompile a module when only `-fkeep-auto-rules` or `-fpolymorphic-specialisation` changes, although each flag changes what the module exports.

With `-fpolymorphic-specialisation` now on by default, this is triggered more often and in unexpected ways, but fortunately there is a cheap workaround: compile the module that defines the INLINABLE function with `-fexpose-overloaded-unfoldings` (GHC 9.12 and later) or `-fexpose-all-unfoldings`. Then its interface has an unfolding for the partial specialisation too, and importers specialise it at the remaining classes. A `SPECIALISE` pragma for the full type in the importer does not help: the call still goes to the partial specialisation.

BTW, this reproducer confirms the second scenario of the description, and shows its cost. It needs only `-O`, on GHC 9.10.3, 9.12.4, 9.14.1 and HEAD (10.1.20260918).

`ReproLib.hs`:

```haskell
module ReproLib (Weight (..), W3 (..), step) where

class Weight s where
  weight :: s -> Int

data W3 = W3
instance Weight W3 where
  weight _ = 3

step :: (Weight s, Num r) => s -> Int -> r -> r
step _ 0 acc = acc
step s n acc = step s (n - 1) (acc + fromIntegral (weight s))
{-# INLINABLE step #-}

{-# SPECIALISE step :: Num r => W3 -> Int -> r -> r #-}
```

`Repro.hs`:

```haskell
module Main (main) where

import ReproLib

main :: IO ()
main = print (step W3 10000000 (0.5 :: Double))
```

`ghc -O -Wmissed-specialisations Repro.hs && ./Repro +RTS -s` gives 1,212,794,224 bytes of allocation on HEAD. Without the `SPECIALISE` pragma, it gives 100,704 bytes. The rule of the pragma fires in `Repro` and sends the call to `step_$sstep`. Its worker `$w$sstep :: Num r => Int# -> r -> r` has no unfolding in the interface, thus `Repro` cannot specialise it (`-Wmissed-specialisations` reports this), and calls it with the dictionary:

```
main4 = $w$sstep $fNumDouble 10000000# main5
```

Without the pragma, `Repro` specialises `step` at both types from its INLINABLE unfolding, and gets a loop on `Int#` and `Double#`. Thus the pragma makes the importer slower than no pragma. With the workaround on `ReproLib`, the result is 100,704 bytes again.

The specialiser makes the same partial specialisation without a pragma. Replace the pragma with a local call at a known `s` only, `stepW3 n acc = step W3 n acc + 1` (exported), and add `-fkeep-auto-rules`. The result is again 1.2 GB, on HEAD because `-fpolymorphic-specialisation` is now on by default (1fd259874d), and on 9.10.3 to 9.14.1 when you also add `-fpolymorphic-specialisation`.

This supports the idea in the description: keep the stable unfolding of a specialisation that is still overloaded.
