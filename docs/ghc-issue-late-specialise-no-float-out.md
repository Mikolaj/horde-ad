# GHC issue: after `-flate-specialise`, nothing floats constants out of the specialised code, so a `TypeRep` is rebuilt on every loop iteration

Draft, not filed; the text from "## Summary" down is the body to file, in the tracker's bug template. Title: **`-flate-specialise`: no float-out runs after the late specialiser, so a constant `TypeRep` from an inlined unfolding is rebuilt, MD5 fingerprint included, on every iteration of the specialised loop**. Verified on 2026-09-30 on HEAD 10.1.20260925 (nightly bindist of commit `9f48a5b908`), 9.14.1 and 9.12.2. Found while reducing GHC [#26895](https://gitlab.haskell.org/ghc/ghc/-/work_items/26895): with `-flate-specialise` on one test module, horde-ad's test ran 5x slower on HEAD instead of faster, because GHC [#27873](https://gitlab.haskell.org/ghc/ghc/-/work_items/27873) left the hot calls to the late specialiser. The tracker was searched on 2026-09-30 for `late-specialise`, `late specialisation`, `mkTrCon`, `TypeRep fingerprint` and float-out after specialisation, with no duplicate found; GHC [#21183](https://gitlab.haskell.org/ghc/ghc/-/work_items/21183) is the nearest.

## Summary

In the reproducer below, `-flate-specialise` makes the program 8x to 11x slower and makes it allocate 6x to 21x more. The late specialiser specialises the imported `f` at `Double` in `Main`. The specialised loop then evaluates `mkTrCon $tcFloat []` on every iteration, and `mkTrCon` computes an MD5 fingerprint each time:

```
$s$wf
  = \ ww acc ->
      case ww of wild {
        __DEFAULT ->
          case lvl of wild1 { TrTyCon ipv ipv1 ipv2 ipv3 ipv4 ->
          case mkTrCon $tcFloat [] of wild2
          { TrTyCon ipv5 ipv6 ipv7 ipv8 ipv9 ->
          case sameTypeRep wild1 wild2 of {
            False ->
              case acc of { D# x -> $s$wf (-# wild 1#) (D# (+## x 1.0##)) };
            True -> case acc of vx { D# ipv10 -> $s$wf (-# wild 1#) vx }
          }
          }
          };
        0# -> acc
      }
```

The expression `mkTrCon $tcFloat []` is the `Typeable Float` evidence in the stable unfolding of `isFloat`, which the post-late-spec simplifier inlines into the loop. It is a constant, and full laziness would float it to the top level. But in [the pipeline](https://gitlab.haskell.org/ghc/ghc/-/blob/9f48a5b908f572847bc8ba4657c9f5a5d4284556/compiler/GHC/Core/Opt/Pipeline.hs#L309-310) the late specialiser and its simplifier run after [the last float-out pass](https://gitlab.haskell.org/ghc/ghc/-/blob/9f48a5b908f572847bc8ba4657c9f5a5d4284556/compiler/GHC/Core/Opt/Pipeline.hs#L271-276), and the simplifier does not float an expression out of a lambda. Without `-flate-specialise`, `f` runs its dictionary-passing code from `Lib`, where full laziness floated the same `TypeRep` to the top level, so the program is faster without the specialisation than with it.

A `TypeRep` is the expensive case, but any constant that an inlining puts into late-specialised code stays where it is.

In horde-ad, the effect is the same: with `-flate-specialise` on one test module, the late specialisations of the interpreter rebuild `TypeRep`s for the `eqT` dispatch in an inlined class method, and the test runs in 280 s instead of 57 s, allocating 749 GB instead of 79 GB. Under callgrind, on a smaller input, a third of the instructions are in `MD5Transform`, `peekW64`, `pokeW64` and `mkTrCon`.

A possible fix, not tested: a float-out pass after the post-late-spec simplifier, as the late specialiser adds code that the last float-out pass did not see.

### Related

- #27873: a bug in the regular specialiser that leaves calls for the late specialiser; that is how horde-ad met this.
- #26895: horde-ad's slowdown, found while reducing it.
- #21183: `TypeRep` evidence of a known type is computed at run time, in a CAF. If `mkTrCon` of a known type were a static constructor, the rebuilt `TypeRep` here would cost nothing, but any other constant in late-specialised code would still not be floated.

## Steps to reproduce

```haskell
module Lib (f) where

import Data.Typeable

isFloat :: Typeable a => a -> Bool
{-# INLINE isFloat #-}
isFloat x = typeOf x == typeOf (0 :: Float)

f :: (Typeable a, Num a) => Int -> a -> a
{-# INLINABLE f #-}
f 0 acc = acc
f n acc = f (n - 1) $! if isFloat acc then acc else acc + 1
```

```haskell
import Lib

main :: IO ()
main = print (f 1000000 (0 :: Double))
```

Save the modules as `Lib.hs` and `Repro.hs`. `-fno-specialise` stands in for anything that makes the regular specialiser miss the call of `f`, so that only the late specialiser specialises it:

```
ghc -O -fno-specialise Repro.hs -o Repro && ./Repro +RTS -s
ghc -O -fno-specialise -flate-specialise Repro.hs -o Repro && ./Repro +RTS -s
```

| compiler | `-O -fno-specialise` | with `-flate-specialise` |
|---|---|---|
| HEAD 10.1.20260925 | 0.029 s, 56 MB | 0.324 s, 1184 MB |
| 9.14.1 | 0.030 s, 56 MB | 0.250 s, 512 MB |
| 9.12.2 | 0.027 s, 88 MB | 0.240 s, 544 MB |

The numbers are the same with `-O2`. On HEAD with `-O` alone, the regular specialiser specialises `f`, and the program runs in 0.012 s and allocates 100 KB.

Both modules are needed: when `f` is defined in `Main`, the late specialiser starts from the optimised right-hand side of `f`, where the constant is already floated. The `INLINE` helper is needed too: with `typeOf (0 :: Float)` written directly in `f`, the constant is at the top of the unfolding of `f`, outside its lambdas, and the post-late-spec simplifier floats it.

## Expected behavior

With `-flate-specialise`, the specialised loop uses a top-level `TypeRep` for `Float`, and the program is at least as fast as without the flag.

## Environment

* GHC version used: HEAD 10.1.20260925 (commit 9f48a5b908), 9.14.1, 9.12.2

Optional:

* Operating System: Ubuntu 24.04
* System Architecture: x86_64

/label ~"T::bug"
/label ~"needs triage"
