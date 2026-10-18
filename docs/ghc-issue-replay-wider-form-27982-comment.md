# GHC issue comment: a small reproducer of the wider form, in which the join point is made after worker/wrapper and a box is allocated on a path that does not use it

Posted 2026-10-18 as a comment on GHC [#27982](https://gitlab.haskell.org/ghc/ghc/-/work_items/27982) ("Since 9.10, a join point jumped to only from other join points, which a loop jumps to, is marked as inside a lambda and is never inlined"), horde-ad's own issue (`docs/ghc-issue-join-point-replay-inside-lambda.md`); this file stays as the record of the comment, the text from "The description says" down being the body as posted. Verified on 2026-10-18 with GHC HEAD 10.1.20260918 (`wip/T27737` at 6913545fd3 on master e2d5702699, with uncommitted patches in five files) and ghc-9.14.1, 9.12.4, 9.10.3, 9.8.4 and 9.6.7; 9.14.1, 9.12.4 and 9.10.3 give the result of HEAD, so the patches are not needed. The issue's description and all its notes were read on 2026-10-18; it had no comments before this one. The reproducer is a reduction of orthotope's Shaped `rerank` empty row at orthotope 22fe4c8e, where the box is the `PlainPtr` of a Storable vector's buffer, 16 bytes a call (item O28 of `docs/inlining-catalogue.md`). Code checked at master f93d523c (2026-10-15); Pipeline.hs and FloatIn.hs there are the same as in the HEAD build. The prose is ASD-STE100 Simplified Technical English. Nothing is stated as open.

The description says that I do not have a small reproducer of the wider form. Here is one. No Exitification is necessary, the join point is made by the simplifier after worker/wrapper, and the cost is a box that is allocated on a path that does not use it.

```haskell
{-# LANGUAGE BangPatterns #-}
module ReproLib (P (..), V (..), A (..), row) where

data P = P !Int | Q
data V = V !Int !Int !P
newtype A = A V

{-# OPAQUE use #-}
use :: P -> Int -> Int
use (P a) i = a + i
use Q i = i

{-# NOINLINE row #-}
row :: Int -> A
row n =
  let p = P n
      go :: Int -> Int -> Int
      go !i !acc | i >= n = acc
                 | otherwise = go (i + 1) (acc + use p i)
  in if n <= 0 then A (V 0 0 p) else case go 0 0 of s -> A (V s 1 p)
```

```haskell
{-# LANGUAGE BangPatterns, MagicHash #-}
module Main (main) where

import GHC.Exts (Int (I#), Int#)
import ReproLib
import System.Environment (getArgs)

-- OPAQUE, so that each iteration calls row anew, on the empty path.
{-# OPAQUE size #-}
size :: Int# -> Int
size _ = 0

main :: IO ()
main = do
  [s] <- getArgs
  let iters = read s :: Int
      loop :: Int -> Int -> Int
      loop !i@(I# i#) !acc
        | i == 0 = acc
        | otherwise = case row (size i#) of A (V a b _) -> loop (i - 1) (acc + a + b)
  print (loop iters 0)
```

Save the modules as `ReproLib.hs` and `Repro.hs`, build with `ghc -O -rtsopts -ddump-simpl -dsuppress-all -dsuppress-uniques -ddump-to-file Repro.hs`, and run `./Repro 1000000 +RTS -s` and `./Repro 2000000 +RTS -s`, and `perf stat -e instructions:u -x,` on the same commands. All calls take the path `n <= 0`. The cost a call is the difference between the two runs, divided by 1000000:

```
GHC      bytes a call   instructions a call
HEAD     16.00          33.49
9.14.1   16.00          33.49
9.12.4   16.00          33.49
9.10.3   16.00          33.49
9.8.4     0.00          32.00
9.6.7     0.00          32.00
```

HEAD with `-fno-exitification` gives the same figures, and at `-O2` the box stays in the same place. On HEAD, the final Core allocates the box `p` before the test, and the path `n <= 0` does not use it:

```
$wrow
  = \ ww ->
      let { p = P ww } in
      case <=# ww 0# of {
        __DEFAULT ->
          join { $j unbx = (# unbx, 1#, ww #) } in
          joinrec {
            $wgo i ww1
              = case i of i1 { I# ipv ->
                case >=# ipv ww of {
                  __DEFAULT ->
                    case use p i1 of { I# y -> jump $wgo (I# (+# ipv 1#)) (+# ww1 y) };
                  1# -> jump $j ww1
                }
                }; } in
          jump $wgo lvl 0#;
        1# -> (# 0#, 0#, ww #)
      }
```

On 9.8.4, the `let { p = P ww } in` is the first line of the `__DEFAULT` branch, and the rest is the same.

The steps:

1. In the simplifier run after worker/wrapper, the simplifier makes a join point `$j :: A %1 -> (# Int#, Int#, Int# #)` for the case that takes the result of the worker apart. One jump to it is on the path `n <= 0`, under no lambda. The other is in the join point `$j :: Int# %1 -> (# Int#, Int#, Int# #)` that the loop `$wgo` jumps to on exit. `-ddump-occur-anal` gives the new join point `[Occ=OnceL2!T[1]]` on HEAD and `[Occ=Once2!T[1]]` on 9.8.4. On HEAD, `-ddump-simpl-iterations` shows it with no unfolding in both iterations of that run, and it is not inlined. On 9.8.4, the second iteration inlines it.
2. On HEAD, the join point is closed, and the late float-out moves it to the top level as a function (`floatJoinsToTop`, [Pipeline.hs, lines 271-276][late-float]). Both paths then give `p` to it, so the late Float inwards keeps `p` above the test: it puts a binding that more than one drop point uses above all of them ([FloatIn.hs, lines 740-742][float-in]). On 9.8.4, the only use of `p` at this point is in the loop, and Float inwards moves `p` into the `__DEFAULT` branch.
3. The final simplifier inlines the top-level `$j`. The use of `p` on the path `n <= 0` goes away, but its `let` stays above the test.

The output of the late Float inwards on HEAD (`-ddump-float-in`, the second of the two passes):

```
$j
  = \ ww ->
      case ww `cast` <Co:1> of nt { V ww ww ww ->
      case ww of wild { P ww -> (# ww, ww, ww #) }
      }

$wrow
  = \ ww ->
      let { p = P ww } in
      case <=# ww 0# of lwild {
        __DEFAULT ->
          join { $j unbx = $j ((V unbx 1# p) `cast` <Co:2>) } in
          joinrec {
            $wgo i ww
              = case i of i { I# ipv ->
                case >=# ipv ww of lwild {
                  __DEFAULT ->
                    case use p i of wild1 { I# y ->
                    jump $wgo (I# (+# ipv 1#)) (+# ww y)
                    };
                  1# -> jump $j ww
                }
                }; } in
          jump $wgo lvl 0#;
        1# -> $j ((V 0# 0# p) `cast` <Co:2>)
      }
```

The orthotope case that this reduces has the same three steps. There, `P` is the `PlainPtr` of the buffer of a Storable vector, and `use` is the `touch#` after each copy into the buffer.

[late-float]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Pipeline.hs#L271-276
[float-in]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/FloatIn.hs#L740-742
