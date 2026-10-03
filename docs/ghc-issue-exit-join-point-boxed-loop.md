# GHC issue: an exit join point in an imported unfolding takes the loop variables boxed, so the client's copy of the loop allocates a box an element

Filed as GHC [#27893](https://gitlab.haskell.org/ghc/ghc/-/work_items/27893) on 2026-10-03; the text from "## Summary" down is the filed body, in the tracker's bug template. Title: **An exit join point in an imported unfolding keeps the client's copy of a loop boxed: Exitify abstracts it over the boxed loop variables, in the client the exit is lazy in them, and `isExitJoinId` keeps it out of the loop**. Verified on 2026-10-03 on HEAD 10.1.20260803 (master at `d415f38a75`), 9.14.1, 9.12.4, 9.10.3, 9.8.4 and 9.6.7. Found in orthotope's unreleased branch `pr-mikolaj-toVectorListT`: with no pragma on its strided fill `genericFillStrided`, `-fexpose-overloaded-unfoldings` in its module and a client built `-fspecialise-aggressively`, the client's specialisations of the fill allocated two `I#` a two-element iteration and ran 1.5 to 2.9 times slower than with the fill `INLINE`, and `-fno-exitification` in the fill's module brought the allocation back to the `INLINE` fill's; the reproducer is the fill's innermost loop, cut down. The tracker was searched on 2026-10-03 for `exitification`, `exit join point`, `boxity`, `reboxing`, `-fno-exitification`, `expose-overloaded-unfoldings`, `late-specialise` and `Do not inline exit join points`, with no duplicate found; GHC [#21148](https://gitlab.haskell.org/ghc/ghc/-/work_items/21148) and GHC [#25982](https://gitlab.haskell.org/ghc/ghc/-/work_items/25982) are the nearest.

## Summary

In the reproducer below, built with plain `-O` on HEAD, `Repro` allocates 16 bytes for each element its loop copies, 160 MB in all, and 0.24 MB when `Lib` is built with `-fno-exitification`. `Repro` inlines `Lib`'s worker `$wcopyStrided`, the optimised code of the overloaded `copyStrided`, at its instance, and the copy of the loop it gets, `go1`, passes both loop variables boxed (HEAD, `-ddump-simpl -dsuppress-all -dsuppress-uniques`, the loop of `main` that calls `copyStrided`):

```
joinrec {
  go x s1
    = join {
        exit eta1 o ipv1 src
          = join {
              $j1 ipv2
                = case x of wild {
                    __DEFAULT -> jump go (+# wild 1#) ipv2;
                    10000# -> jump $j ipv2
                  } } in
            case >=# ipv1 999# of {
              __DEFAULT ->
                case a of { Ptr a1 ->
                case src of { I# i ->
                case readIntOffAddr# a1 i eta1 of { (# ipv2, ipv3 #) ->
                case b of { Ptr a2 ->
                case o of { I# i1 ->
                case writeIntOffAddr# a2 i1 ipv3 ipv2 of s2 { __DEFAULT ->
                jump $j1 s2
                }
                }
                }
                }
                }
                };
              1# -> jump $j1 eta1
            } } in
      joinrec {
        go1 o src eta1
          = case o of o1 { I# ipv1 ->
            case src of src1 { I# ipv2 ->
            case >=# (+# ipv1 1#) 999# of {
              __DEFAULT ->
                case a of { Ptr a1 ->
                case readIntOffAddr# a1 ipv2 eta1 of { (# ipv3, ipv4 #) ->
                case b of { Ptr a2 ->
                case writeIntOffAddr# a2 ipv1 ipv4 ipv3 of s2 { __DEFAULT ->
                let { s3 = +# ipv2 2# } in
                case readIntOffAddr# a1 s3 s2 of { (# ipv5, ipv6 #) ->
                case writeIntOffAddr# a2 (+# ipv1 1#) ipv6 ipv5 of s4
                { __DEFAULT ->
                jump go1 (I# (+# ipv1 2#)) (I# (+# s3 2#)) s4
                }
                }
                }
                }
                }
                };
              1# -> jump exit eta1 o1 ipv1 src1
            }
            }
            }; } in
      jump go1 copyStrided2 copyStrided2 s1; } in
jump go 1# ipv } in
```

`exit` is the exit join point that Exitify made in `Lib`, where `copyStrided`'s worker has the same shape with the class methods unknown. Exitify abstracts the exit over its free variables ([Note [Picking arguments to abstract over]][picking]), and these include the case binders `o1` and `src1` of the loop's arguments, because the methods `rd` and `wr` take them boxed. In `Repro` the methods are known and unbox `o` and `src`, but in one branch of `exit` only, so `exit` is lazy in them, `Str=<L><ML><L><ML>`, and a lazy demand is recorded boxed ([Note [No lazy, Unboxed demands in demand signature]][nolazy]). `exit` is not inlined back into the loop: [`isExitJoinId`][isexit] takes any join point that occurs once inside a recursive group for an exit join point, whichever pass made it, and [`preInlineUnconditionally`][preinline] and [`simplLetUnfolding`][letunf] refuse to inline one ([Note [Do not inline exit join points]][donotinline]). So `go1` passes `o1` and `src1` to `exit`, a boxed use of each, and boxity analysis keeps `go1`'s arguments boxed, `Str=<1L><1L><L>`.

HEAD inlines `$wcopyStrided` since 3eaac1f2b5, "Make inlining a bit more eager for overloaded functions" (#26831): each method of the known dictionary applied to arguments now earns `unfoldingDictDiscount` and `unfoldingFunAppDiscount`, and the six such calls in `$wcopyStrided` together discount it by 540 where 9.14.1 discounts it by 180, so that `-dinline-check '$wcopyStrided'` gives an adjusted size of -123 against 237. The same happens when the client specialises the worker instead of inlining it, as with `-fspecialise-aggressively` (see Steps to reproduce).

It does not happen when the last element is written by a guard of its own, `| o + 1 == n = rd inp src >>= wr out o` followed by `| o >= n = return ()`, which is strict in `o` and `src`, nor when `copyStrided` and the instance are in one module, where the specialiser, which runs [before Exitify][pipeline], copies code that has no exit join point yet.

In orthotope's strided fill, whose innermost loop this is, the boxes cost 16 bytes an element and make the fill 1.5 to 2.9 times slower.

A possible fix, not tested: letting the client inline an imported exit join point before its demand analysis. caced757 ("Don't keep exit join points so much", reverted in 7eac2468 after #22922) kept exit join points from inlining only in the simplifier run right after Exitification; #27885 suggests recognising them by a mark that Exitify sets rather than by occurrence.

### Related

- #21148: an exit join point inhibiting CPR of a result, in one module. It was closed as fixed by caced757, which had been reverted in 7eac2468, together with its test `T21148`; that test's expectation fails on HEAD.
- #25982: one boxed use on a loop's exit path keeps the loop's argument boxed.
- #27885: its second route is `isExitJoinId` recognising exit join points by occurrence information.
- #18837: an exit join point hides a constructor from SpecConstr.

## Steps to reproduce

```haskell
{-# LANGUAGE BangPatterns #-}
module Lib (Store (..), copyStrided) where

class Store f where
  rd :: f -> Int -> IO Int
  wr :: f -> Int -> Int -> IO ()

-- out[o] = inp[o * t] for 0 <= o < n, unrolled by two.
copyStrided :: Store f => f -> f -> Int -> Int -> IO ()
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

Save the modules as `Lib.hs` and `Repro.hs`. On HEAD:

```
ghc -O -fforce-recomp Repro.hs -o Repro && ./Repro +RTS -s
ghc -O -fforce-recomp -fno-exitification Repro.hs -o Repro && ./Repro +RTS -s
```

The first allocates 159,921,808 bytes and the second 241,808. `-ddump-simpl -dsuppress-all -dsuppress-uniques` shows the Core above, and `-ddump-dmdanal` the two signatures.

On 9.12.4 and 9.14.1, plain `-O` does not inline the worker: `Repro` calls the overloaded worker instead, 479 MB with or without `-fno-exitification`. On the releases the issue needs the client to specialise or inline the worker. Adding `-fspecialise-aggressively` to both commands specialises it:

| compiler | bytes allocated | with `-fno-exitification` |
|---|---|---|
| 9.14.1 | 159,922,296 | 242,296 |
| 9.12.4 | 159,922,336 | 242,336 |
| 9.10.3 | 159,922,336 | 242,336 |
| 9.8.4 | 159,922,336 | 242,336 |
| 9.6.7 | 159,922,448 | 242,448 |

Compiling separately with the inlining threshold on `Repro` alone inlines it and gives 160 MB, and 0.24 MB with `-fno-exitification` on `Lib.hs`:

```
ghc -O -c Lib.hs && ghc -O -funfolding-use-threshold=2000 -c Repro.hs && ghc Lib.o Repro.o -o Repro && ./Repro +RTS -s
```

With the threshold on `Lib` too, `Lib` exposes the unfolding of the unsplit `copyStrided`, made before Exitify, and the loop is unboxed.

## Workarounds

Each of these brings `Repro` from 160 MB to 0.24 MB, on HEAD with plain `-O` and on 9.12.4 and 9.14.1 with `-fspecialise-aggressively`. In `Lib`:

- `{-# OPTIONS_GHC -fno-exitification #-}`, at the cost of exitification in the whole module.
- `{-# INLINABLE copyStrided #-}`: the client specialises the unfolding taken before optimisation, and needs no `-fspecialise-aggressively` to do it. `{-# INLINE copyStrided #-}` works too.
- The last element written by a guard of its own, tested before the two-element step and strict in `o` and `src`, as in the summary.
- The last element written without the loop variables:

```haskell
      | o + 1 >= n = if o >= n then return () else rd inp ((n - 1) * t) >>= wr out (n - 1)
```

- The loop variables `Int#`, boxed only where `rd` and `wr` take them, with `MagicHash` on and `import GHC.Exts (Int (I#), Int#, isTrue#, (+#), (>=#))`:

```haskell
copyStrided inp out (I# n) (I# t) = go 0# 0#
  where
    go :: Int# -> Int# -> IO ()
    go o src
      | isTrue# (o +# 1# >=# n) =
          if isTrue# (o >=# n) then return () else rd inp (I# src) >>= wr out (I# o)
      | otherwise = do
          rd inp (I# src) >>= wr out (I# o)
          let s2 = src +# t
          rd inp (I# s2) >>= wr out (I# (o +# 1#))
          go (o +# 2#) (s2 +# t)
```

All but `INLINABLE` and `INLINE` leave `copyStrided` without a pragma, so on 9.12.4 and 9.14.1 they apply only where the client specialises or inlines the worker: with plain `-O`, `Repro` there calls the overloaded worker, 479 MB with them or without.

In `Repro`:

- `-fspec-constr`, which `-O2` turns on: SpecConstr specialises `go` on its `I#` arguments and `exit` along with it, and the loop takes `Int#`s.

Not workarounds: the guards in the other order, the two-element step tested first, `| o + 1 < n = do ...` then `| o < n = rd inp src >>= wr out o` then `| otherwise = return ()`, leave 160 MB, Exitify making the last element and the return one exit again, lazy in `o` and `src`; `-fno-exitification` on `Repro` alone leaves 160 MB, the exit join point arriving with `Lib`'s unfolding; and a `{-# SPECIALISE copyStrided :: P -> P -> Int -> Int -> IO () #-}` in `Repro`, without `-fspecialise-aggressively`, gives 479 MB on 9.12.4 and 9.14.1 and 160 MB on HEAD.

## Expected behavior

The loop takes `Int#` arguments and allocates nothing per element, as with `-fno-exitification`.

## Environment

* GHC version used: HEAD 10.1.20260803 (commit d415f38a75), 9.14.1, 9.12.4, 9.10.3, 9.8.4, 9.6.7

Optional:

* System Architecture: x86_64 Linux

[picking]: https://gitlab.haskell.org/ghc/ghc/-/blob/5236634abce50db7e8e7ecf375def90bf45d2476/compiler/GHC/Core/Opt/Exitify.hs#L490
[nolazy]: https://gitlab.haskell.org/ghc/ghc/-/blob/5236634abce50db7e8e7ecf375def90bf45d2476/compiler/GHC/Core/Opt/DmdAnal.hs#L1796
[isexit]: https://gitlab.haskell.org/ghc/ghc/-/blob/5236634abce50db7e8e7ecf375def90bf45d2476/compiler/GHC/Core/Opt/Simplify/Utils.hs#L3051-3056
[preinline]: https://gitlab.haskell.org/ghc/ghc/-/blob/5236634abce50db7e8e7ecf375def90bf45d2476/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1658
[letunf]: https://gitlab.haskell.org/ghc/ghc/-/blob/5236634abce50db7e8e7ecf375def90bf45d2476/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4831-4833
[donotinline]: https://gitlab.haskell.org/ghc/ghc/-/blob/5236634abce50db7e8e7ecf375def90bf45d2476/compiler/GHC/Core/Opt/Exitify.hs#L421
[pipeline]: https://gitlab.haskell.org/ghc/ghc/-/blob/5236634abce50db7e8e7ecf375def90bf45d2476/compiler/GHC/Core/Opt/Pipeline.hs#L206-263

/label ~"T::bug"
/label ~"needs triage"
