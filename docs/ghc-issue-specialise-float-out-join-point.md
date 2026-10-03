# GHC issue: the specialisation of an imported INLINABLE function meets float-out before the client simplifies it, so a loop that would become a join point is floated out as a closure

Filed as GHC [#27894](https://gitlab.haskell.org/ghc/ghc/-/work_items/27894) on 2026-10-03; the text from "## Summary" down is the filed body, in the tracker's bug template. Title: **Float-out floats a would-be join point out of the specialisation of an imported INLINABLE function: the stable unfolding is not eta-expanded, and the specialiser's copy reaches float-out unsimplified**. Verified on 2026-10-03 on HEAD 10.1.20260803 (commit `d415f38a75`), 9.14.1, 9.12.4, 9.10.3, 9.8.4 and 9.6.7. Found in orthotope's unreleased branch `pr-mikolaj-toVectorListT`: with its strided fill `genericFillStrided` `INLINABLE` in place of `INLINE`, the client's specialisations of the fill allocated 64 to 72 bytes more a call, 56 to 64 for the floated loop's closure and 8 more in the closure that captures it, and ran up to 17% slower on small arrays; bounding the loop by an end computed from an argument of the enclosing function kept it a join point. The reproducer is the fill's odometer, cut down. The tracker was searched on 2026-10-03 for `full laziness join point`, `float out join point`, `specialise float out`, `stable unfolding eta`, `INLINABLE join point` and `potential join point`, with no duplicate found; GHC [#14287](https://gitlab.haskell.org/ghc/ghc/-/work_items/14287) is the nearest.

## Summary

In the reproducer below, `Repro` allocates 16 bytes a call of `fill` more than with `-fno-full-laziness`. The specialisation of `Lib`'s `INLINABLE` `fill` at `Repro`'s instance allocates the loop `$wgo` of the local `level` as a closure on every call, outside `$wrun`, which captures it (HEAD, `-ddump-simpl -dsuppress-all -dsuppress-uniques`):

```
$s$wfill
  = \ out n nest0 eta ->
      letrec {
        $wgo
          = \ ww ww1 ww2 eta1 ->
              case <=# ww 0# of {
                __DEFAULT ->
                  case out `cast` <Co:1> of { Ptr a ->
                  case writeIntOffAddr# a ww1 ww2 eta1 of s2 { __DEFAULT ->
                  $wgo (-# ww 1#) (+# ww1 1#) (+# ww2 1#) s2
                  }
                  };
                1# -> eta1
              }; } in
      letrec {
        $wrun
          = \ ds ww ww1 eta1 ->
              case ds of {
                Fused -> case n of { I# ww2 -> $wgo ww2 ww ww1 eta1 };
                Level bx bx1 inner ->
                  joinrec {
                    $wgo2 ww2 ww3 ww4 eta2
                      = case <=# ww2 0# of {
                          __DEFAULT ->
                            case $wrun inner ww3 ww4 eta2 of ww5 { __DEFAULT ->
                            jump $wgo2 (-# ww2 1#) (+# ww3 bx1) (+# ww4 1#) ww5
                            };
                          1# -> eta2
                        }; } in
                  jump $wgo2 bx ww ww1 eta1
              }; } in
      $wrun nest0 0# 0# eta
```

With `fill` and the instance in one module, the same `$wgo` is a join point of `$wrun`, as `$wgo2` is here.

`Lib` simplifies the `INLINABLE` unfolding with eta-expansion off ([`updModeForStableUnfoldings`][updmode], whose [Note [Eta expansion in stable unfoldings and rules]][etanote] calls the choice "a bit moot"). So in `Lib`'s interface `go` has three lambdas, the `State#` lambda sits under a `case`, its recursive call is under that lambda, and `go` is no join point (`--show-iface`, module prefixes and multiplicities dropped, lines joined):

```
go :: Int -> Int -> Int -> IO ()
  NotJoinPoint [Arity: 4]
= \ (k :: Int) (op :: Int) (b2 :: Int) ->
  case k of k1 { I# ipv2 ->
  case op of op1 { I# ipv3 ->
  case b2 of b3 { I# ipv4 ->
  case leInt k1 (I# 0#) of wild1 {
    False
    -> (\ (s :: State# RealWorld) ->
        case (body op1 b3) `cast` (N:IO <()>_R) s of ds1 { (#,#) ipv5 ipv6 ->
        (go (I# (-# ipv2 1#)) (I# (+# ipv3 1#)) (I# (+# ipv4 1#)))
          `cast` (N:IO <()>_R) ipv5 })
         `cast` (Sym (N:IO <()>_R))
    True
    -> (\ (s :: State# RealWorld) -> (# s, () #)) `cast` (Sym (N:IO <()>_R)) } } } }
```

`Repro`'s specialiser copies that unfolding, and the copy goes to the first float-out with no simplifier run in between: [`CoreDoSpecialising` is followed by `CoreDoFloatOutwards`][pipeline]. There `go` and the `body` it calls depend on nothing that `run` binds, so both are floated out of `run`, and nothing later moves `go` back. When `fill` is specialised in its own module, the [gentle simplifier][gentle] runs before the specialiser, with eta-expansion on, and `go` leaves it a join point.

In orthotope's strided fill, the floated loop's closure costs 56 to 64 bytes a call and the closure that captures it 8 more, and small arrays run up to 17% slower.

A possible fix, not tested: eta-expanding inside stable unfoldings, or simplifying the specialiser's new bindings before the first float-out.

### Related

- #14287: float-out makes a would-be join point a top-level function before the simplifier marks it ("we need a run of the Simplifier to mark it as such"), there after early inlining.
- #13104: a partial application under `runRW#` keeps a loop from being a join point.

## Steps to reproduce

```haskell
{-# LANGUAGE BangPatterns #-}
module Lib (Store (..), Nest (..), fill) where

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
          go !k !op !b
            | k <= 0    = return ()
            | otherwise = body op b >> go (k - 1) (op + blk) (b + 1)
      in  go cnt outPos base
    {-# INLINE level #-}
    run :: Nest -> Int -> Int -> IO ()
    run Fused !o !b = level (wr out) n 1 o b
    run (Level cnt blk inner) !o !b = level (run inner) cnt blk o b
{-# INLINABLE fill #-}
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

Save the modules as `Lib.hs` and `Repro.hs`:

```
ghc -O -fforce-recomp Repro.hs -o Repro && ./Repro +RTS -s
ghc -O -fforce-recomp -fno-full-laziness Repro.hs -o Repro && ./Repro +RTS -s
```

| compiler | bytes allocated | with `-fno-full-laziness` |
|---|---|---|
| HEAD 10.1.20260803 | 7,252,176 | 5,652,192 |
| 9.14.1 | 7,252,664 | 5,652,680 |
| 9.12.4 | 7,252,704 | 5,652,720 |
| 9.10.3 | 7,252,704 | 5,652,720 |
| 9.8.4 | 7,252,704 | 5,652,720 |
| 9.6.7 | 7,252,816 | 5,652,832 |

`-ddump-simpl -dsuppress-all -dsuppress-uniques` shows the Core above, and `ghc --show-iface Lib.hi` the unfolding of `go`.

## Workarounds

Measured on 9.12.4, 9.14.1 and HEAD alike, against 7.25 MB. In `Repro`:

- `-fno-full-laziness`, on `Repro` alone: 5.65 MB, at the cost of full laziness in the whole module. In orthotope's fill it left another local function, which full laziness otherwise floats to the top level, allocated as a closure inside the specialisation, 16 bytes a call.
- `-fliberate-case`, which `-O2` turns on: 5.65 MB. LiberateCase copies the floated loop back into `$wrun`, where it is a join point.
- `-fstg-lift-lams`, which `-O2` turns on: 3.25 MB, as with `fill` `INLINE`. `$wgo` stays floated in the Core, but the STG lambda lifter lifts it and `$wrun` to the top level, so neither is allocated as a closure.
- `-O2`: 3.25 MB.

In `Lib`:

- `go` bounded by an end computed from `outPos`, which `run` binds, so that `go` cannot float out of `run`: 5.65 MB.

```haskell
    level body cnt blk !outPos !base =
      let !opEnd = outPos + cnt * blk
          go :: Int -> Int -> IO ()
          go !op !b
            | op >= opEnd = return ()
            | otherwise = body op b >> go (op + blk) (b + 1)
      in  go outPos base
```

- `go` mentioning a field that `run` takes apart, as the innermost level's step held in `Fused`, with `Repro` passing `(Fused 1)`: 5.65 MB.

```haskell
data Nest = Fused !Int | Level !Int !Int Nest
...
    run (Fused blk) !o !b = level (wr out) n blk o b
```

- `{-# INLINE fill #-}` in place of `INLINABLE`: 3.25 MB, with `fill` inlined at each call.
- No pragma on `fill`, `-fexpose-overloaded-unfoldings` on `Lib` and `-fspecialise-aggressively` on `Repro`: 5.65 MB. The client then specialises the optimised unfolding, where `go` is a join point already, but an optimised unfolding also carries `Lib`'s exit join points into the client, and one whose exit path takes the loop variables boxed keeps the specialised loop boxed (#27893).

Not workarounds: `outPos` mentioned in `go`'s base case, ``| k <= 0 = outPos `seq` return ()``, leaves 7.25 MB, and ``lazy outPos `seq` return ()`` in its place keeps `go` in `run` but gives 12.85 MB; a `{-# SPECIALISE fill :: P -> Int -> Nest -> IO () #-}` in `Repro` leaves 7.25 MB; and writing `go` with its `State#` lambda explicit, `go !k !op !b = IO $ \s -> ...`, leaves 7.25 MB, and gives 137 MB with the arguments evaluated inside the lambda instead.

## Expected behavior

`$wgo` stays a join point of `$wrun`, as when `fill` is specialised in its own module, and `Repro` allocates as it does with `-fno-full-laziness`.

## Environment

* GHC version used: HEAD 10.1.20260803 (commit d415f38a75), 9.14.1, 9.12.4, 9.10.3, 9.8.4, 9.6.7

Optional:

* System Architecture: x86_64 Linux

[updmode]: https://gitlab.haskell.org/ghc/ghc/-/blob/5236634abce50db7e8e7ecf375def90bf45d2476/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1195-1204
[etanote]: https://gitlab.haskell.org/ghc/ghc/-/blob/5236634abce50db7e8e7ecf375def90bf45d2476/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1297-1301
[pipeline]: https://gitlab.haskell.org/ghc/ghc/-/blob/5236634abce50db7e8e7ecf375def90bf45d2476/compiler/GHC/Core/Opt/Pipeline.hs#L206-214
[gentle]: https://gitlab.haskell.org/ghc/ghc/-/blob/5236634abce50db7e8e7ecf375def90bf45d2476/compiler/GHC/Core/Opt/Pipeline.hs#L200-202

/label ~"T::bug"
/label ~"needs triage"
