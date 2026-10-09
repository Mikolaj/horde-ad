# vector issue: `DoNotUnboxLazy`'s `elemseq` forces an element that `fromList` stores unevaluated

Filed 2026-10-09 as [vector issue 575][575]; this file stays as the filed record, the text from "## Summary" down being the filed body. Title: **The `elemseq` of `DoNotUnboxLazy` is `seq`, so `singleton`, `replicate`, `cons`, `snoc` and `constructN` force an element that `fromList` stores unevaluated**. The prose is ASD-STE100 Simplified Technical English. The reproducer is a cabal script and needs only `vector`. The problem was found while reviewing orthotope's `pr-mikolaj-toVectorListT` branch: orthotope's strided fill reads a broadcast element once, forces it with `elemseq` and then stores it many times, and at `DoNotUnboxLazy` that forced an element which orthotope's other copies leave unevaluated; orthotope keeps the call, with a comment that names this problem. A search of the vector issues and pull requests for `DoNotUnboxLazy`, `DoNotUnbox` and `elemseq` found [#503][503], the request for these newtypes, [#508][508], the pull request that added them, [#520][520], about their missing `Generic` instances, and [#518][518], about Unboxed instances for Storable vectors; none of them is about this problem. A workaround is known and is in the body.

## Summary

`Data.Vector.Unboxed` stores a `DoNotUnboxLazy` element in a boxed `Data.Vector`, and a write into that vector does not evaluate the element. The documentation of `DoNotUnboxLazy` says that the newtype "does not alter the strictness semantics of the underlying type". But its `G.Vector` instance in `Data.Vector.Unboxed.Base` defines `elemseq _ = seq` ([lines 842-855][base]). The documentation of `elemseq` in `Data.Vector.Generic.Base` says that it evaluates the element "as far as storing it in a vector would" ([lines 140-152][doc]).

`singleton`, `replicate`, `cons`, `snoc`, `constructN` and `constructrN` call `elemseq` before they store an element (see [`singleton`][singleton]). Because of this, they evaluate a `DoNotUnboxLazy` element to weak head normal form. `fromList` and `generate` do not call `elemseq`, and they store the same element unevaluated. A tuple gives `elemseq` to each component, so a `DoNotUnboxLazy` component of a tuple is also evaluated. The boxed `Data.Vector` keeps the default `elemseq`, which does not evaluate the element.

The table gives the result of the program in "Steps to reproduce" for the element `e = DoNotUnboxLazy undefined`.

| Function | Element evaluated |
|---|---|
| `fromList [e]`, `generate 1 (const e)` | no |
| `singleton e`, `replicate 3 e`, `cons e empty`, `snoc empty e`, `constructN 1 (const e)` | yes |
| `singleton (0, e)` | yes |
| `Data.Vector`: `singleton undefined`, `cons undefined empty` | no |

## Proposed fix

Remove `elemseq _ = seq` from the `G.Vector` instance of `DoNotUnboxLazy`. Then the class default, `elemseq _ = \_ x -> x`, applies, as for `Data.Vector`. On master at [d0f42e0562][master], the instance is in `Data.Vector.Unboxed.Unsafe` ([lines 882-895][unsafe]) and has the same code.

The two other newtypes do not need a change. `DoNotUnboxStrict` stores its elements through `Data.Vector.Strict`, whose write evaluates the element to weak head normal form, as its `elemseq _ = seq` does. `DoNotUnboxNormalForm` stores `force x`, and its `elemseq` uses `rnf`.

Until vector has a fix, use `fromList` or `generate`, not `singleton` or `replicate`, to keep the element unevaluated.

## Steps to reproduce

1. Save the program below as `Repro.hs`.

2. Run it. To select a compiler, add `-w ghc-VERSION`. For GHC HEAD, whose `base` is newer than vector-0.13.2.0 permits, I also added `--allow-newer=base,ghc-prim,ghc-bignum,template-haskell,containers`.

```
cabal run -v0 Repro.hs
```

3. On GHC HEAD 10.1.20260918, the output is below. With `ghc-options: -O0` in the script header, the output is the same.

```
Data.Vector.Unboxed, DoNotUnboxLazy undefined:
  fromList [e]          : element not forced
  generate 1 (const e)  : element not forced
  singleton e           : element forced
  replicate 3 e         : element forced
  cons e empty          : element forced
  snoc empty e          : element forced
  constructN 1 (const e): element forced
  singleton (0, e)      : element forced
Data.Vector, undefined:
  singleton undefined   : element not forced
  cons undefined empty  : element not forced
```

```haskell
{- cabal:
build-depends: base, vector ==0.13.2.0
-}
-- Reproducer: DoNotUnboxLazy's elemseq forces the element, so singleton,
-- replicate, cons, snoc and constructN force an element that fromList
-- and generate store unevaluated.  The boxed Data.Vector is the control.
--
-- Run: cabal run -v0 Repro.hs
{-# LANGUAGE ScopedTypeVariables #-}
module Main (main) where

import Control.Exception (ErrorCall, evaluate, try)
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as VU

e :: VU.DoNotUnboxLazy Int
e = VU.DoNotUnboxLazy undefined

check :: String -> Int -> IO ()
check name n = do
  r <- try (evaluate n)
  putStrLn $ name ++ ": " ++ case r of
    Left (_ :: ErrorCall) -> "element forced"
    Right _ -> "element not forced"

main :: IO ()
main = do
  putStrLn "Data.Vector.Unboxed, DoNotUnboxLazy undefined:"
  check "  fromList [e]          " $ VU.length (VU.fromList [e])
  check "  generate 1 (const e)  " $ VU.length (VU.generate 1 (const e))
  check "  singleton e           " $ VU.length (VU.singleton e)
  check "  replicate 3 e         " $ VU.length (VU.replicate 3 e)
  check "  cons e empty          " $ VU.length (VU.cons e VU.empty)
  check "  snoc empty e          " $ VU.length (VU.snoc VU.empty e)
  check "  constructN 1 (const e)" $ VU.length (VU.constructN 1 (const e))
  check "  singleton (0, e)      " $ VU.length (VU.singleton (0 :: Int, e))
  putStrLn "Data.Vector, undefined:"
  check "  singleton undefined   " $ V.length (V.singleton (undefined :: Int))
  check "  cons undefined empty  " $ V.length (V.cons (undefined :: Int) V.empty)
```

## Expected behavior

`singleton`, `replicate`, `cons`, `snoc` and `constructN` store a `DoNotUnboxLazy` element as `fromList` does, and do not evaluate it.

## Environment

* vector-0.13.2.0, from Hackage. On master at [d0f42e0562][master], the instance has the same code, in `Data.Vector.Unboxed.Unsafe`.
* GHC HEAD 10.1.20260918 (commit 6913545fd3); cabal-install 3.18.1.0.
* Linux (kernel 7.0.0-34-generic), x86_64 (AMD Ryzen 7 5800X).

[575]: https://github.com/haskell/vector/issues/575
[503]: https://github.com/haskell/vector/issues/503
[508]: https://github.com/haskell/vector/pull/508
[518]: https://github.com/haskell/vector/pull/518
[520]: https://github.com/haskell/vector/issues/520
[base]: https://github.com/haskell/vector/blob/d9d0d46623fdecce7652f59caa4a28849292a0e7/vector/src/Data/Vector/Unboxed/Base.hs#L842-L855
[doc]: https://github.com/haskell/vector/blob/d9d0d46623fdecce7652f59caa4a28849292a0e7/vector/src/Data/Vector/Generic/Base.hs#L140-L152
[singleton]: https://github.com/haskell/vector/blob/d9d0d46623fdecce7652f59caa4a28849292a0e7/vector/src/Data/Vector/Generic.hs#L537-L541
[unsafe]: https://github.com/haskell/vector/blob/d0f42e056202fa24b479833dbc21222c1964d096/vector/src/Data/Vector/Unboxed/Unsafe.hs#L882-L895
[master]: https://github.com/haskell/vector/tree/d0f42e056202fa24b479833dbc21222c1964d096
