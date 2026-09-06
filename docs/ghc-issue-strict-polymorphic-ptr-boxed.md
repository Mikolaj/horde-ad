# GHC issue: a strict let-bound `plusPtr` result is boxed and unboxed on every iteration since 9.14

Filed as [GHC work item 27778](https://gitlab.haskell.org/ghc/ghc/-/work_items/27778); this file stays as the filed record, the text from "## Summary" down being the filed body. Title: **Simplifier: a bang-bound `plusPtr` result that let-generalises to `forall b. Ptr b` is allocated and taken apart again on every loop iteration; 9.12 allocates nothing**. The prose is ASD-STE100 Simplified Technical English. The reproducer needs only `ghc` and `base`. The defect was found on the GHC HEAD half of Run 26 of the orthotope micro-benchmark, on the unmerged `speedup-strided-tovector` branch, which is not public: the two pointer-walking fills allocated 1.41x and 2.61x their result vector on HEAD and 1.00x on 9.12.4. A workaround is known and is in the body, so the priority the ticket gets does not matter. It is not a duplicate of GHC #26548, though the two share an ingredient: that issue's discussion names !9874, the strict-worker change of 9.14, as what exposed its stale fast path, and the field-kind experiment in the body points at the same change here. The defects differ, #26548 being a missed evaluatedness mark on the fields of a constructor alternative and this one a case on a type lambda that the simplifier no longer removes, and the fix drafted for #26548, !15037, touches nothing on this path.

## Summary

A strict local binding of a `plusPtr` result has the type `forall b. Ptr b` when let-generalisation is on. From 9.14.1, the simplifier keeps the `case` on that type lambda. The STG then allocates a `Ptr` constructor and takes it apart at once, on every execution of the binding. 9.10.3 and 9.12.4 emit no allocation for the same module.

The program in "Steps to reproduce" copies runs of doubles through two raw pointers. Its inner loop's end pointer is `let !pEnd = op `plusPtr` sBytes`. These are the bytes allocated for one run of the program, `-O1`:

| compiler | bytes allocated |
|---|---|
| 9.10.3 | 97,672 |
| 9.12.4 | 97,592 |
| 9.14.1 | 411,297,552 |
| HEAD 10.1.20260803, `-XGHC2021` | 411,297,104 |

The difference is one 16-byte `Ptr` closure for each run copied. The STG of the 9.14.1 build shows it, at both call sites of the run copy:

```
case plusAddr# [ww3 sBytes] of sat { __DEFAULT -> Ptr [sat]; } of pEnd
{ __DEFAULT -> case pEnd of wild1 { Ptr b1 -> ...ltAddr# p b1... } }
```

The Core after the first simplifier pass already has this shape on 9.14.1, and 9.12.4 has `let { pEnd = plusAddr# ww3 sBytes }` at the same point. Both compilers desugar the binding to the same Core: `case \ @b -> plusPtr op sBytes of pEnd { __DEFAULT -> ... }`.

The trigger is the generalisation. Each of these removes the allocation on 9.14.1: a type annotation on the binding, `let !pEnd = op `plusPtr` sBytes :: Ptr Double`; or `-XMonoLocalBinds`; or `-XGHC2024`. HEAD shows the defect with `-XGHC2021` or `-XNoMonoLocalBinds` and not with its default language. `-O2` and `-fspec-constr` do not change the result.

The kind of the constructor's field decides. The same program with the end pointer wrapped in a data type of my own, `data P a = P FIELD`, built from the address by a function of type `Ptr a -> Int -> P b`, gives on 9.14.1:

| field | bytes allocated, 9.12.4 | bytes allocated, 9.14.1 |
|---|---|---|
| `Addr#` | 97,592 | 411,297,552 |
| `Int` | 97,592 | 97,552 |
| `!Int` | 97,592 | 411,297,552 |

So a lazy lifted field is fine and a strict or an unlifted field is boxed on every run. That is the distinction `Note [Strict fields in Core]` draws since !9874 (#20749), which is in 9.14 and not in 9.12: decomposing a constructor application with a strict or unlifted field first inserts an evaluation of the argument, and here the argument is under a type lambda.

## Steps to reproduce

1. Save the program below as `Repro.hs`.

2. Compile and run it with each compiler:

```
ghc -O1 -rtsopts -XGHC2021 Repro.hs -o Repro
./Repro +RTS -s 2>&1 | grep 'bytes allocated'
```

3. 9.12.4 prints about 98 KB. 9.14.1 prints about 411 MB.

4. To see the allocation, add `-ddump-stg-final -dsuppress-all` and look for `Ptr [` in the output. 9.12.4 emits none; 9.14.1 emits two, one for each call site of `writeRun`.

```haskell
-- Reproducer: a strict let-bound plusPtr result is boxed on every run.
-- Base only.
--
-- Build:  ghc -O1 -rtsopts -XGHC2021 Repro.hs -o Repro
-- Run:    ./Repro +RTS -s
--
-- pEnd has the type forall b. Ptr b.  Give it the type Ptr Double, or
-- compile with -XMonoLocalBinds, and 9.14.1 allocates nothing.
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import Foreign.Marshal.Alloc (mallocBytes)
import Foreign.Ptr (Ptr, plusPtr)
import Foreign.Storable (peek, poke)

-- Copies nRuns runs of sInner doubles, the source runs stride apart.
{-# NOINLINE fill #-}
fill :: Int -> Int -> Int -> Ptr Double -> Ptr Double -> IO ()
fill nRuns sInner stride obase base = do
  let !sBytes = sInner * 8
      !stB = stride * 8
      writeRun !op !bp =
        let !pEnd = op `plusPtr` sBytes
            inner !p !q
              | p >= pEnd = return ()
              | otherwise = do
                  x <- peek q
                  poke p (x :: Double)
                  inner (p `plusPtr` 8) (q `plusPtr` 8)
        in inner op bp
      run !k !p !q
        | k <= 0 = return p
        | otherwise = writeRun p q
                      >> run (k - 1) (p `plusPtr` sBytes) (q `plusPtr` stB)
  _ <- run nRuns obase base
  writeRun obase base

main :: IO ()
main = do
  let n = 1024 :: Int
  a <- mallocBytes (8 * n)
  b <- mallocBytes (8 * n)
  poke (b :: Ptr Double) 1.5
  let loop :: Int -> IO ()
      loop 0 = return ()
      loop i = fill (n `div` 4) 4 4 a b >> loop (i - 1)
  loop 100000
  x <- peek (a :: Ptr Double)
  print x
```

## Expected behavior

The code that 9.12.4 emits: the end pointer is an `Addr#` in a register, and the loop allocates nothing.

## Environment

* GHC version used: 9.14.1 and HEAD 10.1.20260803 (commit d415f38a75) show the defect; 9.10.3 and 9.12.4 do not.

Optional:

* Operating System: Linux (kernel 7.0.0-30-generic)
* System Architecture: x86_64 (AMD Ryzen 7 5800X, Zen 3)

/label ~"T::bug"
/label ~"needs triage"
