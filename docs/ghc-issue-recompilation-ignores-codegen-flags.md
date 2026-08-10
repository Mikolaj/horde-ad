# GHC issue: recompilation checking ignores settings that carry a value

Not filed. This file is the draft, the text from "## Summary" down being the body to file. Title: **Recompilation checking ignores every setting that carries a value: `-fllvm`, the inliner thresholds, `-fproc-alignment` and the `-pgm*` and `-opt*` families are all missed**. The prose is ASD-STE100 Simplified Technical English. The tracker was not searched for duplicates, because the machine that found this has no network access; do this before you file. The case that found the defect is a cache-line alignment measurement in the orthotope micro-benchmark, on the unmerged `speedup-strided-tovector` branch, which is not public; the filed body is self-contained.

## Summary

GHC does not recompile a module when only some code generation settings change. It keeps the objects of the previous build and links them. It gives no message and the exit status is zero. Thus the build is successful, and the binary does not agree with the command line that made it.

The clearest example is the choice of backend. The command `ghc -O1 Repro.hs` and then the command `ghc -O1 -fllvm Repro.hs` keep the objects of the native code generator, thus the second command does not use the LLVM backend. The defect is symmetrical also: if the first build has the setting and the second build does not, GHC again does not recompile, and the binary keeps a property that the command line no longer requests.

These settings are missed. Each one was tested on GHC 9.10.3, 9.12.4, 9.14.1 and HEAD, and the result is the same on all four: no recompilation, and a different binary when `-fforce-recomp` is added.

| setting | function |
|---|---|
| `-fllvm` | selects the LLVM backend in place of the native code generator |
| `-funfolding-use-threshold=N` | the primary control of the inliner |
| `-funfolding-fun-discount=N` | a discount of the inliner |
| `-fmax-worker-args=N` | the limit of the worker/wrapper transformation |
| `-fdmd-unbox-width=N` | the unboxing decision of demand analysis |
| `-fproc-alignment=N` | the alignment of functions; the setting that found the defect |
| `-pgma <program>` | replaces the assembler |
| `-optlo <option>`, `-optlc <option>` | options for the `opt` and `llc` programs of LLVM |

The list is not complete. It contains the settings that one small test module can show. For a setting whose effect the module does not use, the binary is the same with `-fforce-recomp`, and the test gives no result. `-fspec-constr-count`, `-fliberate-case-threshold`, `-msse4.2`, `-mavx` and `-optc` are in this condition. The cause below applies to them also.

The cause is one design decision, and not an omission of one setting. Recompilation checking makes its fingerprint from sets of boolean flags. In the module GHC.Iface.Recomp.Flags, `fingerprintOptFlags` uses the members of `optimisationFlags`, and `fingerprintDynFlags` uses the members of `codeGenFlags` and a fixed list of other fields. A setting that carries a value is not a member of a set of flags, thus it has no effect on the fingerprint. All the settings above carry a value. In GHC.Driver.DynFlags, `-fllvm` sets the field `backend`, the inliner thresholds set fields of `unfoldingOpts`, `-fmax-worker-args` sets `maxWorkerArgs`, `-fdmd-unbox-width` sets `dmdUnboxWidth`, and `-fproc-alignment` sets `cmmProcAlignment`. In GHC.Settings, `-pgma` sets `toolSettings_pgm_a`, and the tool settings have no fingerprint at all. The line numbers are not given, because they move; the names are sufficient to find each field.

The decision of GHC is visible with `-ddump-hi-diffs`. After a build without `-fllvm`, a build with `-fllvm` gives this:

```
Considering whether compilation is required for Main:
Module flags unchanged
Optimisation flags unchanged
HPC flags unchanged
```

The message is not only absent. It is incorrect: the module flags did change. A setting that GHC does compare gives a different message, and this is the control for all the tests below. With `-fspec-constr` in place of `-fllvm`, at `-O1`:

```
  Optimisation flags have changed 3066e399250ae88c095af34f24df8999 -> 1ac90d07bd23b604fcabaf10de5062a5
[1 of 2] Compiling Main             ( Repro.hs, Repro.o ) [Optimisation flags changed]
```

This defect is important because these are the settings that a user changes between two builds that are equal in all other respects. A user who compares two values of `-funfolding-use-threshold`, or the LLVM backend against the native code generator, measures one binary two times. The two measurements agree, the statistics are good, and the result is wrong. Nothing in the output of the build shows the condition.

The setting that found the defect shows the cost. The purpose of `-fproc-alignment` is the control of code layout, and its documentation says that `-fproc-alignment=64` "can be used to limit alignment impact on performance as each function will start at a cache line". Code layout is important: on a Zen 3 processor, a small loop that crosses a cache-line boundary is 1.58 times slower than the same loop in one line, and a separate report covers the absence of loop alignment itself. Six binaries were made to compare positions, and three of them had the setting. All six binaries were the same binary. This was found only by disassembly of the binaries, which showed equal offsets. A comparison of times would have given a result that looks correct.

Four corrections are possible. (1) Add the absent fields to `IfaceDynFlags`. The record has this shape already: its field `ifaceCodeGenDistinctConstructorTables` holds `distinctConstructorTables`, of type `StgDebugDctConfig`, which is a setting that carries a value. `backend` and `cmmProcAlignment` need the same treatment. (2) Add the tool settings and the tool options. The same function has `ifaceCppSig = opt_P_signature dflags`, thus the options of the preprocessor are in the fingerprint. The options of the assembler, of `opt` and of `llc` are not, and the programs from the `-pgm*` flags are not. (3) Make the fingerprint an opt-out list and not an opt-in list. If the fingerprint uses all of `DynFlags`, less the fields that are known to have no effect on the output, a new field is correct by default. Corrections (1) and (2) repair the known settings; correction (3) prevents the return of the defect. (4) A diagnosis aid, and not a correction: make `-ddump-hi-diffs` report which fields it compared. At present it says "Module flags unchanged" for a change of backend, and a user has no method to see which settings the comparison includes.

## Steps to reproduce

1. Save the program below as `Repro.hs`.
2. Compile the program: `ghc -O1 Repro.hs -o prog`. Record the checksum of `prog`.
3. Compile the program again with one setting from the table above: `ghc -O1 -fllvm Repro.hs -o prog`. GHC gives no message. The checksum does not change.
4. Compile the program again with the same setting and `-fforce-recomp`: `ghc -O1 -fllvm -fforce-recomp Repro.hs -o prog`. The checksum changes. Thus the setting does change the generated code, and step 3 did not use it.
5. Repeat steps 2 to 4 for the other settings in the table. For `-fllvm`, `-optlo` and `-optlc`, an installation of LLVM that GHC accepts is necessary.

There is no table of results for each compiler, because the results do not differ: each of the four compilers in the Environment section gives the same behavior for each setting in the table.

Read the recompilation from the message of GHC, and not from the checksum. GHC prints a `Compiling` line only when it recompiles. For the control `-fspec-constr` on 9.12.4, 9.14.1 and HEAD, GHC recompiles and makes an equal binary, because SpecConstr changes nothing in this module. A test that uses the checksum alone thus reports the control as a failure also. Use `-O1` for the control: at `-O2` SpecConstr is already active, and no recompilation is correct there.

```haskell
-- Reproducer for the recompilation defect.  Base only.
--
-- Build:  ghc -O1 Repro.hs -o prog
-- Then:   ghc -O1 <setting> Repro.hs -o prog                 -- no recompilation
--         ghc -O1 <setting> -fforce-recomp Repro.hs -o prog  -- a different binary
--
-- The module has an INLINE function, a strict accumulator loop and a strict
-- constructor that the worker/wrapper transformation can unbox.  This gives
-- the inliner, the simplifier and demand analysis work to do, so that a
-- setting which has any effect makes a different binary.  A smaller module
-- gives an equal binary for many settings, and the test then has no result.
{-# LANGUAGE BangPatterns #-}
module Main (main) where

step :: Int -> Int -> Int
step !a !b = a * 31 + b `quot` 7 + (a `rem` 13) * (b `rem` 11)
{-# INLINE step #-}

chain :: Int -> Int -> Int
chain !acc 0 = acc
chain !acc n = chain (step acc n) (n - 1)

data T = T !Int !Int

walk :: T -> Int -> T
walk t 0 = t
walk (T x y) n = walk (T (step x n) (y + x)) (n - 1)

main :: IO ()
main = do
  let T a b = walk (T 1 2) 500
  print (chain 0 1000 + a + b + sum (map (step 3) [1 .. 200 :: Int]))
```

## Expected behavior

The expected behavior is that GHC recompiles the module when a setting changes that changes the generated code. If GHC does not recompile for a class of settings, the expected behavior is that it gives a message, and that the documentation of the settings says so.

## Workarounds

Give `-fforce-recomp`, or remove the `.o` and the `.hi` file of each module, or give a different `--builddir` for each configuration under cabal. All three are easy when you know the defect, and none of them is discoverable from the symptom, which is a build that is successful. For a measurement that goes from one configuration to the other and back, the third is the best: each configuration keeps its own objects, thus a return to a configuration does not compile it again.

## Environment

* GHC version used: 9.10.3, 9.12.4, 9.14.1, and HEAD 10.1.20260803 (commit d415f38a75). All four show the same behavior.

Optional:

* Operating System: Linux (kernel 7.0.0-28-generic)
* System Architecture: x86_64 (AMD Ryzen 7 5800X, Zen 3, 32 MB last-level cache)
* Other tools: cabal-install 3.16.1.0, gcc 13.3.0 as the assembler, LLVM 18


/label ~"T::bug"
/label ~"needs triage"
