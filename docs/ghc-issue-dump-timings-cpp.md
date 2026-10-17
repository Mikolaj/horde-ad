# GHC issue: `-ddump-timings -ddump-to-file` keeps no compiler pass of a CPP module after a `--make` run that compiles nothing

Filed as GHC [#27978](https://gitlab.haskell.org/ghc/ghc/-/work_items/27978) on 2026-10-17; the text from "## Summary" down is the filed body, in the tracker's bug template. Title: **`-ddump-timings -ddump-to-file`: a `--make` run that compiles nothing leaves only the CPP step in the timings file of each CPP module**. Verified with GHC HEAD 10.1.20260918, 9.14.1, 9.12.4, 9.10.3 and 9.8.4, all with the same effect, from the files as shown here. The effect was first seen on modules that `#include` a file; `#include` does not matter, and any CPP module is affected. A tracker search of 2026-10-16 found no report; a search on 2026-10-17 of the issues filed since then found none. The cited lines were checked at master f93d523c. The prose is ASD-STE100 Simplified Technical English. Open, not tested: one-shot `-c` mode, the other dump flags, and a module with an `-F` preprocessor.

## Summary

With `-ddump-timings -ddump-to-file`, GHC writes the pass timings of a module `M` to `M.dump-timings`. A second `ghc --make` run that finds all modules up to date compiles nothing. But for each module with `{-# LANGUAGE CPP #-}`, this run still runs the C preprocessor, and it writes the time of that step to the module's timings file. That is the first write of the process to the file, so the file is truncated first. The file then has one line, and the timings of all compiler passes from the earlier run are gone. A module without CPP keeps its file.

Cabal builds an executable with two `ghc --make` runs: the first with `-no-link`, the second to link. The second run compiles nothing. Thus every CPP module of an executable loses its timings; we saw the same in a benchmark. In a library, which cabal builds with one run, the CPP modules keep them.

The cause, from the code at master:

1. `getPreprocessedImports` calls `preprocess` for each module in each `--make` run ([Driver/Downsweep.hs, lines 1837-1839][downsweep]).
2. `preprocess` sets the module's dump prefix ([Driver/Pipeline.hs, line 159][pipeline]), so the CPP timing goes to the module's own timings file.
3. `withDumpFileHandle` does `writeFile fileName ""` on the first write of a process to a dump file ([Utils/Logger.hs, lines 508-518][logger]).

## Steps to reproduce

```haskell
-- C.hs
{-# LANGUAGE CPP #-}
module C where
c :: Int
c = 1
```

```haskell
-- N.hs
module N where
n :: Int
n = 2
```

Run this command two times, and after each run count the lines with `wc -l out/C.dump-timings out/N.dump-timings`:

```
ghc --make -no-link -ddump-timings -ddump-to-file -outputdir out C.hs N.hs
```

### Results

Lines in `out/C.dump-timings` (C) and `out/N.dump-timings` (N):

```
GHC              after run 1    after run 2
                 C     N        C     N
HEAD             14    13        1    13
9.14.1           13    12        1    12
9.12.4           13    12        1    12
9.10.3           13    12        1    12
9.8.4            11    10        1    10
```

After run 2, on HEAD, `out/C.dump-timings` has only this line:

```
systool:hs-cpp: alloc=145912 time=0.350
```

## Expected behavior

A `--make` run that compiles nothing does not remove the timings of the earlier run. `out/C.dump-timings` keeps its compiler passes, as `out/N.dump-timings` does.

## Environment

* GHC version used: HEAD 10.1.20260918 (`wip/T27737` at 6913545fd3, on master e2d5702699, with local simplifier patches; none touches `GHC.Driver.Downsweep`, `GHC.Driver.Pipeline` or `GHC.Utils.Logger`), 9.14.1, 9.12.4, 9.10.3 and 9.8.4, all with the same effect.

Optional:

* Operating System: Linux
* System Architecture: x86_64

[downsweep]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Driver/Downsweep.hs#L1837-1839
[pipeline]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Driver/Pipeline.hs#L159
[logger]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Utils/Logger.hs#L508-518

/label ~"T::bug"
/label ~"driver"
/label ~"needs triage"
