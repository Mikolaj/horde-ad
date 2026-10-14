# GHC issue: the RTS without profiling runs the profiling-header code of eras profiling

Staged and filed 2026-10-14 as [GHC work item 27951](https://gitlab.haskell.org/ghc/ghc/-/work_items/27951); this file stays as the filed record, the text from "## Summary" down being the filed body. Title: **Non-profiling RTS runs `PROF_HEADER_CREATE` since 9.10: `setUserEra` crash, layout-dependent slowdown**. The prose is ASD-STE100 Simplified Technical English. The performance case was found in the specialisation benchmark of orthotope on GHC HEAD; the filed body is self-contained, and its reproducer shows the crash. The awareness sweep (2026-10-14, gitlab.haskell.org issues and merge requests, titles and descriptions only) found no report of either symptom. The related items, which the body names but for !12196, are GHC [#24332](https://gitlab.haskell.org/ghc/ghc/-/work_items/24332) and GHC [!11903](https://gitlab.haskell.org/ghc/ghc/-/merge_requests/11903), which added the code; GHC [!12196](https://gitlab.haskell.org/ghc/ghc/-/merge_requests/12196), which repaired an earlier regression from the same commit; and GHC [#27358](https://gitlab.haskell.org/ghc/ghc/-/work_items/27358), where a comment announces a proof of concept for eras without profiling, which bears on the correction; and GHC [#27907](https://gitlab.haskell.org/ghc/ghc/-/work_items/27907), whose code-layout measurements this hazard can disturb.

## Summary

Since GHC 9.10, which included !11903, the RTS without profiling executes the code of the Cmm macro `PROF_HEADER_CREATE`. This code reads the RTS variables `era` and `user_era`. If one of them is more than zero, the code writes a value into the third word of a closure. A profiled closure has its profiling header word there. A closure without profiling has no such word, thus the store writes into the payload of the closure, or past its end.

The code is in the update frames `stg_upd_frame` and `stg_marked_upd_frame`, and thus `stg_bh_upd_frame`, which jumps to the second, and in some primops, for example `atomicModifyMutVar2#` and `finalizeWeak#`. Thus the RTS executes the two loads and the two comparisons each time an update frame updates a thunk.

The cause is the commit b0293f78cb ("rts: eras profiling mode", !11903, for #24332), which is in 9.10.1. It changed the call sites of the macro `LDV_RECORD_CREATE` in the Cmm code of rts/Updates.h and rts/PrimOps.cmm to `PROF_HEADER_CREATE`. For a build without `PROFILING`, rts/include/rts/prof/LDV.h defines `LDV_RECORD_CREATE(c)` to nothing. There is no such definition of `PROF_HEADER_CREATE`. Thus the Cmm parser uses its built-in macro, the function `profHeaderCreate` in `GHC.StgToCmm.Prof`. That function emits the two checks and the stores with no `ifProfiling`. Other functions of that module that write profiling fields, for example `ldvEnter` and `enterCostCentreThunk`, put their code in `ifProfiling`.

The update frame of the RTS without profiling (the object `Updates.o` in `libHSrts-*.a`) shows the change. On 9.6.7 and 9.8.4, `stg_upd_frame_info` has no reference to `era` or `user_era`. On 9.10.3, 9.12.4, 9.14.1 and HEAD (10.1.20260918) it has four relocations against them. The last step below gives the command.

The first consequence is a crash. The function `setUserEra` of `GHC.Profiling.Eras`, in the package ghc-experimental, is a foreign import of the RTS function with the same name. Its documentation does not say that it is only for profiled programs. After `setUserEra 1` in a program without profiling, each update writes 1 into the third word of the updated closure. For a thunk, this word is the first payload word, which the update makes dead. But a CAF is different. The update target of a CAF is the `CAF_BLACKHOLE` that `lockCAF` in rts/sm/Storage.c allocates, and without profiling that object is two words, the size of an `StgInd`. Thus the store writes into the word after the object: the first word of the next object on the heap, or free space. The program below evaluates one CAF in the evaluation of another CAF. With user era 1 it stops with a segmentation fault on 9.10.3, 9.12.4, 9.14.1 and HEAD. On 9.14.1 the fault is in the garbage collector (`evacuate`, called from `scavenge_loop`). With user era 0 it gives the correct output.

The second consequence is a performance hazard that depends on the link layout. Each thunk update does two more loads, from static data of the RTS. In a small loop that updates one thunk for each element of a list, the checks are 4 of the 93 instructions for each element, and the difference in time is not more than the variation between runs. But in a larger program, one operation took 2.5 times as long in one build as in another. In the specialisation benchmark of the orthotope array library, on HEAD, `traverse` in `Identity` over a boxed array of 200000 elements took 27.17 to 27.58 ns for each element in one build, and 10.45 to 10.91 ns in another build of the same source. The two builds differ only in the alignment of code, thus in the address of `.bss`. With the same number of calls, the two processes executed the same number of instructions (909.6 to 909.7 million and 909.2 million). The slow process had 8.7 to 9.4 million demand fills of the L1 data cache from L2, and the fast process 3.6 to 3.7 million, although it made more calls. More than half of the extra cycles were in `stg_upd_frame_info`.

The address of `.bss` decides the effect, and the code does not. The objects of each build were linked again with `-optl-Wl,-Tbss=ADDR`. The fast build with `.bss` at the address of the slow build was slow (27.44 to 27.98 ns), and the slow build with `.bss` at another address was fast (10.88 to 11.88 ns). A change of any one bit from bit 12 to bit 27 of the `.bss` address removes the effect, and a change of bit 28, 29 or 30 does not. A move of the heap with `+RTS -xb` by 1 MiB or by 2^27 bytes removes the effect, and a move by 2^28 or 2^32 bytes does not. The effect is rare. We linked the objects of the slow build with `.bss` at 549 random placements (address bits 6 to 27 random). With the nursery size of the benchmark (`-A32m`), no placement was slow, either as linked or with the checks removed from a copy of the binary. Of the nursery sizes that we tested, from 16 to 64 MB, the slow build was slow only with 32 to 35 MB, and with the checks removed it was slow with none. These results agree with a conflict, in a cache structure that hashes address bits 12 to 27, between the line of `era` and `user_era` and one line on the heap. The way predictor of the L1 data cache of AMD processors is such a structure (Lipp et al., "Take A Way", 2020), and this processor is a Zen 3. But we did not confirm this mechanism, and we could not make a small program that shows the effect. The conclusion does not depend on the mechanism: the RTS without profiling does not need the two loads, and the loads give a program a large cost that a change of code size anywhere in the program can turn on or off. This also applies to measurements of changes to code layout, for example those in #27907: such a change moves `.bss`, and with these loads it can change the time of a program with many thunk updates for a reason that is not the change under test.

Two corrections are possible. (1) Make `PROF_HEADER_CREATE` expand to nothing without `PROFILING`, as `LDV_RECORD_CREATE` did before 9.10, with a definition in rts/include/rts/prof/LDV.h beside the old one. (2) Put the body of `profHeaderCreate` in `ifProfiling`, as other functions of `GHC.StgToCmm.Prof` do. One condition applies to both: if eras become available without profiling, as a comment in #27358 plans, the era needs a field that exists in a closure without profiling. The third word is not such a field. The documentation of `setUserEra`, `getUserEra` and `incrementUserEra` can also say what they do in a program without profiling.

To confirm by experiment that these checks are the root cause, we applied correction (1), below, to HEAD (commit 6913545fd3) as a provisional fix. The change served only this experiment. In the RTS without profiling, `stg_upd_frame_info` has no reference to `era` or `user_era`, and the profiled RTS keeps its four. The reproducer gives the correct output with user era 1 and with user era 5. In the benchmark, the objects of the slow build were linked with the fixed RTS and with `.bss` at the slow address. That binary took 11.84 to 14.99 ns for each element, against 28.01 to 28.54 ns with the old RTS. A profiled program with `+RTS -he` still gives one band for each of two eras. We did not run the testsuite.

```diff
--- a/rts/include/rts/prof/LDV.h
+++ b/rts/include/rts/prof/LDV.h
@@ -48,4 +48,9 @@
 
 #define LDV_RECORD_CREATE(c)   /* nothing */
 
+/* Cmm code calls PROF_HEADER_CREATE, which the Cmm parser otherwise expands
+ * to era checks and a store into the profiling header; a closure built
+ * without profiling has no such header. */
+#define PROF_HEADER_CREATE(c)  /* nothing */
+
 #endif /* PROFILING */
```

## Steps to reproduce

1. Save the program below as `Repro.hs`.
2. Compile it: `ghc -O1 Repro.hs`.
3. Run `./Repro 0`. It prints 500501 and 500500.
4. Run `./Repro 1`. It stops with a segmentation fault (exit status 139) on 9.10.3, 9.12.4, 9.14.1 and HEAD. On 9.8.4 the program does not link, because that RTS has no `setUserEra`.
5. Look at the update frame of the RTS without profiling. With 9.10.3 the commands below print four relocations against `era` and `user_era`. With 9.8.4 they print nothing.

```
A=$(find "$(ghc --print-libdir)" -name 'libHSrts-*.a' ! -name '*_*')
ar x "$A" Updates.o
objdump -dr Updates.o | awk '/<stg_upd_frame_info>:/{f=1} f&&/^$/{exit} f' | grep -E '\b(era|user_era)\b'
```

```haskell
-- A program without profiling sets the user era, and then evaluates two CAFs.
-- The evaluation of the first CAF forces the second CAF.  Base only.  The
-- foreign import is the declaration of setUserEra in GHC.Profiling.Eras
-- (package ghc-experimental).
--
-- Build:  ghc -O1 Repro.hs
-- Run:    ./Repro 0     -- prints 500501 and 500500
--         ./Repro 1     -- segmentation fault on GHC 9.10 and later
module Main (main) where

import System.Environment (getArgs)
import System.Mem (performGC)

foreign import ccall setUserEra :: Word -> IO ()

cafB :: Int
cafB = sum [1 .. 1000 :: Int]
{-# NOINLINE cafB #-}

cafA :: Int
cafA = cafB + 1
{-# NOINLINE cafA #-}

main :: IO ()
main = do
  [e] <- getArgs
  setUserEra (read e)
  print cafA
  performGC
  print cafB
```

## Expected behavior

The RTS without profiling does not execute the code of the profiling header, as before 9.10. In a program without profiling, `setUserEra` has no effect on the heap, or its documentation says that the function is only for profiled programs. It does not corrupt the heap.

## Environment

* GHC version used: 9.10.3, 9.12.4, 9.14.1, and HEAD 10.1.20260918 (commit 6913545fd3). All four show the defect. 9.6.7 and 9.8.4 do not have the code.

Optional:

* Operating System: Linux (kernel 7.0.0-34-generic)
* System Architecture: x86_64 (AMD Ryzen 7 5800X, Zen 3)
* Other tools: gcc 13.3.0, GNU binutils 2.42


/label ~"T::bug"
/label ~"needs triage"
