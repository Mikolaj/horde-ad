# GHC issue: the native code generator does not align hot loops

Not filed. This file is the draft, the text from "## Summary" down being the body to file. Title: **The native code generator has no loop alignment: the same loop is 1.6 times slower when it crosses a cache-line boundary, and `-fproc-alignment` cannot move it**. The prose is ASD-STE100 Simplified Technical English. The tracker was not searched for duplicates, because the machine that found this has no network access; do this before you file. Two observations in the body come from an array micro-benchmark in the orthotope repository, on the unmerged `speedup-strided-tovector` branch, which is not public: what `-fproc-alignment=64` does in a larger program, and what the correction costs there. The filed body is self-contained, and its own reproducer shows the effect.

## Summary

The native code generator gives an alignment directive to the start of a procedure and to nothing inside it. Thus the position of a hot loop in its cache line is an accident of the quantity of code before it. A change elsewhere in the module moves the loop to a different position, and the speed of the program changes with it.

The quantity is large. The reproducer below has a loop of 23 bytes. When an assembler stand-in puts that loop at each of the eight 8-byte positions in a 64-byte line, and nothing else changes, the time for each iteration is this:

| position of the loop head in the line | loop is in | ns per iteration |
|---:|---|---:|
| 0 | one line | 0.259 |
| 8 | one line | 0.257 |
| 16 | one line | 0.261 |
| 24 | one line | 0.256 |
| 32 | one line | 0.258 |
| 40 | one line | 0.260 |
| 48 | **two lines** | **0.410** |
| 56 | **two lines** | **0.411** |

Each value is the smallest of three runs on a machine with no other load, and a second sweep gave the same values to 1%. The six positions that keep the loop in one line agree to 2%. The two positions that divide it are **1.58 times slower**. The step is at the position where the loop first crosses a boundary, which for a loop of 23 bytes is a position above 41. The four compilers in the Environment section give the same result, between 1.55 and 1.59 times; the table in "Steps to reproduce" has each of them.

`-fproc-alignment=N` does not correct this. It aligns the start of a function. A loop keeps its offset in the function, thus the loop keeps an arbitrary offset in the line. The option makes the offset stable and does not make it correct. In a larger program, an array micro-benchmark, three binaries that differ only in inert padding and are built with `-fproc-alignment=64` put the two copies of one loop at byte 3 and byte 53 of a line, the same two positions in each of the three binaries. Byte 53 crosses a boundary. The documentation of the option says that it "can be used to limit alignment impact on performance as each function will start at a cache line". That is correct for a function. The cost is at the loop.

The other compilers on the same system align loops. GCC 13.3 at `-O2` puts `.p2align 4,,10` before each loop head, from the default `-falign-loops=16:11:8`. Clang 18 puts `.p2align 4` before each block that LLVM identifies as an inner loop header, with no option given. The LLVM backend of GHC does the same, thus the two backends of one compiler do not agree; `-optlc -align-loops=64` makes the boundary 64 bytes there. The native code generator gives `.align 8` at each procedure and no directive at any loop. The value of the alignment decides how frequently the problem occurs. With 8-byte alignment, three or four of the eight positions that a loop can occupy cross a boundary. With 16-byte alignment, one of four. With 32-byte alignment or more, no position crosses, for a loop of this size.

A correction is not expensive. In that same larger program, the stand-in assembler below aligned 395 loop heads. Each copy of that loop then starts at byte 0 of a line, `.text` becomes 0.13% larger, and the agreement test of that benchmark, which compares the result of each strategy on each array shape, stays correct. But there is one condition on the padding, and a first attempt did not meet it. The padding must be between two instructions. GHC puts an info table immediately before a return point, and a return point is a local label also. When the first version of the stand-in assembler aligned each of the 928 local labels that a jump goes back to, the padding separated an info table from its code, and the program stopped with an incorrect index. A rule that the previous line must be an instruction gives 395 labels and a correct program. A code generator does not need this rule, because it knows which labels are return points.

The effect on measurements is more urgent than the effect on speed, because a program that is slower is at least honestly slower. The position of a loop changes when unrelated code changes: a new function, a different order of definitions, a different version of a library, or a different set of optimisation flags. Thus two builds of one program can differ by a quantity of this size for that reason alone. Slowdowns of this size do occur in this manner in real measurements, and they are usually not seen, because no output of the compiler or of the benchmark shows the position of a loop.

The condition is worse than noise, because it is a bias. In each build the value is stable, thus more samples make the interval smaller around the value of that build and do not find the error. A user who compares two versions of a function measures the change of the code and the change of the position together, and no statistic in the benchmark divides them. The user then makes a conclusion about the code, keeps it, and can put a change into a program because of a difference that the position of a loop caused.

Three corrections are possible. (1) Align the head of each inner loop in the native code generator, as the LLVM backend does. 16 bytes is the value that GCC, clang and LLVM use; 32 bytes removes the problem for a loop of the size above. (2) If a default is not acceptable, add an option for the boundary, separate from `-fproc-alignment`, because a user who wants loop alignment in this backend today has no option to give and must change the backend or the assembler (see Workarounds). (3) A diagnosis aid, and not a correction: no output of GHC says where a loop is in its line, thus a user who sees a difference in speed between two builds has no method to find this cause. The documentation of `-fproc-alignment` can also say that the option does not align loops.

## Steps to reproduce

1. Save the two programs below as `Repro.hs` and `align-as.py`, and make `align-as.py` executable.
2. Look at the assembly of the native code generator: `ghc -O1 -S -fforce-recomp Repro.hs`. In `Repro.s`, find the conditional jump at the end of the loop of `kernel`, and then find the label that it names. There is no alignment directive before that label.
3. Do step 2 again with `-fproc-alignment=64`. The procedures now start at a 64-byte boundary, and there is still no directive before the label of the loop.
4. Do step 2 again with `-fllvm`. There is a `.p2align 4` immediately before each loop header.

| build | alignment directive before a loop head |
|---|---|
| native code generator, `-O1` | none |
| native code generator, `-O1 -fproc-alignment=64` | none |
| LLVM backend, `-O1 -fllvm` | one before each |

5. Measure the cost. For each position `k` in 0, 8, 16, 24, 32, 40, 48, 56, remove `Repro.o` and `Repro.hi`, and then compile with the stand-in assembler and run the program:

   ```
   LOOP_SKEW=$k ghc -O2 -fforce-recomp -pgma ./align-as.py Repro.hs -o prog-$k
   ./prog-$k
   ```

   The program prints the time for each iteration of the loop. The values are in the table above. To confirm the position, disassemble `prog-$k` and find the backward jump in `Main_zdwkernel_info`: its target is at byte `k` of a line.

   The results on the test system, from five runs of each build, with the loop in one line at position 40 and across two lines at position 48. On none of the four compilers do the two ranges touch:

   | | loop in one line | loop across two lines | slowdown |
   |---|---:|---:|---:|
   | 9.10.3 | 0.255–0.270 ns/iter | 0.406–0.420 ns/iter | 1.59 |
   | 9.12.4 | 0.260–0.270 ns/iter | 0.408–0.421 ns/iter | 1.57 |
   | 9.14.1 | 0.256–0.262 ns/iter | 0.407–0.424 ns/iter | 1.59 |
   | HEAD 10.1.20260803 | 0.262–0.275 ns/iter | 0.407–0.423 ns/iter | 1.55 |

6. See that an ordinary build gives a divided loop by itself, with no position given and no stand-in assembler. Put this same program in a package, build it with `cabal build`, and disassemble the result: the loop starts at byte 50 of a line, thus it crosses a boundary, and the program takes 0.405 ns for each iteration. Build the same package with the stand-in assembler, `cabal build --ghc-options="-fforce-recomp -pgma /full/path/to/align-as.py"`, and the loop starts at byte 0 and the program takes 0.253 ns. Nobody selected byte 50. It is the quantity of code before the loop, and it changes when that code changes.

Use `-fforce-recomp` for each command. GHC does not recompile for a change of `-fproc-alignment`, of `-fllvm` or of `-pgma`, thus a later command gives the output of the first command if the module is not new.

```haskell
-- Reproducer for the absence of loop alignment.  Base only.
--
-- Assembly:  ghc -O1 -S -fforce-recomp Repro.hs
-- Time:      LOOP_SKEW=k ghc -O2 -fforce-recomp -pgma ./align-as.py Repro.hs -o prog
--            ./prog
--
-- The loop of `kernel` adds to four accumulators that do not depend on each
-- other.  Thus the processor executes more than one iteration at the same
-- time, and the speed depends on the rate at which it can fetch the loop.
-- That is the condition in which the position in the cache line is
-- important.  A loop with one accumulator, where each iteration must wait
-- for the previous one, gives the same speed at all positions: the first
-- attempt at this reproducer had that shape and measured no difference.
-- `kernel` is exported, so that it keeps its own symbol in the binary.
{-# LANGUAGE BangPatterns #-}
module Main (main, kernel) where

import GHC.Clock (getMonotonicTime)

{-# NOINLINE kernel #-}
kernel :: Int -> Int -> Int -> Int -> Int -> Int
kernel !a !b !c !d 0 = a + b + c + d
kernel !a !b !c !d n = kernel (a + n) (b + 3) (c + 5) (d + 7) (n - 1)

main :: IO ()
main = do
  t0 <- getMonotonicTime
  let go !acc !i | i >= (40 :: Int) = acc
                 | otherwise = go (acc + kernel i 0 0 0 3000000) (i + 1)
  print (go 0 0)
  t1 <- getMonotonicTime
  putStrLn ("ns/iter: " ++ show ((t1 - t0) * 1e9 / (40 * 3000000)))
```

```python
#!/usr/bin/env python3
# A stand-in assembler for GHC's -pgma.  It aligns each loop head to 64
# bytes, and LOOP_SKEW=k then adds k bytes, which is how the measurement
# above puts one loop at a chosen position.  A loop head is a local label
# that a later instruction jumps backwards to.  The padding goes between two
# instructions only: GHC puts an info table immediately before a return
# point, which is a local label also, and padding between the table and its
# code makes an incorrect program.
#
# With LOOP_SKEW unset this is also a workaround, until GHC aligns loops:
#
#     ghc   -fforce-recomp -pgma /full/path/to/align-as.py Prog.hs
#     cabal build --ghc-options="-fforce-recomp -pgma /full/path/to/align-as.py"
#
# Five things to know before you use it that way.  A path relative to the
# directory that you build in is sufficient, and a full path is safer.
# `-fforce-recomp`, or a new build directory, is necessary, because GHC does
# not recompile for a change of -pgma.  Set REAL_AS if the C compiler of your GHC is not
# /usr/bin/gcc; `ghc --info` gives it as "C compiler command".  Only the
# modules that this GHC compiles change, thus the libraries keep the loops
# that they have.  And test the program that you build this way: the labels
# and the `.p2align` syntax are those of the GNU assembler on x86-64, no
# other system was tested, and a mistake in the padding gives an incorrect
# program and not an error from the compiler.
import os, re, subprocess, sys
REAL = os.environ.get('REAL_AS', '/usr/bin/gcc')
SKEW = int(os.environ.get('LOOP_SKEW', '0'))
LABEL = re.compile(r'^(\.L\w+):')
JUMP = re.compile(r'^j\w*\s+(\.L\w+)\b')
INSTR = re.compile(r'^[a-z][a-z0-9.]*\s')

def rewrite(path):
    src = open(path).read().split('\n')
    seen, heads = set(), set()
    for line in src:
        s = line.strip()
        m = LABEL.match(s)
        if m:
            seen.add(m.group(1))
            continue
        m = JUMP.match(s)
        if m and m.group(1) in seen:
            heads.add(m.group(1))
    if not heads:
        return
    out, prev = [], ''
    for line in src:
        m = LABEL.match(line.strip())
        if m and m.group(1) in heads and INSTR.match(prev):
            out.append('\t.p2align\t6, 0x90')
            if SKEW:
                out.append('\t.byte\t' + ','.join(['0x90'] * SKEW))
        out.append(line)
        s = line.strip()
        if s and not s.startswith('#'):
            prev = s
    open(path, 'w').write('\n'.join(out))

for a in sys.argv[1:]:
    if a.endswith('.s') and os.path.exists(a):
        rewrite(a)
sys.exit(subprocess.call([REAL] + sys.argv[1:]))
```

## Expected behavior

The expected behavior is that the head of an inner loop starts at a boundary that the processor fetches in one operation, as the LLVM backend of GHC and the other compilers on the system do. If this is not the default, the expected behavior is that an option gives it.

## Workarounds

There are two, and the first needs nothing that is not in GHC.

**The LLVM backend.** It aligns each loop head to 16 bytes, thus `-fllvm` makes the condition much less frequent: with 16-byte alignment one position of four crosses a boundary, where with 8-byte alignment three or four of eight cross. `-optlc -align-loops=64` makes the boundary 64 bytes, and then no position of a loop of the size above crosses. `{-# OPTIONS_GHC -fllvm #-}` selects the backend for one module, thus a program that has one hot module does not change everywhere. The cost is that the LLVM backend makes all the code of that module in a different manner, thus this exchanges one set of speeds for another and is not only a correction of the alignment. The reproducer above cannot show the exchange, because LLVM replaces its loop with arithmetic and there is then no loop to align.

**The stand-in assembler below.** It keeps the native code generator and aligns the loop heads of each module that GHC compiles. Its comment gives the commands and the five conditions. It is a demonstration of 40 lines that is not a part of GHC: use it for a measurement, or for a program that you build yourself, and not in a package that other people build.

Nothing else that was tried is a workaround. A change of the source, to move the loop to a better position, is the accident itself and not a control of it: the position depends on the quantity of code before the loop, thus the next change to that code moves the loop again.

## Environment

* GHC version used: 9.10.3, 9.12.4, 9.14.1, and HEAD 10.1.20260803 (commit d415f38a75). All four show the same behavior, and the ratio between a divided loop and a loop in one line is between 1.55 and 1.59 on all four.

Optional:

* Operating System: Linux (kernel 7.0.0-28-generic)
* System Architecture: x86_64 (AMD Ryzen 7 5800X, Zen 3, 32 MB last-level cache)
* Other tools: gcc 13.3.0 as the assembler, clang 18 and LLVM 18


/label ~"needs triage"
