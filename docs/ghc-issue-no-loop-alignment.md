# GHC issue: the native code generator does not align hot loops

Filed as [GHC work item 27668](https://gitlab.haskell.org/ghc/ghc/-/work_items/27668); this file stays as the filed record, the text from "## Summary" down being the filed body. Title: **The native code generator has no loop alignment: the same loop is 1.6 times slower when it crosses a cache-line boundary, and `-fproc-alignment` cannot move it**. The prose is ASD-STE100 Simplified Technical English. Two observations in the body come from an array micro-benchmark in the orthotope repository, on the unmerged `speedup-strided-tovector` branch, which is not public: what `-fproc-alignment=64` does in a larger program, and what the correction costs there. The filed body is self-contained, and its own reproducer shows the effect. The recompilation defect that step 5 names by title is [work item 27667](https://gitlab.haskell.org/ghc/ghc/-/work_items/27667); both reports were written before either number existed, so the tracker copy is where a link between them can go.

## Summary

With no option given, the native code generator aligns the start of a procedure to 8 bytes and puts no alignment directive inside a procedure. There are two reasons why this does not help the speed of a hot loop, and each reason alone is sufficient. The first is the size of the boundary. Those 8 bytes are not a value that was selected for the speed of a loop: they are the word alignment that GHC gives to each section, from `pprAlignForSection` in `GHC.CmmToAsm.X86.Ppr`, which gives the same 8 bytes to every type of section but a string. A boundary of that size is too small for a loop. The loop of 23 bytes in the reproducer below can start at eight positions in a line, and it crosses a boundary at two or three of them.

The second reason is which address the directive constrains, and it is the more important one. The directive is at the start of the procedure, thus it constrains the address of the procedure. The address that decides the speed is the address of the loop head, and that address is the address of the procedure plus the quantity of code between the start of the procedure and the loop. That quantity is arbitrary. `-fproc-alignment=64` shows that the two reasons are separate, because it corrects the first and not the second: the boundary becomes 64 bytes, which is sufficient, but the directive is still at the start of the procedure, thus the loop head is still at that arbitrary distance after a boundary. So even with `-fproc-alignment=64` the position of a hot loop in its line is an accident of the quantity of code between the start of its procedure and the loop, and a change to the function that holds the loop moves it and changes the speed of the program.

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

What `-fproc-alignment=N` does do is make the position stable: with each procedure at a 64-byte boundary, the position of a loop no longer depends on the quantity of code before its procedure, thus a change in another part of the module does not move it. But stable does not mean trustworthy for a benchmark. In a larger program, an array micro-benchmark, three binaries that differ only in inert padding and are built with `-fproc-alignment=64` put the two copies of one loop at byte 3 and byte 53 of a line, the same two positions in each of the three binaries. Byte 53 crosses a boundary. The documentation of the option says that it "can be used to limit alignment impact on performance as each function will start at a cache line". That is correct for a function, and the cost is at the loop. That the option stops at functions is known and is not an oversight. In [#14701](https://gitlab.haskell.org/ghc/ghc/-/work_items/14701), "Investigate the performance impact of code alignment", the person who added the option [wrote in 2022](https://gitlab.haskell.org/ghc/ghc/-/work_items/14701#note_432242): "I've since added the flag `-fproc-alignment` which aligns cmm functions to the given alignment. We could do something about loops as well but I haven't looked too closely." This report is a measurement of the part that was not done.

The other compilers on the same system align loops. GCC 13.3 at `-O2` puts `.p2align 4,,10` before each loop head, from the default `-falign-loops=16:11:8`. Clang 18 puts `.p2align 4` before each block that LLVM identifies as an inner loop header, with no option given. The LLVM backend of GHC does the same, thus the two backends of one compiler do not agree; `-optlc -align-loops=64` makes the boundary 64 bytes there. The native code generator gives its `.align 8` at each procedure and, as above, nothing at a loop. The value of the alignment decides how frequently the problem occurs, and a longer loop is in more danger. For the loop of 23 bytes in the reproducer, 8 bytes leave two or three positions of eight that cross a boundary, the 16 bytes that those compilers use leave one or two of four, and 32 bytes leave none of two. A loop of 48 bytes crosses at five or six positions of eight at 8-byte alignment. Which of the two quantities applies depends on where the loop starts inside its procedure. A loop longer than the boundary crosses at every position, but its position still decides the quantity of lines that it occupies: a loop that starts at a boundary occupies the fewest lines that its length permits, and a loop that starts late enough in a line occupies one more. This report measures one line against two and does not measure that case.

A correction is not expensive. In that same larger program, the stand-in assembler below aligned 395 loop heads. Each copy of that loop then starts at byte 0 of a line, `.text` becomes 0.13% larger, and the agreement test of that benchmark, which compares the result of each strategy on each array shape, stays correct. And the code generator can do this more easily than a stand-in assembler can. The assembler sees only labels, thus it must find the loop heads by a search for a jump that goes backwards, and it must obey a rule about where the padding may go, which Workarounds gives. The code generator knows which labels are loop heads and which are return points, thus it needs neither the search nor the rule.

The effect on measurements is more urgent than the effect on speed. In each build the position is stable, thus it is a bias and not noise: more samples make the interval smaller around the incorrect value. A user who compares two versions of a function measures the change of the code and the change of the position together, and no statistic divides the two. What that user then decides can cost more than the worst position of a loop does, because the decision keeps the slower version, or removes the faster one, and it stays in the program after the loop has moved again. Reports of a difference in speed that nobody can explain, or of a benchmark that does not give the same result again, are a large class, and this condition can be a part of the cause of some of them. #20405 and #19701 in this tracker are examples, and [criterion issue 60](https://github.com/haskell/criterion/issues/60) is an example from outside it. This report does not examine those three: the connection is possible and it is not demonstrated here.

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

5. Measure the cost. For each position `k` in 0, 8, 16, 24, 32, 40, 48, 56, compile with the stand-in assembler and run the program:

   ```
   LOOP_SKEW=$k ghc -O2 -fforce-recomp -pgma ./align-as.py Repro.hs -o prog-$k
   ./prog-$k
   ```

   The program prints the time for each iteration of the loop. The values are the ones in the first table of this report. To confirm the position, disassemble `prog-$k` and find the backward jump in `Main_zdwkernel_info`: its target is at byte `k` of a line.

   The results on the test system, from five runs of each build, with the loop in one line at position 40 and across two lines at position 48. On none of the four compilers do the two ranges touch:

   | | loop in one line | loop across two lines | slowdown |
   |---|---:|---:|---:|
   | 9.10.3 | 0.255--0.270 ns/iter | 0.406--0.420 ns/iter | 1.59 |
   | 9.12.4 | 0.260--0.270 ns/iter | 0.408--0.421 ns/iter | 1.57 |
   | 9.14.1 | 0.256--0.262 ns/iter | 0.407--0.424 ns/iter | 1.59 |
   | HEAD 10.1.20260803 | 0.262--0.275 ns/iter | 0.407--0.423 ns/iter | 1.55 |

6. See that an ordinary build gives a divided loop by itself, with no position given and no stand-in assembler. Put this same program in a package, build it with `cabal build`, and disassemble the result: the loop starts at byte 50 of a line, thus it crosses a boundary, and the program takes 0.405 ns for each iteration. Build the same package with the stand-in assembler, `cabal build --ghc-options="-fforce-recomp -pgma /full/path/to/align-as.py"`, and the loop starts at byte 0 and the program takes 0.253 ns. Nobody selected byte 50. It is the quantity of code before the loop, and it changes when that code changes.

Use `-fforce-recomp` for each command. GHC does not recompile for a change of `-fproc-alignment`, of `-fllvm` or of `-pgma`, thus a later command gives the output of the first command if the module is not new. That is a different defect, and it is reported as "Recompilation checking ignores every setting that carries a value: `-fllvm`, the inliner thresholds, `-fproc-alignment` and the `-pgm*` and `-opt*` families are all missed".

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
# bytes, and LOOP_SKEW=k then adds k bytes, which is how the measurement in
# the report puts one loop at a chosen position.  A loop head is a local label
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
# not recompile for a change of -pgma, which is a separate defect and has its
# own report.  Set REAL_AS if the C compiler of your GHC is not
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

**The LLVM backend.** This one needs nothing that is not in GHC. It aligns each loop head to 16 bytes, thus `-fllvm` makes the condition less frequent: for the loop of the reproducer, one or two positions of four cross a boundary, where at 8 bytes two or three of eight cross. `-optlc -align-loops=64` makes the boundary 64 bytes, and then a loop that is not longer than 64 bytes crosses at no position. `{-# OPTIONS_GHC -fllvm #-}` selects the backend for one module, thus a program that has one hot module does not change everywhere. Give `-fforce-recomp` when you add or remove `-fllvm`, because GHC does not recompile for a change of backend, which is the separate defect named in step 5. The cost is that the LLVM backend makes all the code of that module in a different manner, thus this exchanges one set of speeds for another and is not only a correction of the alignment. The reproducer above cannot show the exchange, because LLVM replaces its loop with arithmetic and there is then no loop to align.

**The stand-in assembler above.** Save the second of the two programs as `align-as.py`, make it executable, and give its path to `-pgma`. Do not set `LOOP_SKEW`: that variable is for the measurement above, and with it unset the program puts each loop head at a 64-byte boundary, which is what a workaround wants.

    ghc   -fforce-recomp -pgma /full/path/to/align-as.py Prog.hs
    cabal build --ghc-options="-fforce-recomp -pgma /full/path/to/align-as.py"

This keeps the native code generator and aligns the loop heads of each module that GHC compiles, and no others. The comment in the program repeats these commands and gives the conditions that apply when you use it on a program of your own. It is a short demonstration and not a part of GHC: use it for a measurement, or for a program that you build yourself, and not in a package that other people build.

The reason it puts the padding between two instructions only, and the reason to test what you build with it, are the same. GHC puts an info table immediately before a return point, and a return point is a local label also, thus it looks like a loop head. The first version of this program aligned each of the 928 local labels that a jump goes back to, the padding then separated an info table from its code, and the program stopped with an incorrect index. The rule that the previous line must be an instruction gives 395 labels and a correct program. The loops that this rule does not align are the loops whose head is immediately after a table. A mistake of this kind gives an incorrect program and not an error from the compiler, which is why the test matters. All of this is a limitation of work at the level of the assembly file, and not a difficulty of loop alignment itself.

Nothing else that was tried is a workaround. A change of the source, to move the loop to a better position, is the accident itself and not a control of it: the position depends on the quantity of code before the loop, thus the next change to that code moves the loop again.

## Environment

* GHC version used: 9.10.3, 9.12.4, 9.14.1, and HEAD 10.1.20260803 (commit d415f38a75). All four show the same behavior, and the ratio between a divided loop and a loop in one line is between 1.55 and 1.59 on all four.

Optional:

* Operating System: Linux (kernel 7.0.0-28-generic)
* System Architecture: x86_64 (AMD Ryzen 7 5800X, Zen 3, 32 MB last-level cache)
* Other tools: gcc 13.3.0 as the assembler, clang 18 and LLVM 18


/label ~"needs triage"
