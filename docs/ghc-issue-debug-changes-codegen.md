# GHC issue: a DWARF debug option changes the code that GHC emits

Filed as [GHC work item 27687](https://gitlab.haskell.org/ghc/ghc/-/work_items/27687); this file stays as the filed record, the text from "## Summary" down being the filed body. Title: **A DWARF debug option changes the generated code: `-g1` gives different instructions and a different register assignment**. The prose is ASD-STE100 Simplified Technical English. The case that found the defect is a loop placement measurement in the orthotope micro-benchmark, on the unmerged `speedup-strided-tovector` branch, which is not public: a debug build was made to find which function each hot loop belongs to, and that build was not the same program as the build that was measured. The filed body is self-contained.

## Summary

GHC emits different machine code for one module when you give a DWARF debug option. The debug information is not the difference. Remove each `.loc` directive, each label that the option adds, and each `.debug_*` section from the two assembly files. The instructions that remain are still not equal.

The module in "Steps to reproduce" gives this result at `-O1` on each of the four compilers in the Environment section. Without the option, GHC emits 96 instructions. With `-g1`, it emits 95. The difference is one `movq`. The register assignment is different also, and one basic block of two instructions is in a different position.

`-g1` is sufficient, and it is the level of the option that promises the least. The users guide says that `-g1` "produces stack unwinding records for top-level functions". A record is data about a program. It is not a part of the program. `-g2` and `-g3` give the same result as `-g1` for this module, thus the level is not what changes the code. The option is.

The optimisation level has an effect on the result. At `-O0`, the code is equal on all four compilers. At `-O1`, it is different on all four. At `-O2`, it is equal on 9.12.4 and on HEAD, and it is different on 9.10.3 and on 9.14.1.

The defect is that debug information must describe a program and must not change it. A user gives the option to examine a program, and receives a different program to examine. Two consequences follow, and they are general. Different code can have a different speed, thus a measurement that uses a debug build does not measure the build that a user releases. Also, different code has a different position in memory, thus the difference in speed is not limited by the quantity of code that is different.

## Steps to reproduce

1. Save the program below as `Repro.hs`.

2. Compile it two times, to assembly:

```
ghc -O1 -S Repro.hs -o plain.s
ghc -O1 -g1 -S Repro.hs -o debug.s
```

3. Keep the instructions only, and make the names of the labels and the numbers equal. This step is necessary because a debug build gives other names to its labels:

```
for f in plain debug; do
  grep -E '^[[:space:]]+[a-z]' $f.s |
    sed 's/\.L[A-Za-z0-9_]*/L/g; s/-\?[0-9][0-9]*/N/g' > $f.txt
done
wc -l plain.txt debug.txt
diff plain.txt debug.txt
```

4. The counts are 96 and 95, and the diff is not empty. Its first part, from 9.12.4, shows one instruction that is absent and a register that is different:

```
9d8
< 	movq N(%rN),%rbx
11,12c10,12
< 	xorl %edx,%edx
< 	jmp L
---
> 	movq N(%rN),%rdx
> 	xorl %ebx,%ebx
> 	movq %rbx,N(%rsp)
```

```haskell
-- Reproducer: a DWARF debug option changes the generated code.  Base only.
--
-- Build:  ghc -O1 -S Repro.hs -o plain.s
--         ghc -O1 -g1 -S Repro.hs -o debug.s
--
-- The two loops are mutually recursive: the inner one calls the outer one.
-- That property and the strictness annotations are both necessary in this
-- module.  If you remove the annotations, or if you make the inner loop
-- independent of the outer one, the two builds give equal code.
{-# LANGUAGE BangPatterns #-}
module Repro (go) where

go :: [Int] -> Int -> Int
go (n : ns) !off =
  let dim !i !acc | i >= n = acc
                  | otherwise = dim (i + 1) (go ns (off + i))
  in dim 0 off
go [] !off = off
```

## Expected behavior

The expected behavior is that a DWARF debug option adds debug information and changes no instruction. If the option must change the code, the expected behavior is that its documentation says so. A level of it that produces records for backtraces must not change the code at all.

## Environment

* GHC version used: 9.10.3, 9.12.4, 9.14.1, and HEAD 10.1.20260803 (commit d415f38a75). All four show the same behavior at `-O1`.

Optional:

* Operating System: Linux (kernel 7.0.0-28-generic)
* System Architecture: x86_64 (AMD Ryzen 7 5800X, Zen 3)
* Other tools: gcc 13.3.0 as the assembler

/label ~"T::bug"
/label ~"needs triage"
