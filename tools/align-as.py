#!/usr/bin/env python3
"""A stand-in assembler for GHC's -pgma that aligns loop heads to a cache line.

Written for orthotope's micro-regime3 benchmark and kept there until
2026-10-06, so the README.md, Main.hs, `micro` binary, Runs and scripts
named below are that directory's, at
https://github.com/Mikolaj/orthotope/tree/speedup-strided-tovector/micro-regime3

GHC's native backend emits `.align 8` at procedure starts and nothing inside
them, so a hot loop lands wherever its procedure's code puts it, and
README.md's floor section prices that at 1.22x best to worst for the 28-byte
run-fill. `-fproc-alignment=64` does not reach a loop -- it pins the procedure
and so freezes the offset rather than choosing it. This does choose it: it
sits between GHC and the real assembler and puts a `.p2align` in front of
every loop head, which is a local label that a later instruction jumps
backwards to.

    cabal build micro --ghc-options="-pgma /path/to/align-as.py -fforce-recomp"

A fresh `--builddir` is not optional: cabal answers "Up to date" for a change
of `-pgma`, of the LOOP_* environment or of this file, so an existing build
keeps the old object code and reports nothing, `-fforce-recomp` reaching no GHC
(README.md's run chapter). Where cabal does re-invoke GHC, GHC does not count
`-pgma` or `-fproc-alignment` as a flag change, which is what `-fforce-recomp`
is for (its floor section).

  LOOP_ALIGN   log2 of the boundary, default 6 (64 bytes)
  LOOP_MAXSKIP pad only a loop that would cross a boundary it need not,
               default off
  LOOP_LOOKTHROUGH  read past byte-free lines when deciding whether a head
               follows an info table, which a `-g` assembly gets anyway;
               on a plain one it finds 27 heads more and so is a basis
               change, which is why it is a switch and off by default
  LOOP_NOOVERLAP  leave alone a head whose own cycle begins inside
               another's and ends after it, `a < h < b < j`, where the pad
               would sit on that other loop's back-edge path and be paid at
               its trip count. Ordinary nesting is untouched. A basis
               change, so off by default, as LOOP_MAXSKIP is
  LOOP_DEADSPOT  put every pad in a dead spot -- right after an
               unconditional jump, or at the module's text start -- rather
               than in front of the head, so that no pad is ever executed
               and nothing comes between an info table and its label. Every
               head is placed; the guard, the look-through and the
               containment test as a skip do not apply, the last serving
               as a priority instead. Its own section below. A basis
               change, so off by default
  LOOP_EXITSPAN  cost a head's fall-through exit with its body: a second
               span runs from the head through the first jump after its
               last back edge, and the lines-spanned charge is taken on
               both. A cost inside the dead-spot planner, so it wants
               LOOP_DEADSPOT=1 beside it and refuses without. A basis
               change, so off by default. Its own section below
  LOOP_ENTRIES  charge op-cache entries rather than lines: each straight
               segment of the cycle, body and exit, is cut at every
               LOOP_WINDOW boundary, each piece costs one entry per
               LOOP_ENTRY_OPS instructions, and the head pays the total
               beyond the uncut minimum. Wants LOOP_DEADSPOT=1 likewise,
               stands alone rather than adding the lines charge, and is
               off by default. The same section
  LOOP_WINDOW  bytes of the window that ends an entry, default 64
  LOOP_ENTRY_OPS  instructions an entry holds, default 8
  LOOP_BLOCKRULES  charge the fetch blocks of the cycle and the front-end
               penalties nine sweeps measured on this Zen 3: a whole cycle
               for the segment's taken conditional or its fused pair
               astride a boundary or ending in a different line from the
               segment's previous branch, a whole cycle for the head
               within eight bytes of its line's end, half cycles for a
               cut leaving a short last block and for a block holding
               only a jmp, a quarter for an unfused taken conditional,
               over the larger of ops/6 and blocks. Wants
               LOOP_DEADSPOT=1 likewise, stands alone, and is off by
               default. The same section
  LOOP_SETTLED  the block rules plus the back edge's own rules, the spot
               fewest jumps cross, and the plan settled against the
               assembler. Wants LOOP_DEADSPOT=1 likewise, stands alone,
               and is off by default. Its own section below
  PAD_BYTES    dead bytes appended after the first module's text, default 0
  LOOP_PIN     LABEL:RESIDUE, a probe's knob and never a recipe's: the group
               holding that head takes the residue that puts the head
               there, whatever any cost says, so a placement can be built
               to order and timed. Dead-spot form only; refused otherwise
  REAL_AS      the real assembler, default /usr/bin/gcc
  ALIGN_AS_VERBOSE  report the budgets emitted, the heads fallen back on,
               and the heads the info-table guard left alone

An on/off variable above is off when unset, empty or `0`, and on for any
other value; `LOOP_ALIGN` and `PAD_BYTES` take a number and are read as one.

**Pad only a loop that would cross a boundary it need not, and only by what
it needs** -- `LOOP_MAXSKIP=1`, and off by default because a default is the
one thing a pair's note cannot record: every half is built by a recipe that
sets what it wants explicitly, so a default that moved would rebuild some
other binary under the name the note gives. Run 11 priced the two forms and
the basis has been max-skip since Run 12, which is a fact about the recipes
and not about this file. A loop of length `L` at
`p = addr mod 64` occupies `(p + L - 1) div 64 - p div 64 + 1` cache lines,
and holds that at its least `ceil(L/64)` for every `p` up to `s = 64 *
ceil(L/64) - L`, the free room in its last line. So

    spans a line it need not  <=>  p > s  <=>  padding <= 63 - s

and `63 - s` is `(L-1) mod 64`, which makes `.p2align 6, 0x90, (L-1) mod 64`
move exactly the heads that would cross an extra boundary and no others --
exactly, GNU `as` skipping the alignment altogether when it would need more
than `max_skip` bytes. A head so treated either stays byte for byte where it
fell or goes to offset 0, there being no third outcome, and none is moved for
nothing. `p` is left to the assembler because padding upstream moves it; `L`
is measured here because the assembler will not say, and can be, being
layout-invariant for these loops: padding before a head does not change
intra-loop distances, so a short loop's backward branch keeps its `rel8`
encoding.

**The criterion is lines spanned and not straddling**, and the two are the
same question only for a loop that fits a line, where `s = 64 - L` and the
budget is the plain `L-1`. Above that the straddle reading says a loop
crosses a boundary wherever it sits and so cannot be helped, which is true
and beside the point: a 68-byte loop occupies 2 lines at offset 60 and 3 at
offset 61. **Taking the narrow reading is a ruling this file now records
against itself.** The first max-skip form dropped every head with `L > 64`
and left **137** of the 395 heads spanning a line more than they need, where
the unconditional form leaves none -- and this code is mostly such loops,
only 120 heads carrying a loop that fits a line, the median 144 bytes and the
longest 18097. Nor did it leave them alone: 134 long heads span an extra line
with no shim at all and 137 after that one, the padding for the short heads
having shifted them. Under the rule above, 148 of the 275 long heads end at
offset 0, the other 127 stay where they fell, and every one of the 127 is
already spanning the least its length allows.

**Measured out of band, one extra assembly per module, and from the symbol
table rather than from a disassembly.** A probe copy of the source carries an
ordinary local symbol at each head and one after each backward jump that
targets it -- symbols occupy no bytes, so the probe lays out as the real
assembly will -- and `L` is the shortest head-to-end distance the assembled
probe's symbol table reports. **The disassembly this was first written as is
what the symbol table replaced, and the reason is a measurement**: on
`Main.hs` at 2b41e53 `objdump` can attribute a backward jump to only **141**
of the 395 heads, tables-next-to-code being what its linear sweep loses
sync on (`loop-offsets.py`'s own docstring prices the same effect), so 254
heads would have fallen back to the unconditional directive and most of the
change would not have happened. The two routes **agree on `L` at every one of
the 141 both can read**, which is what warrants the exact one; the symbol
table prices all 395, so the fallback count here is **0** and nothing rests
on it (2026-08-11, -fspec-constr, GHC 9.12.4).

Both forms emit a directive at all 395 heads, and what differs is the budget:
without one the assembler always pads, with one it declines wherever the loop
already spans the least it can. The costs the unconditional form charged fall
accordingly. `.text` is
20385989 bytes under it against the plain build's 20373701, up 12288 or
0.060% -- the 0.13% recorded here before does not reproduce at any of the
three sizes it could have been a ratio of -- and 20377797 under max-skip, up
4096 or 0.020%, a third of it for the same zero heads spanning a line they
need not. And arms whose loops were already line-resident read 1.0069 to
1.0378 *slower* aligned in Run 10, having fallen through into aligned heads
and executed the NOPs; those loops now keep their own offset, 58 of the 112
short loops `--survey` reads in this binary sitting at 0 against 100 of 101
in the unconditional one, and **none straddling in either**. What the
max-skip form gives up is membership invariance -- adding an arm can move a
fitting loop onto a boundary, where the unconditional form relocates
nothing -- which is why Run 11 pairs the two rather than replacing one with
the other.

**Every pad in a dead spot, `LOOP_DEADSPOT=1`** (2026-08-31). A pad in front
of a head is executed by whatever falls through into it, and two shapes GHC
emits make that dear. An inner loop is rotated so that its bottom test is
where the enclosing loop enters, which puts the outer head's pad on the
inner loop's every iteration: `lib-stage2` on `alexnet-L1-55-c3-k11` counts
19119938 instructions an iteration under the max-skip form against 18121686
with no shim (`perf stat -e instructions:u`, `-n 100` minus `-n 50` over
50). And a head that is a return point sits behind its info table, which
the INSTR guard protects by leaving the head where it fell. A pad after an
unconditional `jmp` instead -- the only way to the byte after it being a
label, which comes after the pad -- costs nothing at run time and precedes
any table, so the guard is not needed and every head is placed: 1233 of
`Main.hs`'s heads at 0add4f4 against the guard's 563, among them 119 short
loops behind a table -- the list walk's return point, whose
already-evaluated branch `testb $7,%bl; jne` jumps straight back to it --
93 of which straddle under the max-skip form and none of which
`loop-offsets.py --survey` can see, `objdump` losing sync on the table
before them.

Heads with no dead spot between them move together, so a group gets one
directive, at a dead spot before it: `.p2align 6, 0x90, m`, and a `.skip
rho, 0x90` after it where the group wants the spot at a residue other than
0. `m` fires exactly when some head of the group would otherwise span a
line it need not: the `.align 8` before each table between the spot and the
heads is modelled for all 64 incoming residues, and the assembler counts the
pad's bytes, so a `.skip k` predicted from the probe's addresses -- which a
`jmp` across the pad, growing from `rel8` to `rel32`, put off on 458 of 504
groups -- is not needed. A jump between the spot and a head that targets
above the spot still grows across the pad, and the head then lands off its
residue by the bytes it grew: Run 38's control half put `.LQeN1` at 8 where
its plan bought 0 or 1, three such jumps and nine bytes, which the verified
count carries and the line after it names (2026-09-22); the nearer spot lost
on budget alone, and preferring it is a basis change nobody has taken. And
whatever lands upstream of a group moves it by whole lines: the first roster
change read under this form, `run23-spot` to `run24-g912` on 2026-09-02,
kept every mod-64 offset of the tracked eight heads, two addresses to the
byte and six on one displacement of 0x940, which is 37 lines, where the
max-skip form's two roster changes, Runs 20 and 21, kept none (README, the
floor section's build rules). The cost has one order inside a group: a head
`overlapped` names is the outer of a rotated pair and yields, its straddle
being paid once per exit of the inner loop where the inner's would be paid
per iteration. Measured on that assembly, against the max-skip form: 4
short loops straddling of 285 against 94, no pad byte executed against
2281, `.text` up 18190 bytes against 6096. The four are the fills' rotated
pairs -- `fillStage2`, `fillStage2Short`, `fbMutOdoVecdimsAddInLeafU2` and
its `Down` twin, named off a `-g3` twin -- which no residue resolves, two
loops of 51 and 55 bytes 42 apart not fitting a line, and the inner one
is the resident. `check` is green with its log byte-identical, and the
counter reads the shim-free figure on the fills. Timed against the basis
on 2026-09-01 (README's task 6): every arm whose fill carried a pad reads
faster, `fillStage2`'s users 0.943 to 0.945 and the `u2` leaves 0.951 and
0.955, the arms whose fills carried none within the floor. Off by default
for the reason the other switches are: every figure published through this
shim was measured under the max-skip form, and moving the basis is a run's
decision.

**The exit span and the entry count, `LOOP_EXITSPAN=1` and
`LOOP_ENTRIES=1`** (2026-09-15). The span the planner protects runs from
a head to its back edge, and a loop that turns over once a run exits
every run through the instructions after that edge: Run 32's HEAD half
left `fillStage2`'s stepping loop at offset 9, its 51-byte body inside
the line and its exit `cmp; jge` astride the line's end, and paid about
a cycle a run for it where the 9.12.4 half at offset 0 paid none, the
instructions and the taken branches being identical -- an op-cache fetch
more a run on the counter, and the same cost whether the branch is split
by the boundary or starts the next line, read off a sweep of that loop
over all 64 offsets. README's placement section carries the sweep, the
per-core table it was checked against and the sources. So the exit-span
form reads a second span, head through the first jump on the fall-through
path after the last back edge, and charges lines spanned beyond the least
on both spans, summed rather than replaced so that a short body whose
exit span is long keeps the protection it has. The entry form is the
model the sweep suggests and does not fully bear out, the count
reproducing 51 to 54 of the 64 offsets over two sweeps: each straight segment of the cycle,
body and exit, cut at every window boundary by the instruction's ending
byte, a piece costing one entry per LOOP_ENTRY_OPS instructions, the head
charged the total beyond the uncut minimum, and nothing else -- a cut
that leaves a full entry on each side of a long segment is free under it
and is not under the exit span, which is where the two part and what a
pair of them prices. Priced the same day on thirteen cells in interleaved
pairs, on 9.12.4 and on HEAD, the two read level, 0.9917 to 1.0071 of
each other, with the entry form crossing up to twice the windows for it,
while the exit-span half beats Run 32's HEAD binary by 4 to 9 percent
gross on the four short-run cells. Those thirteen were fills and
references; on a reducer's per-run loop with a three-element body,
window-224x224-k3's stage 9, the entry form reads 7 percent behind,
its cut having stranded a stub (README, the open list). So the exit span is
the candidate basis and the entry form stays here, off, for the day a
cell contradicts that (README, the open list).

**The block rules, `LOOP_BLOCKRULES=1`** (2026-09-15, evening): the
cost `probe-fetch-model.py` fitted to nine sweeps, 319 of 320 residues
on the loops the front end bounds, carried over rule for rule -- one
cycle a fetch block, a straddling first instruction leaving an empty
block that is fetched like any other; a whole cycle for a segment's
taken conditional branch, or its fused pair, astride the boundary or
ending in a different line from the segment's previous predicted
branch; a whole cycle for the loop head within eight bytes of its
line's end; half cycles for a cut leaving a last block of three or
fewer instructions starting in its line, for a block holding only a
`jmp`, and a quarter for an unfused taken conditional; the penalties
added to the larger of ops over six and blocks, whole where the blocks
bound the loop and halved where the dispatcher does. A head's cost at a
residue is that figure less its least over the 64 residues, in the tier
its body length puts it in, so a crossing that fires no rule is free
and a cycle longer than a line is priced by where its cut falls, which
neither earlier cost could say. The segment-ending branch is taken and
any inside a segment is not, the shim's standing assumption. All three
are costs of the dead-spot planner and refuse to run without
`LOOP_DEADSPOT=1`, since a switch that implied another would be a
default and a pair's note records no default. Under
ALIGN_AS_VERBOSE each plans the module a second time under the cost
below it, the entry count and the block rules each against the exit
span and the exit span against the plain dead-spot cost, probes that
plan too, and names the
heads the two costs place at different residues, which is the list a
pair of the two can say anything about; and the verified line counts
the exit spans still astride. `probe-entries-sweep.py` is
the exhaustive reading for one loop, predicted entries against measured
cycles at every residue.

**The settled plan, `LOOP_SETTLED=1`** (2026-09-22): the block rules with
three rules for the back edge's own bytes, and the spot chosen and then
checked against the assembler --- one switch, both halves being a reading
taken over the model's, the core's on the residue and the assembler's on the
spot. The rules are `probe-r38-sweep.py`'s, the fill loop's Run 38 bytes
swept over the 64 residues at a fixed address: the back edge starting on
a 16-byte boundary or crossing one costs 5 to 11.5 cycles a run against 4
to 5 (residues 3, 4, 19, 20, 35, 36, 51 and 52 there), in the first eight
bytes of a line up to 11.5, easing with distance (21 to 26), and in the
last four 6 to 8.5 (43 to 46, the tail's `jmp`, which is the outer head's
back edge); the exit's taken branch, the `jge`, crossed the line's end at
14 and 15 for nothing, so the back edge alone is charged --- the first rule
read on a `jl` and the other two on a `jmp`, each charged to any back edge,
which is the switch's bet and what a pair prices. On that loop the exit
span and the block rules rate residues 0 to 13 alike and this cost charges
3 and 4, where the run had put every fill head: pinned at 0, the basis read
`lib-stage2-lean` at 9.6 million cycles an iteration against 11.5 to 12.3
at 4. The spot: a group's spots are ranked on cost, then on how many jumps
between the spot and its heads target above the spot, the only ones a pad
there can lengthen, then on nearness, and last on the budget, which alone
chose `.LQeN1`'s far spot under the other costs. Then the plan is settled:
the padded copy is assembled and read as the verbose check reads it, and
a group whose heads cost more where they landed than its plan bought is
planned again, at a spot no jump crosses where it has one left and otherwise
at the same spot with the shift it was moved by folded into its residues,
a pad that has grown a jump keeping it grown, up to three rounds; a head
can cost more than its plan only by being moved, every dearer residue being
inside the budget. The verbose report says how many rounds, how many groups,
and which are still off by this cost; its straddle count stays on the lines
criterion, so under this cost a head straddling beyond the plan is one
the pad moved inside the free band, not one off the plan. On Run 38's two
halves, built from the run's own recipes with the switch added: two rounds
and one group planned again on each, 56546 and 61790 pad bytes against
the exit span's 33297 and 32586, 38 and 33 short loops straddling by the
lines criterion and one on each beyond the plan, the three fill heads read
at residue 0 on both, the two `fillStage2`s' and `u1`'s, the fill cell
on `stretch-wide-2xM` at 9.6 to 10.0 million cycles an iteration on both
halves where the run read 11.7 to 12.9, and `check` green with its log
byte-identical. A basis change, so off by default; wants `LOOP_DEADSPOT=1`
beside it and refuses without; stands alone as the block rules do. Its
controls are in `defects.json`: the back edge's rules on the rotated pair, the
spot and the rounds on a group whose every spot a jump crosses.

Its defects are kept as cases in `defects.json`: the switch read for
truth, the head after a zero-operand instruction, the pad's announcement,
the empty `PAD_BYTES`, for the dead-spot form the pad's place, the table
kept with its label and the rotated pair's order, and for the three costs
above the fill's shape under each, a cut the entry count and the block
rules keep and the exit span pads, and the refusal without the dead-spot
form. Add one there
before fixing anything here, and the proof outlives the commit.

The published copy of this is in horde-ad's
`docs/ghc-issue-no-loop-alignment.md`, filed as
[GHC work item 27668](https://gitlab.haskell.org/ghc/ghc/-/work_items/27668),
which gives it as that issue's workaround and adds a LOOP_SKEW variable for
stepping one loop through the eight positions of a line. **The two have
diverged and are not to be re-synced by editing the filed record**: what is
filed is what was filed,
and the max-skip form above postdates it. A reproducer wanting the smaller
`.text` can take this file; the issue text stands as posted.

`PAD_BYTES` is a trailing pad, here because only one `-pgma` reaches a build
and Run 11's pair needed both: its two halves are the unconditional shim and
this one, whose `.text` sizes differ by the 8192 the two growths above leave
between them, and the pad is what puts the libraries back in phase. It goes
at the end of the first module's text, so the module's own code keeps every
offset it had -- the first module it is handed, whether or not that one
carries a loop head. Until 2026-08-16 a headless first module returned
before the pad was written and the pad went to the next module with a head,
or to none at all, which is the pair out of phase and nothing said. Checked
that day on a two-file synthetic: the pad lands in the first headless module
and not in the second, where the previous version wrote it in neither and
left it owed.

**"The first module" is the first of each INVOCATION, which in a real build
is every module** -- the real assembler refuses several inputs alongside
`-c -o` (`cannot specify '-o' with '-c' ... with multiple files`), so GHC
necessarily calls `-pgma` once per module and the two-file synthetic above
exercises an arrangement no build produces. A target of two Haskell modules
therefore gets `2 * PAD_BYTES` and its libraries land where neither half
wants them. `micro` and `probe` are one module each, which is the whole of
why that is harmless here; the pad is announced on stderr as it is written,
one line per module, so a second line is the tell, and
`./loop-offsets.py --library A B` is what settles the phase either way.
Found 2026-08-17 by review.

How the number is derived, since the script that once did it is gone: a pair
must not move the libraries, no shim on `-pgma` reaching them, so anything
that changes `.text`'s size displaces everything linked after it -- aligning
grew it by 12 KB and moved 856 of 867 library loops. Matching the size alone
does not repair that: it left the delta at 32 mod 64, which is the worst
shift a line admits. The pad is therefore derived in two steps, the size
difference and then the residual phase, and the result is checked rather
than assumed -- `./loop-offsets.py --library A B`, which is what reports how
far two halves agree about where the libraries sit. Here PAD_BYTES=8192
needs neither correction: it shifts the libraries rigidly, by 256 or four whole lines, on
29318 of the 29449 `.text` symbols the two halves share, 100.0% of them in
phase. **Read that off `nm`, symbol by symbol, and not off the loop-based
phase.** An earlier max-skip build wanted a correction the two steps do not
cover -- equalising the size left the libraries in two populations 8 bytes
apart, the linker aligning an input section between them, so the pad's own
size mod 16 decided whether they moved together. The loop-based figure said
only that something was wrong (86%); the symbol tables said what, two
populations with the boundary at one address, which is what a third step
would have to be derived from.

This is what Run 10's aligned half was built with, unconditionally, and what
Run 11's `micro-maxskip` half is built with at the max-skip form above;
README.md's run procedure has the build and check sequence, and the halves
must not be rebuilt between them.

Measured on the suite (2026-08-10, `Main.hs` at the Run 10 roster,
-fspec-constr) in the unconditional form: 395 loop heads aligned in the
assembly, which in the binary leaves 100 of 101 short self-loops of Main's own
code at offset 0 and none of them straddling, against 50 straddling of 115
without it -- `loop-offsets.py --survey` counts that population, and the
shim's own 395 counts labels rather than loops. `micro check` green in both
forms: 45 shapes at agree=True and none at agree=False, and the two halves'
`check` logs byte-identical, agreement being a property of the strategies and
not of where their loops landed.

**Those two survey populations differ in size for a reason that is the
disassembler's, not the shim's** (2026-08-11). 115 against 101 is not fourteen
loops removed: Main carries 1580 backward jumps unaligned and 1583 aligned,
so the loop structure is untouched, while targets that `objdump -d` fails to
decode as an instruction start go 613 to 777. A linear sweep over
tables-next-to-code re-synchronises differently once code shifts by arbitrary
NOP runs, so the aligned binary is simply harder to read; lifting the survey's
64-byte cap shows the loss spread across every span bucket, which rules out
padding having inflated loops past a line. So *none straddling* is a
statement about a sample alignment makes smaller. The claim is sound in the
form this script can make it -- unconditionally every head it aligned is at
offset 0 by construction and the only ones it skips are the INSTR guard's,
and under max-skip every head it left alone was measured not to need moving
-- and that is where completeness should be argued, with the survey as
corroboration. README.md's floor section carries the same correction.

**Pad only between two instructions -- looking through the lines that emit
none.** The first version of this aligned every `.L` label a backward jump
targeted, which is 928 of them, and the binary it produced failed `check` on
the first shape with `index out of bounds (-1378,324)`. GHC's
tables-next-to-code puts an info table immediately before a return point,
which is also a local label, and a `.p2align` inserted there separates the
table from the code it belongs to. Requiring the preceding line to be an
instruction drops the count to 395 and fixes it. Requiring it *literally*
made this blind under `-g`, which is the second half of the rule and was
found on 2026-08-13: GHC then closes every basic block with `_end` and
`_proc_end` labels, so a head follows a label rather than an instruction and
every site was dropped -- **0 of a `-g3` assembly's heads against 395 of the
plain one's**, and the build came out unaligned in silence, no short loop at
offset 0, 41 straddling, two of them timed fills. A table's last line is a
`.quad` or a `.long`, so a label and a `.loc` are read past and the guard
asks its question of the last line that emits a byte. That form fires only
where the file carries `.loc`, for the reason `sites` records: it is not
inert on a plain build, and moving one is a basis change this is not the
place to make. The control is two fresh builddirs -- a shim change reaches
nothing without one, `-fforce-recomp` included -- and the max-skip half
comes out md5-identical under the two forms, each printing 395, while the
`-g3` build goes from 0 to 421. Loops whose head
follows a table are therefore left unaligned -- and the survey above says
that costs nothing here, none of the skipped heads being a short loop that
would have straddled. That failure is also this script's non-vacuity proof: the
suite's own `check` distinguishes a working build from a broken one, so a
green `check` here means something -- and it is the gate for the max-skip form
too, offsets alone being what a mispadded binary still gets right.
"""
import bisect
import collections
import os
import re
import subprocess
import sys
import tempfile


def switch(name):
    """An on/off variable: unset, empty and `0` are off, anything else on.

    `bool(os.environ.get(name))` is true for any value at all, so
    `LOOP_MAXSKIP=0` built the max-skip form: set that way, the version
    before this announced a max-skip budget where the recipe had asked for
    the unconditional one. A default is the one thing a pair's note cannot
    record and every half therefore sets what it wants explicitly, which is
    exactly the recipe that spells the unconditional half `LOOP_MAXSKIP=0`
    and got the other one under its name. Found 2026-08-17 by review.
    """
    return os.environ.get(name, '') not in ('', '0')


def number(name, default):
    """A variable that carries a number, empty reading as unset.

    These are parsed at import, outside `main`'s "never break a build over
    this" handler, so `PAD_BYTES=` -- which is what `PAD_BYTES=$PAD` spells
    with `PAD` unset, and what `switch` above reads as off -- raised a
    ValueError before the real assembler was ever reached and killed the
    compile with a traceback out of the shim. Found 2026-08-17 by review.
    A value that is not a number still kills the compile, and should: the
    recipe asked for something this cannot do -- in one line naming the
    variable and its value rather than a traceback, under the handler that
    `defect-lint.py` asks of a parse at import. Found
    2026-08-22 by review.
    """
    try:
        return int(os.environ.get(name) or default)
    except ValueError:
        sys.exit('align-as: %s=%r is not a number; the recipe asked for'
                 ' something this shim cannot do'
                 % (name, os.environ.get(name)))


REAL = os.environ.get('REAL_AS', '/usr/bin/gcc')
ALIGN = str(number('LOOP_ALIGN', 6))
MAXSKIP = switch('LOOP_MAXSKIP')
LOOKTHROUGH = switch('LOOP_LOOKTHROUGH')
NOOVERLAP = switch('LOOP_NOOVERLAP')
DEADSPOT = switch('LOOP_DEADSPOT')
EXITSPAN = switch('LOOP_EXITSPAN')
ENTRIES = switch('LOOP_ENTRIES')
BLOCKRULES = switch('LOOP_BLOCKRULES')
SETTLED = switch('LOOP_SETTLED')
PIN = os.environ.get('LOOP_PIN', '')
TRACE = os.environ.get('LOOP_TRACE', '')   # a head label: its group's plan, on stderr
WINDOW = number('LOOP_WINDOW', 64)
ENTRY_OPS = number('LOOP_ENTRY_OPS', 8)
VERBOSE = switch('ALIGN_AS_VERBOSE')
PAD = number('PAD_BYTES', 0)
BOUND = 1 << int(ALIGN)
if (EXITSPAN or ENTRIES or BLOCKRULES or SETTLED) and not DEADSPOT:
    sys.exit('align-as: LOOP_EXITSPAN, LOOP_ENTRIES, LOOP_BLOCKRULES and'
             ' LOOP_SETTLED are'
             ' costs of the dead-spot planner and want LOOP_DEADSPOT=1 beside'
             ' them; the recipe asked for something this shim cannot do')
if PIN and not DEADSPOT:
    sys.exit('align-as: LOOP_PIN is a knob of the dead-spot planner and'
             ' wants LOOP_DEADSPOT=1 beside it')
if PIN and (':' not in PIN or not PIN.rsplit(':', 1)[1].isdigit()):
    sys.exit('align-as: LOOP_PIN=%r is not LABEL:RESIDUE' % PIN)
if ENTRIES and (WINDOW < 1 or BOUND % WINDOW or ENTRY_OPS < 1):
    sys.exit('align-as: LOOP_WINDOW=%d LOOP_ENTRY_OPS=%d: the window must'
             ' divide the alignment boundary of %d bytes and an entry must'
             ' hold an instruction; the recipe asked for something this'
             ' shim cannot do' % (WINDOW, ENTRY_OPS, BOUND))
LABEL = re.compile(r'^(\.L\w+):')
JUMP = re.compile(r'^j\w*\s+(\.L\w+)\b')
# A mnemonic, not a directive or label -- with no operand as much as with
# one. Requiring the whitespace made `ret`, `nop`, `cqto`, `cltq`, `leave`
# and `ud2` fail the guard, so any head following one was dropped and
# nothing said so; verified on a synthetic whose head follows `ret`, which
# read "0 loop head(s)". Found 2026-08-17 by review. What it moves here is
# nothing: on that day's Main.hs at plain -O1 the two forms admit the same
# heads, 391 of them -- not the 395 above, which is a -fspec-constr build
# of an earlier file -- the assembly's 44 bare mnemonics all being `cqto`
# and none of them sitting before a head. The count `rewrite` now returns
# is what would have said so, the verbose line having counted only what it
# aligned.
#
# TO RE-MEASURE THAT after a Main.hs change, since it is a fact about one
# assembly and not about this file. Build keeping the input this shim is
# handed, and count the sites under each form -- `sites` is importable,
# `main` being guarded:
#
#     cabal build micro --builddir=dist-sfiles \
#       --ghc-options="-keep-s-files"        # leaves Main.s beside Main.hs
#     python3 -c "import importlib.util as u; \
#       m=u.module_from_spec(s:=u.spec_from_file_location('a','align-as.py')); \
#       s.loader.exec_module(m); \
#       src=open('Main.s').read().split(chr(10)); \
#       h=m.heads_of(src); print(len(h), len(m.sites(src,h)))"
#
# then `rm -rf dist-sfiles Main.s`, a stray builddir being what put
# unpacked sources under `hlint .` once.
INSTR = re.compile(r'^[a-z][a-z0-9.]*(?:\s|$)')
BYTELESS = re.compile(r'^(?:[\w.$]+:|\.(?:loc|file|cfi_\w+)\b.*)$')  # no bytes
UNCOND = re.compile(r'^(?:jmp|ret|ud2|hlt)\b')      # nothing falls through
EXITEND = re.compile(r'^(?:j\w*|ret|ud2|hlt)\b')     # where a fall-through exit ends
ALIGNDIR = re.compile(r'^\.(p2)?align\s+(\d+)')
PROBE = 'apLoop'          # apLoopHead_<line>, apLoopEnd_<line>_<k>_<n>
DS = 'dsProbe'            # dsProbe{H,A,B,D,Q}_<line>, dsProbeE_<head>_<line>
NEAREST = 16              # dead spots tried per group, nearest first


def heads_of(src):
    """The `.L` labels some later instruction jumps backwards to."""
    seen, heads = set(), set()
    for line in src:
        s = line.strip()
        m = LABEL.match(s)
        if m:
            seen.add(m.group(1))
            continue
        m = JUMP.match(s)
        if m and m.group(1) in seen:     # jumps back: its target is a loop head
            heads.add(m.group(1))
    return heads


def edges_of(src):
    """head label -> (its line, the line of every jump back to it).

    `heads_of` answers WHICH labels are heads and throws away where, which
    is all the at-head alignment needs and not enough to say whether a pad
    at one head is paid by another loop, nor to measure the loops.
    """
    seen, back = {}, collections.defaultdict(list)
    for i, line in enumerate(src):
        st = line.strip()
        m = LABEL.match(st)
        if m:
            seen.setdefault(m.group(1), i)
            continue
        m = JUMP.match(st)
        if m and m.group(1) in seen:
            back[m.group(1)].append(i)
    return {h: (seen[h], js) for h, js in back.items()}


def spans_of(src):
    """head label -> (its line, its furthest backward jump's line)."""
    return {h: (i, max(js)) for h, (i, js) in edges_of(src).items()}


def overlapped(spans):
    """The heads whose pad another loop pays for, by the containment test.

    A pad goes in FRONT of a head, so it is executed by whatever cycles run
    through that point. For ordinary nesting -- an inner head inside an
    outer cycle -- that is the trade this script exists to make: one pad per
    outer iteration to align the inner loop. The bad case is the other
    shape, a head whose own cycle BEGINS inside another's and ENDS after it,
    `a < h < b < j`: the pad then sits on the other loop's back-edge path
    and is paid at ITS trip count, which is not the padded loop's and may be
    orders larger.

    It is a real shape and not a corner: GHC rotates an inner loop so its
    test is at the bottom, and an enclosing loop re-enters at that test, so
    the inner loop's latch IS the outer loop's head. On the assembly this
    file was written for, 331 of 1172 heads are in that position.
    """
    return {h for h, (i, j) in spans.items()
            if any(a < i < b < j for a, b in spans.values() if (a, b) != (i, j))}


def exits_of(src, edges):
    """head label -> the line of the first jump on the fall-through path
    after its last back edge: the loop's exit test, which a loop that
    turns over once per entry executes as often as its body. None where
    a table, a section change or the file's end comes first, and none
    where the last back edge is an unconditional jump, nothing falling
    through it: the bytes after it are another block's, and until
    2026-09-15 they were read as the exit and charged."""
    out = {}
    for h, (i, js) in edges.items():
        if UNCOND.match(src[max(js)].strip()):
            continue
        for k in range(max(js) + 1, len(src)):
            s = src[k].strip()
            if not s or s.startswith('#') or BYTELESS.match(s):
                continue
            if s.startswith('.'):        # a directive: a table or a section
                break
            if EXITEND.match(s):
                out[h] = k
                break
    return out


def instr_lines(src, edges, exits):
    """The instruction lines of every head's cycle, head through exit."""
    out = set()
    for h, (i, js) in edges.items():
        for k in range(i, exits.get(h, max(js)) + 1):
            if INSTR.match(src[k].strip()):
                out.add(k)
    return out


def instr_index(sym):
    """The instruction labels' lines in order with their addresses, read
    off the symbol table once: `segments` then takes a head's slice by
    bisection rather than scanning every symbol per head, which is what
    made a build with instruction labels take twelve minutes for one."""
    lines = sorted((int(k.split('_')[1]), v) for k, v in sym.items()
                   if k.startswith(f'{DS}I_'))
    return [ln for ln, _ in lines], [v for _, v in lines]


def segments(index, i, j, x, a, end_body, end_exit, mnemonic):
    """A head's cycle as two lists of (start, end, mnemonic) from the
    head, body through the back edge on line `j` and exit through line
    `x`, each instruction ending where the next begins."""
    lines, addrs = index
    lo = bisect.bisect_left(lines, i)
    hi = bisect.bisect_right(lines, x if x is not None else j)
    at = [(addrs[n] - a, lines[n]) for n in range(lo, hi) if addrs[n] >= a]
    body, exit_ = [], []
    for n, (start, line) in enumerate(at):
        if line <= j:
            end = at[n + 1][0] if n + 1 < len(at) and at[n + 1][1] <= j else end_body
            body.append((start, end, mnemonic[line]))
        else:
            end = at[n + 1][0] if n + 1 < len(at) else end_exit
            exit_.append((start, end, mnemonic[line]))
    return body, exit_


def entry_cost(segs, r):
    """Entries the cycle's segments need at residue `r` beyond their least:
    each cut at a window boundary by ending byte, a piece charged one entry
    per ENTRY_OPS instructions. Instructions and not fused ops, which fit
    the sweep of 2026-09-15 better, at 51 offsets of 64 against 48 on
    its first run."""
    tot = 0
    for seg in segs:
        if not seg:
            continue
        pieces = collections.Counter((r + end - 1) // WINDOW for _, end, _ in seg)
        tot += (sum(-(-n // ENTRY_OPS) for n in pieces.values())
                - -(-len(seg) // ENTRY_OPS))
    return tot


FUSABLE = {'cmp', 'test', 'add', 'sub', 'and', 'or', 'xor', 'inc', 'dec',
           'cmpq', 'cmpl', 'testq', 'testl', 'addq', 'addl', 'subq', 'subl',
           'andq', 'andl', 'orq', 'orl', 'xorq', 'xorl', 'incq', 'incl',
           'decq', 'decl'}
HEAD_TAIL = 8             # a head this close to the line's end pays a cycle


def is_cond(mn):
    return mn.startswith('j') and mn != 'jmp'


def prepared(segs):
    """The per-segment figures `block_cost` needs at every residue, taken
    once: instruction starts, ends and mnemonics, the op count less fused
    pairs, and the taken branch's own bytes. A build prices 1874 heads at
    64 residues each, so what is per segment and not per residue is done
    here -- 419 of 452 seconds went to redoing it, profiled 2026-09-15."""
    out = []
    for seg in segs:
        if not seg:
            continue
        starts = [s for s, _, _ in seg]
        ends = [e for _, e, _ in seg]
        mns = [m for _, _, m in seg]
        fusedpairs = sum(1 for x, y in zip(mns, mns[1:])
                         if x in FUSABLE and y.startswith('j'))
        last = mns[-1]
        fused = len(seg) >= 2 and mns[-2] in FUSABLE and is_cond(last)
        prev = [n for n in range(len(seg) - 1) if mns[n].startswith('j')
                and not (fused and n == len(seg) - 2)]
        out.append(dict(starts=starts, ends=ends, mns=mns,
                        ops=len(seg) - fusedpairs, last=last, fused=fused,
                        pair_start=starts[-2] if fused else starts[-1],
                        prev_end=ends[prev[-1]] if prev else None))
    return out


def block_cost(segs, r):
    """Front-end cycles of a cycle placed with its head at residue `r`,
    `probe-fetch-model.py`'s rules as fitted on 2026-09-15: fetch blocks
    over the dispatcher's floor, plus the penalties the docstring lists,
    whole where the blocks bound the loop and halved otherwise. `segs` is
    `prepared`'s list, the body first; each segment ends in its taken
    branch and every branch inside it is taken not to be."""
    ops, blocks, whole, half = 0, 0, 0, 0.0
    for n_seg, sg in enumerate(segs):
        ends, starts = sg['ends'], sg['starts']
        ops += sg['ops']
        lines = {(r + e - 1) >> 6 for e in ends}
        blocks += len(lines)
        if (r + starts[0]) >> 6 != (r + ends[0] - 1) >> 6:
            blocks += 1                              # the empty block left
        if n_seg == 0 and r % 64 >= 64 - HEAD_TAIL:
            whole += 1                               # a head near the end
        last_line = (r + ends[-1] - 1) >> 6
        whole_in_last = 0
        for n in range(len(ends) - 1, -1, -1):
            if (r + ends[n] - 1) >> 6 != last_line:
                break
            if (r + starts[n]) >> 6 == last_line:
                whole_in_last += 1
        last = sg['last']
        if is_cond(last):
            lb = r + ends[-1] - 1
            cut = (r + sg['pair_start']) >> 6 != lb >> 6
            if not cut and sg['prev_end'] is not None:
                cut = (r + sg['prev_end'] - 1) >> 6 != lb >> 6
            if cut:
                whole += 1
            if not sg['fused']:
                half += 0.5
            if len(lines) > 1 and whole_in_last <= 3 and not cut:
                half += 1
        elif last == 'jmp' and whole_in_last <= 1:
            half += 1
    floor = max(ops / 6.0, blocks)
    w = 1.0 if blocks >= ops / 6.0 else 0.5
    return floor + w * (whole + half / 2.0)


def branch_cost(segs, r):
    """Whole cycles the back edge's own bytes cost at residue `r`: the
    three rules the sweep of 2026-09-22 fixed on Run 38's fill loop, the
    docstring's settled section. The branch starting on a 16-byte
    boundary or crossing one; the branch starting in the first eight
    bytes of a line; the branch starting in its last four. `segs` is
    `prepared`'s list and the body's last instruction is the back edge.
    The exit's taken branch showed none of the three on that loop, so
    it is left alone."""
    sg = segs[0]
    s, e = r + sg['starts'][-1], r + sg['ends'][-1]
    cost = 0
    if s % 16 == 0 or s // 16 != (e - 1) // 16:
        cost += 1
    if 1 <= s % 64 <= 7:
        cost += 1
    if s % 64 >= 60:
        cost += 1
    return cost


def sites(src, heads):
    """Where a directive would go: (line index, label), in source order.

    The INSTR guard is the correctness half of this script rather than a
    tuning knob -- the docstring above has the `check` failure that put it
    here -- so the sites are settled before any length is measured, and the
    probe carries a symbol at exactly these and no others.

    What it asks is whether an info table ends immediately before this head,
    and a table's last line is a `.quad` or a `.long`, so the lines to read
    past are the ones that emit no bytes at all: another label, and the `.loc`
    a `-g` build interleaves. That is what makes the guard readable under
    `-g`, where every head follows the previous block's `_end`/`_proc_end`
    labels rather than an instruction.

    **The look-through is switched on by the file, and a `-g`-less assembly
    keeps the literal form byte for byte.** On the plain assembly the two
    forms differ: 422 heads against 395, and the extra 27 are one shape of
    loop rather than a scattering -- a pre-tested loop, whose head carries
    the block's label as well as its own, two labels at one address. What
    that does to the binary is **one pad**, a directive being a budget rather
    than a padding: of the 395 the assembler pads 156, 3941 bytes at a median
    of three multi-byte NOPs each, and with the 27 it pads 157, 3988 bytes.
    Twenty-six are declined; one fires and moves everything after it by 47
    bytes. So the cost is not the NOPs, it is that re-rolling placement
    re-bases every figure this README has published for a reason no strategy
    changed, and what the extra alignment buys is unmeasured. So it is not
    taken on the way past, and `LOOP_LOOKTHROUGH=1` is how a run asks for it
    -- Run 13's other half, which is what prices it. An
    assembly carrying `.loc` is a `-g` one, is nobody's basis (README's open
    list has why a `-g3` build is never timed), and gets the correct form;
    everything else is left exactly as it was.
    """
    out, prev = [], ''
    look = LOOKTHROUGH or any(l.lstrip().startswith('.loc') for l in src)
    for i, line in enumerate(src):
        s = line.strip()
        m = LABEL.match(s)
        if m and m.group(1) in heads and INSTR.match(prev):
            out.append((i, m.group(1)))
        if s and not s.startswith('#') and not (look and BYTELESS.match(s)):
            prev = s
    return out


def probe_cmd(args, path, ps, po):
    """The invocation we were handed, aimed at the probe copy instead."""
    cmd = [ps if a == path else a for a in args]
    if '-o' in cmd:
        cmd[cmd.index('-o') + 1] = po
    else:
        cmd += ['-o', po]
    return [REAL] + cmd


def no_lengths(path, why):
    """Say that this module fell back wholesale, and hand back no lengths.

    A head the probe could not price falls back on its own and is ordinary,
    which is what the verbose line counts. EVERY head falling back is not:
    it is the max-skip half built as the unconditional one under the name
    of the other, which is the failure `switch` above records by its own
    route -- so it is said unconditionally, a build being where nobody is
    reading a verbose flag.
    """
    print(f'align-as: {path}: {why}, so no head has a measured length and'
          ' every one takes the unconditional directive -- this module is'
          ' not the max-skip form', file=sys.stderr)
    return {}


def symbols(obj, want):
    out = {}
    got = subprocess.run(['objdump', '-t', obj], capture_output=True,
                         text=True)
    if got.returncode != 0:
        print(f'align-as: objdump -t {obj} exited {got.returncode}:'
              f' {got.stderr.strip() or "(no stderr)"}', file=sys.stderr)
        return out
    for line in got.stdout.split('\n'):
        f = line.split()
        if len(f) >= 2 and f[-1].startswith(want):
            try:
                out[f[-1]] = int(f[0], 16)
            except ValueError:
                pass
    return out


def lengths(src, st, args, path):
    """Each site's loop length, by assembling a probe copy and measuring it.

    A probe carries an ordinary local symbol at each head and one after each
    backward jump that targets it; `L` is then the smallest head-to-end
    distance the symbol table reports, which is the innermost loop at that
    head and is exactly what a disassembler would have to reconstruct.
    Symbols occupy no bytes, so the probe lays out as the real assembly will
    -- and `L` would survive a shift anyway, which is why it is the quantity
    measured here and `p` is left to the assembler.

    Returns {label: L}; a label absent from it is one the probe could not
    price, and the caller falls back to the unconditional directive for it.
    """
    if not MAXSKIP:
        return {}
    at = dict(st)
    back = {lab: i for i, lab in st}
    ends = collections.defaultdict(list)
    for j, line in enumerate(src):
        m = JUMP.match(line.strip())
        if m and m.group(1) in back:
            ends[j].append(m.group(1))
    out = []
    for i, line in enumerate(src):
        if i in at:
            out.append(f'{PROBE}Head_{i}:')
        out.append(line)
        for k, lab in enumerate(ends.get(i, ())):
            out.append(f'{PROBE}End_{back[lab]}_{i}_{k}:')
    sym = probe(out, args, path, PROBE)
    if sym is None:
        return no_lengths(path, 'the probe copy did not assemble')
    if not sym:
        return no_lengths(path, 'the probe object carries no probe symbol')
    span = {}
    for name, a in sym.items():
        if not name.startswith(f'{PROBE}End_'):
            continue
        i = name.split('_')[1]
        h = sym.get(f'{PROBE}Head_{i}')
        if h is None or a <= h:      # a jump that does not run backwards
            continue
        if i not in span or a - h < span[i]:
            span[i] = a - h
    return {lab: span[str(i)] for i, lab in st if str(i) in span}


def probe(text, args, path, want):
    """Assemble a probe copy and read its symbols: None if it did not
    assemble, {} if it carries none with the prefix asked for."""
    with tempfile.TemporaryDirectory(prefix='align-as-') as tmp:
        ps, po = os.path.join(tmp, 'probe.s'), os.path.join(tmp, 'probe.o')
        with open(ps, 'w') as f:
            f.write('\n'.join(text))
        if subprocess.call(probe_cmd(args, path, ps, po),
                           stdout=subprocess.DEVNULL,
                           stderr=subprocess.DEVNULL):
            return None
        return symbols(po, want)


def extra(p, ln):
    """Lines a loop of length `ln` at offset `p` spans beyond its least."""
    p %= BOUND
    return (p + ln - 1) // BOUND - (ln - 1) // BOUND


def costs_more(got, plan):
    """Whether the tier costs a group's heads landed at exceed those its
    plan bought, the settling rounds' test of a group the pad moved.

    In the order `choose` ranks them, the first tier that differs by more
    than the tolerance deciding. The tolerance added to every tier and the
    tuples compared (2026-09-25, by review) let an equal tier 0 fall below
    its padded self and decide alone, so an outer head or a long loop the
    pad moved was never planned again. Case:
    `settled-rounds-see-only-the-short-loops`.
    """
    for g, p in zip(got, plan):
        if g > p + 1e-9:
            return True
        if g < p - 1e-9:
            return False
    return False


def dead_spots(src):
    """-> (lines a pad may follow, {align line: its bytes}), `.text` only.

    A pad after an unconditional transfer is reached by no path: the only
    way to the byte after it is a label, which comes after the pad. The
    first `.section .text` line is a spot too, so that a head before any
    jump has one. An `.align` in `.data` moves no code, hence the section
    tracking; GHC's are `.align 8` before each info table, and they are
    what the planner has to see between a spot and a head.
    """
    intext, dead, aligns = False, [], {}
    for i, line in enumerate(src):
        st = line.strip()
        if st.startswith('.section') or st == '.text':
            intext = st.startswith('.section .text') or st == '.text'
            if intext and not dead:
                dead.append(i)
            continue
        if not intext:
            continue
        if UNCOND.match(st):
            dead.append(i)
        m = ALIGNDIR.match(st)
        if m:
            n = 1 << int(m.group(2)) if m.group(1) else int(m.group(2))
            if n > 1:
                aligns[i] = n
    return dead, aligns


def marked(src, edges, dead, aligns, ins, exits=None, ilines=()):
    """`src` with `ins` applied and a byte-free symbol at every place the
    planner reasons about: each head, each back-edge's end, each dead spot
    on both sides of its pad, each `.align` on both sides -- and, for the
    two costs that read past the back edge, each exit's end and each
    instruction of a cycle."""
    head_at = {i: h for h, (i, _) in edges.items()}
    end_at = collections.defaultdict(list)
    for h, (i, js) in edges.items():
        for j in js:
            end_at[j].append(i)
    exit_at = collections.defaultdict(list)
    for h, x in (exits or {}).items():
        exit_at[x].append(edges[h][0])
    deadset = set(dead)
    out = []
    for i, line in enumerate(src):
        if i in head_at:
            out.append(f'{DS}H_{i}:')
        if i in aligns:
            out.append(f'{DS}A_{i}:')
        if i in ilines:
            out.append(f'{DS}I_{i}:')
        out.append(line)
        if i in aligns:
            out.append(f'{DS}B_{i}:')
        for hi in end_at.get(i, ()):
            out.append(f'{DS}E_{hi}_{i}:')
        for hi in exit_at.get(i, ()):
            out.append(f'{DS}X_{hi}:')
        if i in deadset:
            out.append(f'{DS}D_{i}:')
            out += ins.get(i, [])
            out.append(f'{DS}Q_{i}:')
    return out


def plan_dead(src, args, path):
    """-> ({line: directives to follow it}, groups, short loops left
    straddling), or None when the probe did not assemble.

    Each group of heads with no dead spot between them gets one directive
    at one of the spots before it, the nearest NEAREST tried: for every
    residue `p` the spot could be at, and every `rho` the group might want
    it moved to, the group's cost is the lines its loops would span beyond
    their least -- short loops first, the outer of a rotated pair next, long
    loops last -- and `m` is the largest pad that a `p` costing more than
    `rho` does would need, so the directive fires for exactly those. The
    `.align` between a spot and a head is applied to `p` as the assembler
    will apply it, so no rigid-distance assumption is made across one.

    Under LOOP_EXITSPAN the lines charge is taken on the exit span as
    well, and under LOOP_ENTRIES the charge is `entry_cost` instead, both
    in the tier the body's length puts the head in; the docstring above
    says what each is for. `mode` names the cost, and the verbose report
    plans every group a second time under the cost below the one in force
    and probes that plan too, to name the heads the two place differently.
    """
    edges = edges_of(src)
    dead, aligns = dead_spots(src)
    exits = exits_of(src, edges) if (EXITSPAN or ENTRIES or BLOCKRULES
                                     or SETTLED) else {}
    ilines = (instr_lines(src, edges, exits)
              if (ENTRIES or BLOCKRULES or SETTLED) else set())
    mnemonic = {k: src[k].strip().split()[0] for k in ilines}
    sym = probe(marked(src, edges, dead, aligns, {}, exits, ilines),
                args, path, DS)
    if not sym:
        return None
    L, LX, SEGS, BC, BS = {}, {}, {}, {}, {}
    index = instr_index(sym) if ilines else ([], [])
    for h, (i, js) in edges.items():
        a = sym[f'{DS}H_{i}']
        ends = [sym[f'{DS}E_{i}_{j}'] - a for j in js if sym[f'{DS}E_{i}_{j}'] > a]
        if not ends:
            continue
        L[h] = min(ends)
        x = sym.get(f'{DS}X_{i}')
        if x is not None and x - a > L[h]:
            LX[h] = x - a
        if ENTRIES or BLOCKRULES or SETTLED:
            j = max(js)
            SEGS[h] = segments(index, i, j, exits.get(h), a,
                               sym[f'{DS}E_{i}_{j}'] - a, LX.get(h, L[h]),
                               mnemonic)
            if (BLOCKRULES or SETTLED) and SEGS[h][0]:
                pre = prepared(SEGS[h])
                costs = [block_cost(pre, r) for r in range(BOUND)]
                least = min(costs)
                BC[h] = [c - least for c in costs]
                if SETTLED:
                    costs = [block_cost(pre, r) + branch_cost(pre, r)
                             for r in range(BOUND)]
                    least = min(costs)
                    BS[h] = [c - least for c in costs]
    outer = overlapped(spans_of(src))
    align_lines = sorted(aligns)
    mode = ('settled' if SETTLED else 'blocks' if BLOCKRULES
            else 'entries' if ENTRIES else 'exit' if EXITSPAN else 'plain')
    below = {'settled': 'blocks', 'blocks': 'exit', 'entries': 'exit',
             'exit': 'plain'}

    def residue(d, i, p):
        """Head line i's offset mod BOUND when the pad after d ends at p."""
        pos, cur = p, sym[f'{DS}Q_{d}']
        for a in align_lines[bisect.bisect_left(align_lines, d):
                             bisect.bisect_left(align_lines, i)]:
            pos = (pos + sym[f'{DS}A_{a}'] - cur) % BOUND
            pos = -(-pos // aligns[a]) * aligns[a] % BOUND
            cur = sym[f'{DS}B_{a}']
        return (pos + sym[f'{DS}H_{i}'] - cur) % BOUND

    labels = {}
    for k, line in enumerate(src):
        m = LABEL.match(line.strip())
        if m:
            labels.setdefault(m.group(1), k)

    def crossing(d, i):
        """Jumps between spot `d` and head line `i` whose target lies
        above the spot: the only ones a pad at `d` can lengthen."""
        n = 0
        for k in range(d + 1, i):
            m = JUMP.match(src[k].strip())
            if m and labels.get(m.group(1), i) < d:
                n += 1
        return n

    groups, last = [], -1
    for h in sorted(L, key=lambda h: edges[h][0]):
        i = edges[h][0]
        cands = dead[bisect.bisect_right(dead, last):bisect.bisect_left(dead, i)]
        if cands or not groups:
            groups.append((cands[-NEAREST:], [h]))
        else:
            groups[-1][1].append(h)
        last = i
    ins, ins_alt, chosen_by, hl_by = {}, {}, {}, {}
    banned, shift = collections.defaultdict(set), collections.defaultdict(int)

    def head_cost(hd, r, how):
        i, ln, out, lx, segs, bc, bs = hd
        if how == 'settled' and bs is not None:
            return bs[r]
        if how == 'blocks' and bc is not None:
            return bc[r]
        if how == 'entries' and segs is not None:
            return entry_cost(segs, r)
        v = extra(r, ln)
        if how == 'exit' and lx:
            v += extra(r, lx)
        return v

    def tiered(hl, residues, how):
        c = [0, 0, 0]
        for hd, r in zip(hl, residues):
            tier = 2 if hd[1] > BOUND else 1 if hd[2] else 0
            c[tier] += head_cost(hd, r, how)
        return tuple(c)

    def plan_one(g, first):
        """Plan group `g`: its directive into `ins` and its choice into
        `chosen_by`, the trace and the alternate plan on the first pass
        only. A spot the settling rounds banned is not offered."""
        cands, hs = groups[g]
        cands = [d for d in cands if d not in banned[g]]
        hl = [(edges[h][0], L[h], h in outer, LX.get(h), SEGS.get(h),
               BC.get(h), BS.get(h)) for h in hs]
        hl_by[g] = hl

        def cost(d, p, how):
            return tiered(hl, [(residue(d, hd[0], p) + shift[g, d]) % BOUND
                               for hd in hl], how)

        def choose(how):
            best = None
            for d in reversed(cands):
                costs = [cost(d, p, how) for p in range(BOUND)]
                for rho in range(BOUND):
                    c0 = costs[rho]
                    m = max(((BOUND - p) % BOUND for p in range(BOUND)
                             if costs[(p + rho) % BOUND] > c0), default=-1)
                    # Under the settled plan a spot no jump crosses wins
                    # on cost alone, then the nearer spot, a pad growing
                    # only the jumps that cross it; the other costs let
                    # the budget decide a tie, which is what chose
                    # `.LQeN1`'s far spot (the docstring).
                    key = ((c0, crossing(d, hl[0][0]), hl[0][0] - d, rho, m)
                           if SETTLED else (c0, rho, m))
                    if best is None or key < best[0]:
                        best = (key, ((c0, rho, m), d))
            return best[1]

        def directive(chosen, into):
            (c0, rho, m), d = chosen
            if m < 0:                    # no residue costs more than rho's
                return c0
            into[d] = [f'\t.p2align\t{ALIGN}, 0x90'
                       + (f', {m}' if m < BOUND - 1 else '')]
            if rho:
                into[d].append(f'\t.skip\t{rho}, 0x90')
            return c0

        chosen = choose(mode)
        if first and TRACE and TRACE in hs:
            (tc0, trho, tm), td = chosen
            i = edges[TRACE][0]
            print(f'align-as: trace {TRACE}: group {hs}, spots at lines'
                  f' {cands}, chosen spot line {td}, rho {trho}, budget {tm},'
                  f' cost {tc0}; the spot\'s raw residue {sym[f"{DS}D_{td}"] % BOUND},'
                  f' the head\'s {sym[f"{DS}H_{i}"] % BOUND};'
                  f' L {L[TRACE]}, exit span {LX.get(TRACE)}', file=sys.stderr)
            for name, table in (('block-rule', BC), ('settled', BS)):
                if TRACE in table:
                    costly = [r for r in range(BOUND)
                              if table[TRACE][r] > 1e-9]
                    print(f'align-as: trace {TRACE}: {name} costly residues'
                          f' {costly}', file=sys.stderr)
        if PIN and PIN.rsplit(':', 1)[0] in hs:
            # the pinned head's group: the nearest spot, the residue that
            # puts the head where asked, a budget that always fires
            lab, want = PIN.rsplit(':', 1)
            d = cands[-1]
            i = edges[lab][0]
            rho = next(p for p in range(BOUND)
                       if (residue(d, i, p) + shift[g, d]) % BOUND
                       == int(want) % BOUND)
            chosen = ((cost(d, rho, mode), rho, BOUND - 1), d)
            if VERBOSE and first:
                print(f'align-as: {path}: {lab} pinned at residue'
                      f' {int(want) % BOUND} by LOOP_PIN', file=sys.stderr)
        directive(chosen, ins)
        chosen_by[g] = chosen
        if first and VERBOSE and mode in below:
            directive(choose(below[mode]), ins_alt)

    for g, (cands, hs) in enumerate(groups):
        if cands:
            plan_one(g, True)

    # The plan settled against the assembler: the padded copy assembled
    # and every head read where it landed, and a group whose heads cost
    # more there than its plan bought is planned again with that spot
    # banned, the pad having moved something between it and the heads
    # that the probe's distances did not carry -- `.LQeN1`'s three jumps
    # (the docstring's settled section). A group can only cost more than
    # its plan by being moved: every residue costing more than the chosen
    # one is inside the budget and gets padded to it.
    settled = None
    if SETTLED:
        again, off, rounds = [], [], 0
        for rounds in range(1, 4):
            sym2 = probe(marked(src, edges, dead, aligns, ins, exits, ilines),
                         args, path, DS)
            if not sym2:
                break
            off = [g for g, ((c0, _, _), _) in chosen_by.items()
                   if costs_more(tiered(hl_by[g],
                                        [sym2[f'{DS}H_{hd[0]}'] % BOUND
                                         for hd in hl_by[g]], mode), c0)]
            if not off:
                break
            moved = 0
            for g in off:
                (_, rho, _), d = chosen_by[g]
                i0 = hl_by[g][0][0]
                # How far the head landed from where this spot's plan put
                # it is what the pad moved between the two; a spot no jump
                # crosses is preferred where the group has one left, and
                # otherwise the same spot is planned again with that
                # shift folded into its residues, a pad that has grown a
                # jump keeping it grown.
                delta = (sym2[f'{DS}H_{i0}'] - residue(d, i0, rho)
                         - shift[g, d]) % BOUND
                clean = [x for x in groups[g][0]
                         if x != d and x not in banned[g]
                         and not crossing(x, i0)]
                if clean:
                    banned[g].add(d)
                elif delta:
                    shift[g, d] = (shift[g, d] + delta) % BOUND
                else:
                    continue                 # nothing this round can move
                ins.pop(d, None)
                plan_one(g, False)
                moved += 1
                again.append(g)
            if not moved:
                break
        settled = (rounds, again, off)

    planned = set()
    for g, ((_, rho, _), d) in chosen_by.items():
        planned |= {h for h, hd in zip(groups[g][1], hl_by[g])
                    if hd[1] <= BOUND
                    and extra((residue(d, hd[0], rho) + shift[g, d]) % BOUND,
                              hd[1])}
    if VERBOSE:
        # The plan checked against the assembler, one more probe: what the
        # symbol table of the padded copy says every head's residue is.
        sym2 = probe(marked(src, edges, dead, aligns, ins, exits, ilines),
                     args, path, DS)
        if sym2:
            stradl = [h for h in sorted(L, key=lambda h: edges[h][0])
                      if L[h] <= BOUND
                      and extra(sym2[f'{DS}H_{edges[h][0]}'], L[h])]
            strad = len(stradl)
            padb = sum(sym2[f'{DS}Q_{d}'] - sym2[f'{DS}D_{d}'] for d in dead)
            astride = ''
            if mode != 'plain':
                stradx = sum(1 for h in LX if LX[h] <= BOUND
                             and extra(sym2[f'{DS}H_{edges[h][0]}'], LX[h]))
                astride = f', {stradx} exit span(s) astride'
            print(f'align-as: {path}: {len(L)} head(s) in {len(groups)} group(s),'
                  f' {len(ins)} dead-spot directive(s), {padb} pad byte(s);'
                  f' verified: {strad} short loop(s) straddling'
                  f' ({len(planned)} planned){astride}', file=sys.stderr)
            # A head straddling that the plan did not accept is one the
            # assembler moved off its planned residue, and naming it is
            # what turns the two counts' disagreement into a case: Run
            # 38's control half read 13 against 12, and the one was
            # `.LQeN1`, a 63-byte loop pinned free at 0 or 1 by a pad at a
            # spot fifty lines up, whose 40 bytes grew three `rel8` jumps
            # between that spot and the head to `rel32`, nine bytes the
            # spot-to-head distance did not carry (2026-09-22).
            off = [h for h in stradl if h not in planned]
            if off:
                shown = ', '.join(off[:12])
                shown += ', ...' if len(off) > 12 else ''
                print(f'align-as: {path}: {len(off)} short loop(s) straddling'
                      f' beyond the plan: {shown}', file=sys.stderr)
            if settled:
                rounds, again, left = settled
                names = ', '.join(groups[g][1][0] for g in left[:12])
                print(f'align-as: {path}: settled in {rounds} round(s),'
                      f' {len(again)} group(s) planned again'
                      + (f', {len(left)} still off the plan: {names}'
                         if left else ''), file=sys.stderr)
        # And the plan under the cost below this one, probed the same way:
        # the heads the two costs place at different residues are the ones
        # a pair of the two costs can say anything about, budgets that
        # differ without moving a head being no difference at all.
        sym3 = probe(marked(src, edges, dead, aligns, ins_alt, exits, ilines),
                     args, path, DS) if mode in below else None
        if sym2 and sym3:
            names = [h for h in sorted(L, key=lambda h: edges[h][0])
                     if sym2[f'{DS}H_{edges[h][0]}'] % BOUND
                     != sym3[f'{DS}H_{edges[h][0]}'] % BOUND]
            shown = ', '.join(names[:12]) + (', ...' if len(names) > 12 else '')
            print(f'align-as: {path}: {len(names)} head(s) the {mode} cost'
                  f' places at a residue the {below[mode]} cost would not'
                  + (f': {shown}' if names else ''), file=sys.stderr)
    return ins, len(groups), len(planned)


def pad_note(path):
    """Say where the pad went, and clear it: one module's worth an invocation.

    Unconditional, not under ALIGN_AS_VERBOSE. The pad is once per
    invocation and GHC invokes this once per module, so on a multi-module
    target it is written once per module and each half's libraries move
    further than its note records -- a second line here is the only tell a
    build gives, the docstring above having the rest.
    """
    global PAD
    print(f'align-as: {PAD} pad byte(s) appended to {path}', file=sys.stderr)
    PAD = 0


def rewrite(path, args):
    """-> (emitted with a budget, fallen back on, dropped by the guard).

    The third is what the INSTR guard refused: a head whose last
    byte-emitting line is a table entry rather than an instruction, which
    is the correctness half of this script and is meant to refuse them.
    Counted because nothing counted it -- the verbose line reports what was
    aligned, so the head count this file quotes has always been a floor
    with no way to see how far below the ceiling it sits.
    """
    with open(path) as f:
        src = f.read().split('\n')

    if DEADSPOT:
        got = plan_dead(src, args, path)
        if got is None:
            print(f'align-as: {path}: the probe copy did not assemble, so no'
                  ' head is placed -- this module is not the dead-spot form',
                  file=sys.stderr)
            ins, n = {}, 0
        else:
            ins, n, _ = got
        out = []
        for i, line in enumerate(src):
            out.append(line)
            out += ins.get(i, [])
        if PAD:
            out += ['\t.section .text', '\t.p2align 3', f'\t.space {PAD}, 0x90', '']
            pad_note(path)
        with open(path, 'w') as f:
            f.write('\n'.join(out))
        return n, 0, 0

    heads = heads_of(src)
    # Off by default and a switch for the reason LOOP_MAXSKIP is one: every
    # figure this benchmark has published was measured through this shim, so
    # padding differently is a new basis and not a bug fix.
    if NOOVERLAP:
        bad = overlapped(spans_of(src)) & heads
        heads = heads - bad
        if VERBOSE:
            print('align-as: %s: %d head(s) left alone as overlapping'
                  % (path, len(bad)), file=sys.stderr)
    st = sites(src, heads)
    dropped = len(heads) - len(st)
    if not st:
        # The pad is owed by the FIRST module this shim is handed, and a
        # module with no loop head is still that module. Returning here
        # before the PAD block below sent it to whichever later module
        # happened to have a head -- or nowhere, when none did -- putting
        # the pair's libraries out of phase with nothing said about it.
        if PAD:
            with open(path, 'a') as f:
                f.write('\n\t.section .text\n\t.p2align 3'
                        f'\n\t.space {PAD}, 0x90\n')
            pad_note(path)
        return 0, 0, dropped

    L = lengths(src, st, args, path)
    at, n, back = dict(st), 0, 0
    out = []
    for i, line in enumerate(src):
        if i in at:
            ln = L.get(at[i])
            if ln is None:
                out.append(f'\t.p2align\t{ALIGN}, 0x90')
                back += 1
            else:
                # (L-1) mod BOUND, so a loop longer than a line is moved when
                # -- and only when -- it would otherwise span one line more
                # than its length forces. It is L-1 whenever L fits a line.
                out.append(f'\t.p2align\t{ALIGN}, 0x90, {(ln - 1) % BOUND}')
                n += 1
        out.append(line)
    if PAD:
        out += ['\t.section .text', '\t.p2align 3', f'\t.space {PAD}, 0x90', '']
        pad_note(path)
    with open(path, 'w') as f:
        f.write('\n'.join(out))
    return n, back, dropped


def main():
    args = sys.argv[1:]
    n = back = dropped = 0
    for a in args:
        if a.endswith('.s') and os.path.exists(a):
            try:
                dn, db, dd = rewrite(a, args)
                n, back, dropped = n + dn, back + db, dropped + dd
            except Exception as e:           # never break a build over this
                print(f'align-as: {a}: {e}', file=sys.stderr)
    if VERBOSE:
        if DEADSPOT:
            print(f'align-as: {n} group(s) of loop heads given a dead-spot'
                  ' directive', file=sys.stderr)
        elif MAXSKIP:
            print(f'align-as: {n} loop head(s) given a max-skip budget, {back} '
                  f'without a measured length and so aligned unconditionally',
                  file=sys.stderr)
        else:
            print(f'align-as: aligned {back} loop head(s) unconditionally',
                  file=sys.stderr)
        if not DEADSPOT:
            print(f'align-as: {dropped} head(s) left alone, the guard finding'
                  f' a table rather than an instruction before them',
                  file=sys.stderr)
    return subprocess.call([REAL] + args)


if __name__ == '__main__':
    sys.exit(main())
