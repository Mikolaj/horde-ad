#!/usr/bin/env python3
"""Find a binary's copies of a hot loop and report where each lands in its
cache line -- the cheap half of the placement question.

Written for orthotope's micro-regime3 benchmark and kept there until
2026-10-06, so the README.md, Main.hs, Runs, binaries and scripts named below
are that directory's, at
https://github.com/Mikolaj/orthotope/tree/speedup-strided-tovector/micro-regime3

README.md's floor section prices a straddled copy of the 28-byte run-fill at
1.19 against a resident one, so before crediting any margin under about a
fifth to a strategy, ask this first: it is one objdump against a
quiet-machine window. Ask it first, but do not assume the answer: Run 10 read
three arms of one family at four placements each, none of them straddling in
two of the three, and their 16% stayed. Placement is the cheapest
explanation to rule out, not the likeliest to be right.

A loop copy is found structurally rather than by symbol -- a backward branch
whose target is exactly LEN bytes back, with the intervening instructions
accounting for those bytes -- and copies are then grouped by their raw bytes,
so "N byte-identical copies of one loop" is something this reads rather than
assumes. That matters because the interesting arms compile to the same worker:
the group, not the symbol, is what identifies them.

Reading the output: the copies are listed in address order, and for the
`build`/`mut-odo` group in this suite's binaries that order is
[dead, mut-odo, dead, build] -- one copy per arm is the mismatched-length
`fail` join, which cannot run on a well-formed shape, and it is the executed
one that the penalty applies to.

**Which arm owns a copy is a property of the binary, and only a `-g3` one has
it.** A plain build prints every copy under one mangled symbol, because these
arms compile to one worker and nothing per-arm survives: all eight sit inside
`Main_zdWT_info`, which spans 271 KB, and the assembly GHC hands
`align-as.py` carries 11 named labels, every one a string literal, against
18829 anonymous `.L` ones. The names are not there to emit. A `-g3` build
emits a per-block symbol (`Main_zdwgo7_svYG_entry` and siblings) with DWARF
line info, and **this tool then names each copy itself** -- `addr2line` for
the source line, the source file for the top-level binding containing it --
so the symbol column reads `fbMutOdoVecdims (Main.hs:1669)` instead. Nothing
changes for a binary carrying no line info, which is every build this README
timed before Run 13.

Read that way 2026-08-13, at `-fspec-constr` with `LOOP_MAXSKIP=1`: the
four-copy vecdims group is, in address order, `fbMutOdoVecdims`,
`fbMutOdoVecdimsAddIn`, `fbMutOdoVecdimsAddOut` and `fbMutOdoVecdimsAddBoth`,
and the pair beside it is `fbMutOdo` then `fbBuild`.
`fbMutOdoVecdimsAddBothDown` is in neither group because its loop is 24 bytes
and not 28, the count-down form's; `--len 24` finds it, and in that build it
is a singleton at offset 0.

**The two copies a `-g3` build lacks are the dead ones**, which is what the
naming establishes rather than assumes: the plain build's `build`/`mut-odo`
group has four copies and the `-g3` build's has two, and those two are the
two live arms. That confirms the `[dead, mut-odo, dead, build]` reading above
by a second route, and it is this tool's non-vacuity control for naming --
any scheme that names them must put `fbMutOdo` before `fbBuild` and must
reproduce the vecdims group in roster order.

**A `-g` build is a different program at every level, so it is a twin to read
and never a binary to time.** On the assembly GHC hands the assembler at
`-g3`, stripped of every `.loc`,
debug label and `.debug_*` section: 60056 instructions against the plain
build's 59991, of which +63 are `movq`, with register assignments differing
throughout -- register allocation and block order, not different arithmetic.
The timed loops themselves come out byte-identical, all three 28-byte groups
sharing a body across the two builds, but every offset differs and two copies
are gone. It was gated against a plain half of the same source and lost, at
5% on `build` and 3% on `mut-odo` against a 1.4% floor, which is why building
everything this way is refused, and `-g1` is no way round it -- README's open
list has both readings and what they rest on. The twin
is built beside the binary it explains, from the same source and shim:

    LOOP_MAXSKIP=1 cabal build micro --builddir=db-g3 \
      --ghc-options="-fspec-constr" --ghc-options="-g3" \
      --ghc-options="-pgma $PWD/../../horde-ad/tools/align-as.py -fforce-recomp"

and `rm -rf db-g3` with the binary afterwards, `.gitignore` covering the
builddir but not a copied-out probe binary. **Matching its copies to the
timed binary's is by the bytes of the loop body and never by proximity**,
which is what `--match` below does. The instruction window around a head,
which the hand method before it used, is not reliable everywhere: it
separates the vecdims copies at 73 to 75 of 80, and falls to 10 to 13 on the
`build`/`mut-odo` group, whose surroundings `-g3` restructured when it
dropped the two dead copies.

Non-vacuity, and it is a known-answer control rather than an assertion. It
was settled against the pad probe's binaries, reproducing every offset
README records for them -- micro-pad0 [3, 53, 59, 45], micro-pad1 [27, 13,
19, 5], micro-pad6 [19, 5, 11, 61], whose second and fourth entries are
the documented `mut-odo` and `build` offsets -- before it was pointed at a
binary whose answer was unknown, which is the whole of its warrant. Those
binaries are deleted, and so is `micro-unaligned`, which stood as the
control after them: binaries are named `<run>-<half>` from Run 12 on, and
each run's are deleted with it, so no *binary* can hold this role for
long. The live control is the current pair's recorded fills -- for Run 12,
`run12-maxskip` [11, 0, 4, 0] and [24, 8, 0, 0] against `run12-maxskippa`
[4, 0, 4, 0] and [8, 8, 4, 4] -- which this tool must reproduce before it
is read for anything new. They are in README's open list and in the pair's
own `<prefix>-pair.txt` -- written by hand, with the recipe for each half
-- so the check outlives the binaries it was born on. **Those binaries are
deleted with their run**, which is how the previous control died, so what
has to survive is the recipe the note carries: the commit is recorded, and a
rebuild that reproduces the two md5s reproduces the offsets above. Taken
whole for the first time 2026-09-11: both Run 28 halves rebuilt md5-identical
from `bdf06c8`, in a scratch directory two days after the run and from a
different working directory, so the recipe and not the path is what fixes
them. **Rebuild at the commit and never at the tip**: from the tip, whose
only build-input change was two comment hunks in `Main.hs`, the HEAD half
reproduced its `.text` byte for byte and the basis half did not, 145622 bytes
of it differing -- and yet no loop moved, every short loop coming back at the
same address and all but fourteen byte-identical, those fourteen differing
only in a rip-relative displacement, so what a failed md5 there proves is
that the source moved and not that a placement did. Re-prove this against a known
answer before pointing it at a new one.

**`--survey`'s population size is not comparable between binaries whose
layout differs**, which is the one way to misuse the mode. It counts loops
this tool can *resolve*, and `objdump -d` sweeps linearly over
tables-next-to-code, so shifting code by arbitrary padding changes where the
sweep mis-decodes: measured 2026-08-11, Main's backward jumps hold at 1580
against 1583 between the aligned and unaligned halves while targets not
decoded as an instruction start go 613 to 777, which is the whole of why one
reads 115 short loops and the other 101. The straddle count *within* one
binary is sound; a difference in the totals between two is the disassembler.

**`--survey` counts exit spans astride beside the straddlers** (2026-09-16),
the span as `align-as.py` costs it under `LOOP_EXITSPAN`: from a head
through the first jump on the fall-through path after its last back edge,
none where that edge is a `jmp`, and astride when a span of at most a line
crosses one. The shim prints its own count only under `ALIGN_AS_VERBOSE`,
which no recipe sets, so this is the reading a run has off the binary it
timed. Under `LOOP_EXITSPAN=1` it is an invariant: Run 33's two halves read
0 and 0 where Run 32's read 65 and 72, and a nonzero on a half built with
the switch says the recipe lacked it, the shim regressed, or `scan` met a
table shape it has no tell for yet, as Run 35's one astride and Run 36's
two were (2026-09-18): read the head's bytes before the recipe. It counts
a placement and not a cost.

Its defects are kept as cases in `defects.json` -- objdump's status
and addr2line's -- and a fix here wants one there first.

    ./loop-offsets.py BINARY...          # 28-byte loop, the one this README prices
    ./loop-offsets.py --len 24 BINARY    # e.g. the count-down form
    ./loop-offsets.py --survey BINARY    # every loop that could fit a line:
                                         #   the straddlers, and the exit
                                         #   spans astride (2026-09-16)
    ./loop-offsets.py --library A B      # do the two halves move the libraries
    ./loop-offsets.py --delta OLD NEW    # how far a rebuild moved the tracked
                                         #   loops: the pinning claim's reading
    ./loop-offsets.py B --match TWIN...  # name B's straddlers, and its exit
                                         #   spans astride, off -g3 twins,
                                         #   the other half's included
    ./loop-offsets.py ... --loose        # and by a register-masked signature
                                         #   where every twin's bytes refuse
    ./loop-offsets.py ... --source REV   # read a twin's names at REV's
                                         #   source, not the working tree's
"""
import argparse
import collections
import os
import re
import subprocess
import sys

INSN = re.compile(r'^\s*([0-9a-f]+):\t((?:[0-9a-f]{2} )+)\s*\t?(\S+)\s*(.*)$')
CONT = re.compile(r'^\s*([0-9a-f]+):\t((?:[0-9a-f]{2} )+)\s*$')  # bytes 8 on
SYM = re.compile(r'^([0-9a-f]+) <(.+)>:$')
JMP = re.compile(r'^j')
TARGET = re.compile(r'^([0-9a-f]+)\b')
LOC = re.compile(r'^(.*):(\d+)$')
REG = re.compile(r'%[a-z][a-z0-9]*')               # a register, for --loose
OPTGT = re.compile(r'^[0-9a-f]+ <.*>$')            # a branch's own target
TOP = re.compile(r'^([a-z]\w*)\s*(?:::|[^=]*=)')   # a top-level binding
KEYWORD = {'type', 'data', 'newtype', 'class', 'instance', 'import', 'module',
           'infix', 'infixl', 'infixr', 'foreign', 'pattern'}
LINE = 64  # the cache line, and the op cache's window on this Zen 3
UNCOND = re.compile(r'^(?:jmp|ret|ud2|hlt)')   # nothing falls through it
# A pad as objdump spells it, mnemonic and operands: `nop`, `nopl`, `nopw`
# behind any `cs` or `data16` prefixes, and the two-byte `66 90`, which it
# spells `xchg %ax,%ax`. By spelling and not by encoding: `0f 1f` takes any
# ModRM, and `nopl (%rsi)` is a pad an encoding list did not have.
PAD = re.compile(r'^(?:(?:cs|data16) )*(?:nop|xchg\s+%ax,%ax)')
HIGHBYTE = re.compile(r'%[abcd]h\b')           # GHC's codegen names none
EXITEND = re.compile(r'^(?:j|ret|ud2|hlt)')    # where a fall-through exit ends


def span_label(want):
    """What a report scanned, for its own header.

    `at most LINE B` and not `any length`: `--len 0` lifts the exact-size
    filter and NOT the cache-line cap, `scan` dropping every loop wider
    than a line whatever `want` is. The old wording read as this binary's
    whole loop count, which it is not -- `--len 128` finds loops the `any
    length` report did not contain. Same phrasing as --survey's header, and
    a function rather than an expression so that saying it wrong is
    checkable without a binary to scan.
    """
    return 'at most %d B' % LINE if want is None else '%d B' % want


def innermost(path):
    """{head address: the shortest loop starting there}.

    Every mode wants a binary's loops one per head rather than one per
    jump, an outer loop and the inner one it contains sharing a head, and
    each mode built the dict for itself in the same five lines.
    """
    heads = {}
    for f in scan(path, None):
        cur = heads.get(f['start'])
        if cur is None or f['len'] < cur['len']:
            heads[f['start']] = f
    return heads


def listing(path):
    """`objdump -d -j .text` over `path` -- or `path` itself, where it is a
    saved listing: a text file rather than ELF, carrying objdump's own
    `Disassembly of section` header. A run's binary dies at the deletion
    offer, so a case that holds one of its sites holds the listing of that
    site instead, which is the one form of it that can be tracked. Anything
    else goes to objdump, whose refusal is the answer for a file that is
    neither.
    """
    try:
        with open(path, 'rb') as f:
            head = f.read(4096)
    except OSError:
        head = b''
    if head[:4] != b'\x7fELF' and b'Disassembly of section' in head:
        with open(path) as f:
            return f.read()
    # objdump's verdict and not merely its stdout. A mistyped or missing
    # binary, or one with no `.text`, left `dis` empty and every mode then
    # read it as a binary with no loops: `--survey no-such-binary` printed
    # `0 self-loops ... at offset 0: 0, still straddling: 0` and exited 0,
    # a placement report reading as a perfect result for a file that was
    # never opened. Found 2026-08-17 by review.
    cmd = ['objdump', '-d', '-j', '.text', path]
    try:
        got = subprocess.run(cmd, capture_output=True, text=True)
    except OSError as exc:
        sys.exit('%s: %s' % (' '.join(cmd), exc))
    if got.returncode != 0:
        sys.exit('%s exited %d: %s' % (' '.join(cmd), got.returncode,
                                       got.stderr.strip() or '(no stderr)'))
    return got.stdout


def reaches(insns, k, n):
    """Whether flow from the head at `k` reaches the closing branch at `n`
    through the body's own edges: fall-through past anything but an
    unconditional transfer, plus the direct branches inside the body whose
    targets are inside it.

    A backward branch whose bytes sum is not yet a loop. `objdump -d`
    sweeps tables-next-to-code linearly, so an info table decodes as
    instructions, and a word of one can decode as a backward `js` whose
    span the bytes before it happen to fill: `run25-g912`'s survey read
    FIVE straddling self-loops in Main-compiled code where its `-g3` twin
    and every other binary read four, the fifth closed by the SRT word of
    the table in front of `$wrun` -- `0x013dd878`, whose low two bytes
    `78 d8` are `js -40` -- over a body that was a continuation's tail, a
    heap-check jump, a pad and twenty bytes of table, which control leaves
    at its second instruction. Read 2026-09-04 and named by the twin
    refusing it. It removes one to four self-loops from each of the four
    real binaries and two twins of that day, and every one inspected, on
    three of the six, is such a word behind a `jmp` and a pad; the blanket
    form, refusing any unconditional transfer inside the body, took
    fourteen real loops with them, so this one follows the flow instead.
    Survey totals recorded before 2026-09-04 are higher than this reads by
    that few, and stand as taken.

    A second shape this flow test cannot see, `run26-g912`'s sixth
    straddler of 2026-09-06: the SRT word of a return-frame table in front
    of a 29-byte continuation of `$wfbCanonVecdims` throws the sweep out of
    step for the whole continuation, so its closing `jmp` to a list
    equality is swallowed into a `(bad)` and the low bytes of the
    displacement, `71 d3`, read as `jno -45` back to the table -- a body
    with no transfer in it for the flow to leave at. The twin refused it,
    three relocated addresses and the SRT word differing. This shape's tell, which no real loop
    can carry, is a `(bad)` mnemonic inside the body: over the four Run 26
    binaries and Runs 24's and 25's four it marks this loop, one 8-byte
    body in `run25-g912` and one in Run 26's basis twin, and nothing else.
    `scan` refuses such a body since 2026-09-06, so survey totals recorded
    before then are higher by one on those three binaries and stand as
    taken.

    A third shape, one of `run28-g912`'s straddlers of 2026-09-11, which
    both of the above admit: the body is the table itself. At 0x41c9fc a layout
    word and a type word read as three `add %al,(%rax)` and an `adc`, closed
    by `78 f6` -- the low bytes of the word after them -- as `js -10`, with
    no transfer inside for the flow test to leave at and no `(bad)` for the
    filter. The real code ends ten bytes earlier at a `jmp *-0x10(%r13)` and
    a pad, and nothing in the binary branches to the head but that `js`. The
    tell is a run of four zero bytes in the body, which no real loop of the
    binaries read carries; `scan` refuses such a body since 2026-09-11. Over
    twenty binaries -- Runs 24 to 28's twins and the two pairs still on
    disk, with six rebuilds of Run 28's -- it marks twenty bodies and no
    real loop. Survey totals recorded before then are higher by one or two
    wherever it fires and stand as taken; the two STRADDLER counts it moves
    are `run28-g912`'s, from eight to seven, and Run 26's HEAD twin's, from
    six to four. Since 2026-09-18 the tell also asks for an instruction of
    two zero bytes, Run 36's basis half having read a table's `00 00 78 fc`
    as a loop astride; `zero_run` says what that moved.

    A shape of another kind, no phantom of the sweep: a backward branch into a
    block that leaves the body unconditionally, which control enters from
    the branch and never from the head. Until 2026-09-19 the flow resumed
    at any instruction some branch ANYWHERE targets, so the check after
    such a block, entered by a forward branch, carried the flow to the
    back edge and the body counted: the heap-check failure block, `movq
    $imm32,0x388(%r13)` and a jump to the collector with the check's `ja`
    branching back to it, is the common member, invisible until 2cbaeb6
    for its eleven-byte push, and run36-gheadtwopass's 0x482d4d, an error
    block entered on a negative byte count, straddled and read as the
    ninth straddler where the shim's verified line had eight. Following
    the body's own edges refuses the class and keeps what the blanket form
    lost: 22 to 39 Main loops a binary carry an unconditional transfer and
    stay, every one read in run36-gheadnospec closed by a `jmp` back to
    its head. Over the twelve run binaries on disk it
    refuses 13 to 29 Main bodies and 832 to 968 library bodies a binary,
    the statistics Quantile pair the run notes read as straddling among
    them, a `max` returning either argument; takes that half's straddling
    back to 8; holds every LOOP_EXITSPAN
    half's exit spans astride at 0, and reads Run 31's and 32's four
    halves at 66, 51, 73 and 66 for 67, 52, 75 and 68. Survey totals
    recorded between the two dates are higher and stand as taken.
    """
    inside = {insns[i][0]: i - k for i in range(k, n + 1)}
    live = [False] * (n - k + 1)
    live[0] = True
    changed = True
    while changed:
        changed = False
        for i in range(k, n + 1):
            if not live[i - k]:
                continue
            _addr, _nb, _raw, mnem, op, _sym = insns[i]
            if JMP.match(mnem):
                t = TARGET.match(op.strip())
                j = inside.get(int(t.group(1), 16)) if t else None
                if j is not None and not live[j]:
                    live[j] = True
                    changed = True
            if (i < n and not live[i - k + 1]
                    and not (mnem in ('jmp', 'jmpq') or mnem.startswith('ret'))):
                live[i - k + 1] = True
                changed = True
    return live[n - k]


def zero_run(insns, k, n, run_of=4):
    """Does this body carry `run_of` consecutive zero bytes, or an
    instruction of two, `add %al,(%rax)` -- the third site in `reaches`,
    where the body is an info table rather than code.

    Byte-aligned, and that is the point: the hex string of `10 00 00 00 01`
    holds eight zero characters and only three zero bytes. The instruction
    form is the same tell at two bytes, which no run of four can see and no
    compiler emits: Run 36's basis half read `00 00 78 fc` at 0x4a4832 as
    a four-byte loop astride, two table bytes and the low bytes of the
    word after them (2026-09-18). Neither form subsumes the other over the
    twelve run binaries on disk, so both are asked. There the instruction
    form marks five Main bodies, each a table's words, and 28 to 50 library
    bodies a binary; it moves no straddling count, and run31-nospec's exit
    spans astride, a half built without the switch, from 65 to 64.
    """
    body = ''.join(i[2] for i in insns[k:n + 1])
    run = 0
    for i in range(0, len(body), 2):
        run = run + 1 if body[i:i + 2] == '00' else 0
        if run >= run_of:
            return True
    return any(i[2] == '0000' for i in insns[k:n + 1])


def signature(insns, k, n):
    """The body with its registers masked and its branch targets dropped --
    `--match --loose`'s weaker key, and never a substitute for the bytes.

    Two builds of one arm differ in register assignment where `-g3` moved
    the allocator, which is the whole of why byte identity refuses them:
    `fillStage2`'s two runs are matched by nothing else in Run 28's pair.
    It is NOT unique, so a caller prints the family and names only what
    another key has already anchored: in that pair one signature covers
    `fillStage2Short`, `fillStage2` and `fbMutOdoVecdimsAddInLeafU2`.
    """
    out = []
    for _addr, _nb, _raw, mnem, op, _sym in insns[k:n + 1]:
        op = op.split('#')[0].strip()
        op = 'TGT' if OPTGT.match(op) else REG.sub('%R', op)
        out.append('%s %s' % (mnem, op) if op else mnem)
    return '; '.join(out)


_PARSED = {}


def parse(path):
    """The listing's instructions, read once per path: (address, byte
    count, hex, mnemonic, operands, enclosing symbol).

    An instruction past seven bytes objdump prints over two lines, the
    second carrying its address and the remaining bytes and no mnemonic.
    Until 2026-09-18 that line was read as `INSN` or not at all -- one byte
    dropped, two or more parsed as an instruction whose mnemonic was its
    last byte -- so every body holding such an instruction failed `scan`'s
    byte sum and was dropped unsaid, the `movq $imm32,disp(%rbp)` of a
    return-frame push and the `movq $imm32,0x388(%r13)` of a heap-check
    failure among them. Read whole, over the twelve run binaries on disk,
    they admit 27 to 113 Main loops and 559 to 707 library loops a binary
    and lose none; every straddling count holds but run36-gheadtwopass's,
    8 to 9, the ninth at 0x482d4d a backward branch into a block that
    tail-calls out, so the survey read one straddler there that the shim's
    verified line does not, until `reaches` refused it (2026-09-19); every
    LOOP_EXITSPAN
    half's exit spans astride hold at 0, and Run 31's and 32's four halves,
    built without the switch, read 67, 52, 75 and 68 for 64, 40, 72 and
    65. Survey totals recorded before then are lower and stand as taken.
    """
    if path not in _PARSED:
        cur, insns = None, []
        for line in listing(path).split('\n'):
            m = SYM.match(line)
            if m:
                cur = m.group(2)
                continue
            m = CONT.match(line)
            if m and insns:
                addr, nb, raw, mnem, op, sym = insns[-1]
                more = m.group(2).split()
                insns[-1] = (addr, nb + len(more), raw + ''.join(more),
                             mnem, op, sym)
                continue
            m = INSN.match(line)
            if m:
                insns.append((int(m.group(1), 16), len(m.group(2).split()),
                              ''.join(m.group(2).split()), m.group(3),
                              m.group(4), cur))
        _PARSED[path] = insns
    return _PARSED[path]


def scan(path, length):
    insns = parse(path)
    at = {i[0]: n for n, i in enumerate(insns)}
    found = []
    for n, (addr, nb, _raw, mnem, op, _sym) in enumerate(insns):
        if not JMP.match(mnem):
            continue
        t = TARGET.match(op.strip())
        if not t:
            continue
        tgt = int(t.group(1), 16)
        if tgt >= addr:
            continue
        span = (addr + nb) - tgt
        # length=None surveys every loop that could fit a line; otherwise the
        # span must be exactly the length asked for.
        if length is None:
            if span > LINE:
                continue
        elif span != length:
            continue
        k = at.get(tgt)
        if k is None:
            continue
        body = ''.join(i[2] for i in insns[k:n + 1])
        if len(body) != 2 * span:     # a jump into the middle of an instruction
            continue
        if not reaches(insns, k, n):
            continue
        # No code GHC emits decodes as (bad): a body holding one is the
        # sweep out of step over a table, the second site in `reaches`.
        if any(i[3] == '(bad)' for i in insns[k:n + 1]):
            continue
        # Nor does it carry a run of zero bytes, or an instruction of two:
        # such a body IS a table, the third site in `reaches`.
        if zero_run(insns, k, n):
            continue
        # Nor a stray REX prefix, `rex.*` in the mnemonic column: the sweep
        # entered an instruction mid-way, a fifth shape, the sixth site in
        # defects.py (2026-09-18), which carries the totals it moves.
        if any(i[3].startswith('rex.') for i in insns[k:n + 1]):
            continue
        # Nor an x87 instruction, a mnemonic beginning `f`: GHC's x86-64
        # code generator does floating point in SSE2, so the sweep decoded
        # one out of step -- Run 41's phantom astride, a `jmp` rel32's own
        # bytes `de e9 70 fc` read as `fsubrp` and `jo -4` back to it, the
        # thirteenth site in defects.py (2026-09-26).
        if any(i[3].startswith('f') for i in insns[k:n + 1]):
            continue
        # Nor a high-byte register, `%ah`, `%bh`, `%ch` or `%dh`, which
        # GHC's x86-64 code generator never names: Run 44's control read
        # the thirteenth site's shape with another mnemonic, a mov's last
        # byte and a jmp rel32's first three, `28 e9 73 fc`, as
        # `sub %ch,%cl` and `jae -4`, passing every
        # tell above -- the fourteenth site in defects.py (2026-10-04).
        if any(HIGHBYTE.search(i[4]) for i in insns[k:n + 1]):
            continue
        # Nor does it begin with a pad: a `nopl` pad after an unconditional
        # jump, closed by the info-table word after it read as a short
        # backward jcc, is a fourth table shape -- six bytes that cannot straddle,
        # so only the exit-span count met it, two on run33-gheadexit and one
        # on run32-ghead (2026-09-16). Survey totals recorded before then are
        # higher by that on those two and stand as taken. With `xchg
        # %ax,%ax` beside `nop` since 2026-09-18, when Run 36's HEAD half
        # read a two-byte pad so spelled and its table word as a four-byte
        # loop astride. Over the twelve run binaries on disk that spelling
        # marks the site, run31-o2's twin of it and one library body a
        # binary, and moves run31-o2's exit spans astride from 41 to 40.
        if PAD.match(insns[k][3] + ' ' + insns[k][4]):
            continue
        found.append({'start': tgt, 'bytes': body, 'sym': insns[k][5],
                      'len': span, 'ninsn': n - k + 1, 'mod': tgt % LINE,
                      'straddles': tgt % LINE + span > LINE,
                      'sig': signature(insns, k, n)})
    return found


def source(src, rev):
    """The lines of `src`, from the working tree or from `rev`.

    A twin's DWARF names lines in the source it was built from, so a name is
    right only while that file has not moved; `--source REV` is how a twin
    older than the tree is read. It REFUSES rather than falling back, exit 2
    being this directory's `the check did not run`.
    """
    if rev is None:
        with open(src) as f:
            return f.read().splitlines()
    d, b = os.path.split(src)
    cmd = ['git', '-C', d or '.', 'show', f'{rev}:./{b}']
    try:
        got = subprocess.run(cmd, capture_output=True, text=True)
    except OSError as exc:
        sys.stderr.write('%s: %s\n' % (' '.join(cmd), exc))
        raise SystemExit(2)
    if got.returncode != 0:
        sys.stderr.write('%s exited %d: %s\n'
                         % (' '.join(cmd), got.returncode,
                            got.stderr.strip() or '(no stderr)'))
        raise SystemExit(2)
    return got.stdout.splitlines()


def bindings(src, rev=None):
    """(line, name) for every top-level binding of a Haskell source file."""
    out = []
    for n, line in enumerate(source(src, rev), 1):
        m = TOP.match(line)
        if m and m.group(1) not in KEYWORD:
            out.append((n, m.group(1)))
    return out


def arms(path, addrs, rev=None):
    """{addr: 'fbMutOdoVecdims (Main.hs:1669)'}, or {} without line info.

    The arm is the top-level binding the line falls in, read off the source
    file `addr2line` names, so this is the source's own vocabulary rather
    than a table kept here that a rename could rot. One `addr2line` for every
    address asked about; a build with no DWARF answers `??` to all of them
    and the caller falls back to the mangled symbol.

    That fallback is the ANSWER to a question addr2line took, and it exits 0
    giving it, so the two ways it can fail to take the question at all are
    told apart from it here and said on stderr rather than read as a build
    without DWARF. Neither refuses, unlike `scan` above: what a name buys is
    legibility, and the mangled symbol is already the documented substitute.
    Measured 2026-08-17: no DWARF is `??:0` at exit 0, an unreadable file is
    exit 1, and an absent addr2line raises.

    The source read is the WORKING TREE's unless `rev` is given, so a name is
    right only while the file has not moved since the twin was built: at
    09c7211 the Run 26 twin's lines named `-u2-down`'s and `-u2-ptr`'s
    straddlers as `-u2-ptr`'s and `-u1-ptr`'s, and on 2026-09-11 the Run 27
    twin called a body `fillStage2U4 (Main.hs:3645)` that Run 28's twin, and
    the tree, call `fillStage2Short`. Two comment lines are enough: the same
    day, twins built four lines apart read `3709` and `3713` for one loop.
    So pass `--source REV` for a twin older than the tree -- the run's own
    commit, which its `<prefix>-pair.txt` records -- or run at that commit.
    """
    if not addrs:
        return {}
    cmd = ['addr2line', '-e', path] + [f'0x{a:x}' for a in addrs]
    try:
        got = subprocess.run(cmd, capture_output=True, text=True)
    except OSError as exc:
        sys.stderr.write('addr2line: %s; arms are named by their mangled'
                         ' symbol\n' % exc)
        return {}
    if got.returncode != 0:
        sys.stderr.write('addr2line -e %s exited %d: %s; arms are named by'
                         ' their mangled symbol\n'
                         % (path, got.returncode,
                            got.stderr.strip() or '(no stderr)'))
        return {}
    out = got.stdout.split('\n')
    src, named = {}, {}
    for a, loc in zip(addrs, out):
        m = LOC.match(loc.strip())
        if not m or not os.path.exists(m.group(1)):
            continue
        f, n = m.group(1), int(m.group(2))
        if f not in src:
            src[f] = bindings(f, rev)
        name = None
        for ln, nm in src[f]:
            if ln > n:
                break
            name = nm
        where = f'{os.path.basename(f)}:{n}'
        named[a] = f'{name} ({where})' if name else where
    return named


def exit_spans(path, heads):
    """{head: its exit span in bytes}, for the heads given, as align-as.py
    costs them under LOOP_EXITSPAN: from the head through the first jump
    on the fall-through path after the head's LAST back edge, and none
    where that edge is unconditional, nothing falling through it. The last
    back edge is any backward jump to the head, however long, which is why
    this reads the listing again rather than the loops `scan` kept.
    """
    insns = parse(path)
    last = {}
    for n, (addr, _nb, _raw, mnem, op, _sym) in enumerate(insns):
        if not JMP.match(mnem):
            continue
        t = TARGET.match(op.strip())
        if not t:
            continue
        tgt = int(t.group(1), 16)
        if tgt in heads and tgt < addr:
            last[tgt] = n
    out = {}
    for h, n in last.items():
        if UNCOND.match(insns[n][3]):
            continue
        for k in range(n + 1, len(insns)):
            if EXITEND.match(insns[k][3]):
                out[h] = insns[k][0] + insns[k][1] - h
                break
    return out


def astride(loops, spans):
    """The loops whose exit span, of at most a line, crosses one --
    `extra` in align-as.py, over LX."""
    return sorted((f for f in loops
                   if f['start'] in spans and spans[f['start']] <= LINE
                   and f['mod'] + spans[f['start']] > LINE),
                  key=lambda f: f['start'])


def survey(path, want='_Main_'):
    """Every self-loop of any length, and how many can still straddle.

    And every head's exit span, astride or not, since 2026-09-16: the
    count that says whether a LOOP_EXITSPAN build did what it claims, the
    shim's own line needing a rebuild under ALIGN_AS_VERBOSE to print.

    Only a loop no longer than a line can be rescued by an offset outright,
    so that is the population the count is about: the loops an alignment
    takes from two lines to one. Everything longer spans several lines in
    any build, but fewest from a line boundary, and one line fewer crossed
    is worth having too -- which is why the shim aligns every head it can
    regardless of the loop's length; that gain is real and not one this
    count certifies. The default `want` restricts this to code GHC compiled
    here rather than to the libraries linked in, which no shim on -pgma
    reaches.
    """
    mine = [f for f in innermost(path).values() if want in (f['sym'] or '')]
    at0 = [f for f in mine if f['mod'] == 0]
    strad = [f for f in mine if f['straddles']]
    print(f'{path}: {len(mine)} self-loops of at most {LINE} B in '
          f'{want}-compiled code')
    print(f'   at offset 0        : {len(at0)}')
    worst = sorted(strad, key=lambda x: -x['len'])[:10]
    cut = '' if len(worst) == len(strad) else f', {len(worst)} longest listed'
    print(f'   still straddling   : {len(strad)}{cut}')
    named = arms(path, [f['start'] for f in worst])
    for f in worst:
        print(f'      0x{f["start"]:x}  mod {LINE} = {f["mod"]:2d}, '
              f'{f["len"]} B  {named.get(f["start"]) or f["sym"]}')
    spans = exit_spans(path, {f['start'] for f in mine})
    over = astride(mine, spans)
    worst = sorted(over, key=lambda x: -spans[x['start']])[:10]
    cut = '' if len(worst) == len(over) else f', {len(worst)} longest listed'
    print(f'   exit spans astride : {len(over)}{cut}')
    print(f'      of {sum(1 for f in mine if spans.get(f["start"], LINE + 1) <= LINE)}'
          f' heads whose fall-through exit ends within a line of the head;'
          f' 0 is what a LOOP_EXITSPAN=1 build owes')
    named = arms(path, [f['start'] for f in worst])
    for f in worst:
        print(f'      0x{f["start"]:x}  mod {LINE} = {f["mod"]:2d}, '
              f'{f["len"]} B body, exit span {spans[f["start"]]} B  '
              f'{named.get(f["start"]) or f["sym"]}')


def match(timed, twins, loose=False, rev=None, want='_Main_'):
    """Name the timed binary's straddling loops off -g3 twins, by BYTE
    IDENTITY and never by address or proximity.

    Post-run step 3a owes this and did it by hand for two runs: `objdump`
    over both binaries at addresses guessed from the survey, compared by
    eye (Run 23, 2026-09-02). The rule the step states is that a loop is
    named from the twin only where the twin holds a byte-identical copy,
    and refused where it holds none or fewer copies than the timed binary
    -- which is what makes a negative honest. So: every loop the survey
    counts as straddling in `timed` is looked up by its bytes among the
    twin's loops as the survey counts them, at most a line long, which a
    byte-identical copy of one always is; a unique match is named through the
    twin's DWARF, several matches are listed, and none is a refusal said
    aloud. The count check is printed first, twin against timed, as the
    survey counts them.

    **SEVERAL TWINS ARE TRIED IN TURN, and the other half's is one of them.**
    The two compilers emit many of these bodies alike -- 85 of the HEAD
    half's 209 short loops are byte-identical to the basis half's in Run 28's
    pair -- so where a half's own twin refuses, the other half's often names
    it: four of the six refusals that run first recorded, at no build and one
    command (2026-09-11). The key is still the bytes and each twin gets its
    own count check; the first twin holding a copy is the one that names.

    `--loose` adds a second pass for what no twin holds byte-identical, over
    the register-masked `signature`. It is a WEAKER KEY and prints as one:
    the whole family rather than a name, so that a reader sees what the
    signature does not separate. In Run 28's pair it is what named
    `fillStage2`'s two runs, the broadcast one because its family has a
    single member and the stepping one because two of that family's three
    were anchored by the bytes already.
    """
    mine = [f for f in innermost(timed).values() if want in (f['sym'] or '')]
    strad = sorted((f for f in mine if f['straddles']), key=lambda f: f['start'])
    spans = exit_spans(timed, {f['start'] for f in mine})
    over = astride(mine, spans)
    print(f'{timed}: {len(mine)} self-loops of at most {LINE} B in '
          f'{want}-compiled code, {len(strad)} straddling, '
          f'{len(over)} exit span(s) astride')
    tw = []
    for t in twins:
        theirs = [f for f in innermost(t).values() if want in (f['sym'] or '')]
        short = ('  -- FEWER than the timed binary, so a name off it rests on'
                 ' its own byte match and the population comparison is'
                 ' refused' if len(theirs) < len(mine) else '')
        print(f'   twin {t} holds {len(theirs)}, '
              f'{sum(1 for f in theirs if f["straddles"])} straddling{short}')
        by_bytes = collections.defaultdict(list)
        by_sig = collections.defaultdict(list)
        for f in theirs:
            by_bytes[f['bytes']].append(f)
            by_sig[f['sig']].append(f)
        tw.append((t, by_bytes, by_sig,
                   arms(t, sorted(f['start'] for f in theirs), rev)))
    tally = collections.Counter()

    def name(f, where):
        hits, from_twin, named = [], None, {}
        for t, by_bytes, _by_sig, nm in tw:
            if by_bytes.get(f['bytes']):
                hits, from_twin, named = by_bytes[f['bytes']], t, nm
                break
        if len(hits) == 1:
            h = hits[0]
            print(f'      {where}  {named.get(h["start"]) or h["sym"]}  '
                  f'(in {from_twin} at 0x{h["start"]:x}, mod {h["mod"]}, '
                  f'{"straddles" if h["straddles"] else "fits"} there)')
            tally['named'] += 1
            return
        if hits:
            print(f'      {where}  {len(hits)} byte-identical copies in '
                  f'{from_twin}: '
                  + '; '.join(f'{named.get(h["start"]) or h["sym"]} at '
                              f'0x{h["start"]:x}' for h in hits))
            tally['named'] += 1
            return
        print(f'      {where}  NOT NAMED: no twin holds a byte-identical copy')
        if not loose:
            tally['not named'] += 1
            return
        for t, _bb, by_sig, nm in tw:
            fam = sorted(by_sig.get(f['sig'], []), key=lambda h: h['start'])
            if not fam:
                continue
            only = '  (its only member)' if len(fam) == 1 else ''
            print(f'         SIGNATURE in {t}, a weaker key: '
                  + '; '.join(f'{nm.get(h["start"]) or h["sym"]} at '
                              f'0x{h["start"]:x}' for h in fam) + only)
            tally['loose'] += 1
            return
        tally['not named'] += 1

    for f in strad:
        name(f, f'0x{f["start"]:x}  mod {LINE} = {f["mod"]:2d}, {f["len"]} B')
    # THE TALLY, which a write-up quotes and had to count by grep over the
    # lines above (Run 42): named by bytes, a --loose family only, neither.
    print(f'   straddlers: {tally["named"]} named by byte identity, '
          f'{tally["loose"]} with a --loose family only, '
          f'{tally["not named"]} with neither')
    # The exit spans astride, named the same way (2026-09-16): a block a
    # LOOP_EXITSPAN=1 half leaves empty, and otherwise the loops the switch
    # would move.
    print(f'   exit spans astride: {len(over)}')
    for f in over:
        name(f, f'0x{f["start"]:x}  mod {LINE} = {f["mod"]:2d}, {f["len"]} B'
                f' body, exit span {spans[f["start"]]} B')


def delta(old, new, length, min_copies, want='_Main_'):
    """How far a rebuild moved the tracked loops, group by group.

    The pinning claim is read at every build that brings a new timed
    function -- the fills on one build either side, before anything else
    changes -- and reading it means answering three questions of the
    tracked groups: are the mod-64 offsets preserved, does any address
    survive to the byte, and do the heads move by one constant. Nothing
    here subtracted the two address lists until 2026-09-04. Run 24's
    preparation did that arithmetic by hand and recorded the improvisation
    in its note; Run 25's improvised it again, which is two runs paying for
    a subtraction, on the reading the claim's whole record rests on.

    Groups are matched by the loop body's BYTES, which is the identity
    `--match` uses and the only one that survives a relink moving every
    address. A group on one side alone is reported as such rather than
    dropped: that is what a change of compiler produces, and Run 24's HEAD
    half grew a third group the basis did not have. WITHIN a group the
    copies are paired by address order, the i-th old head with the i-th
    new, which is what `survive to the byte` and the displacements are
    read over: a group that keeps its count while one arm's copy leaves
    and another's lands reads as displacements, and can read as an address
    surviving, with nothing here to say the pairing slipped. The `-g3`
    twins of post-run step 3a are what name a copy; this mode only counts.

    The population is `want`'s, Main-compiled code as `--match` and
    `--survey` take it, and the linked libraries' groups are left to
    `--library`: read without the filter, the statistics Quantile pair
    stood among the tracked groups on both halves of Run 25 and in the
    summary line a note would copy (2026-09-04).

    This is a reading and not a gate. It exits 0 whatever it finds, because
    what a given displacement MEANS is the README's to say -- the floor
    section's *A shim'd build does not hold its tracked loops*, where the
    claim's record lives form by form -- and a threshold here would be
    this file asserting a claim the runs are still measuring.
    """
    sides = []
    left = 0
    for path in (old, new):
        groups = collections.defaultdict(list)
        for f in scan(path, length):
            if want in (f['sym'] or ''):
                groups[f['bytes']].append(f)
            else:
                left += 1
        for fs in groups.values():
            fs.sort(key=lambda f: f['start'])
        sides.append(groups)
    og, ng = sides
    span = span_label(length)
    print(f'== {old} -> {new}: {span} loops in {want}-compiled code, '
          f'matched by body bytes; {left} library loop(s) left to --library')
    # EITHER SIDE meeting the threshold is enough. Taking it of the OLD
    # side alone dropped, in silence, exactly the group whose copy count is
    # the finding: one that grew from a copy or two to six is below the
    # threshold in `og` and present in it, so it failed the first test and
    # was excluded from the second by `k not in og`.
    keys = [k for k in og
            if len(og[k]) >= min_copies or len(ng.get(k, ())) >= min_copies]
    keys += [k for k in ng if k not in og and len(ng[k]) >= min_copies]
    preserved = moved = one_sided = recount = compared = 0
    for k in sorted(keys, key=lambda k: -max(len(og.get(k, ())),
                                             len(ng.get(k, ())))):
        a, b = og.get(k, []), ng.get(k, [])
        if not a or not b:
            where = new if b else old
            fs = b or a
            one_sided += 1
            print(f'   {len(fs)} copies, {fs[0]["len"]} B, '
                  f'{fs[0]["ninsn"]} insns, offsets '
                  f'{[f["mod"] for f in fs]} -- IN {where} ONLY')
            continue
        oo = [f['mod'] for f in a]
        nn = [f['mod'] for f in b]
        print(f'   {len(a)} -> {len(b)} copies, {a[0]["len"]} B, '
              f'{a[0]["ninsn"]} insns')
        if len(a) != len(b):
            recount += 1
            print(f'      copy COUNT moved: offsets {oo} -> {nn}')
            continue
        compared += 1
        if oo == nn:
            preserved += 1
            print(f'      every mod-{LINE} offset preserved: {oo}')
        else:
            print(f'      offsets MOVED: {oo} -> {nn}')
        kept = [f['start'] for f, g in zip(a, b) if f['start'] == g['start']]
        disp = [g['start'] - f['start'] for f, g in zip(a, b)]
        if kept:
            print('      %d address(es) survive to the byte: %s'
                  % (len(kept), ', '.join('0x%x' % v for v in kept)))
        else:
            print('      NO address survives to the byte')
        # The displacement SET and not the list: what the README's readings
        # turn on is how many constants the heads moved by, one being the
        # weakest disturbance on record and none of them a constant the
        # strongest.
        uniq = sorted(set(d for d in disp if d))
        if not uniq:
            print('      nothing moved')
        else:
            moved += 1
            print('      %d displacement(s): %s'
                  % (len(uniq), ', '.join(
                      '0x%x%s' % (v, '' if v % LINE == 0
                                  else ' (NOT a whole line)')
                      for v in uniq)))
    # TWO LINES AND NOT ONE, because the four numbers are of two kinds and
    # a single `of N group(s): ...` invited reading them as a partition
    # summing to N -- which they do not, a group both keeping its offsets
    # and moving being counted in each. The first line partitions; the
    # second states two properties over the part it makes sense of.
    # The unmatched groups are in the summary at all because without them
    # a run where nothing matched printed `0 kept every offset; 0 moved at
    # all`, which reads as `nothing moved` and means `nothing was
    # compared` -- measured on /bin/sh against /bin/cat, whose every group
    # is one-sided (2026-09-04, both faults).
    print(f'   {len(keys)} group(s) read = {compared} compared + '
          f'{recount} changed copy count + {one_sided} matched nothing '
          f'on the other side')
    if compared:
        print(f'   of the {compared} compared: {preserved} kept every '
              f'offset, {moved} moved at all')


def library(a, b):
    """How much the two halves agree about where the LIBRARIES' loops sit.

    A pair is meant to differ in the code compiled here and nowhere else,
    and this is the half of that nothing else measures: `--survey` and the
    default mode are scoped to `_Main_`, which is exactly the code a pair is
    allowed to move. The libraries are what must sit still, and a shim on
    `-pgma` never reaches them, so where they have moved it is because
    everything after a size change was displaced.

    That is not hypothetical and it is why the aligned/unaligned pairing
    needed a padding step at all: aligning grew `.text` by 12 KB, and of
    867 library symbols carrying a short loop, 856 landed at a different
    address. Matching the size alone left the delta at 32 mod 64, the worst
    shift available; matching size AND phase left 95% of the library loops
    at the same offset and 98% in the same straddle state. A pair of two
    shims, which is what is built now, has no padding step and no guarantee
    -- it has whatever its two recipes happen to give, and this is how to
    know which.

    Non-vacuous 2026-08-14 on Run 13's pair: 899 common loops, 96.8% phase
    and 98.8% straddle agreement, the same figures reached through
    the pair builder's own reading, before that script was deleted. A
    binary compared with
    itself reads 100.0% both ways, and the two counts differ from `--survey`
    because that one reports Main's loops and this one everything else.

    **Those counts were SYMBOLS**, one per symbol however many loops it
    carried, which is the keying corrected below on 2026-08-16. Run 14's
    pair reads 1723 common loops at 100.0% and 100.0% where the symbol
    keying said 953, so a count from before that date is not comparable
    with one after it, and the percentages before it covered about half
    the library.

    The self-comparison proves nothing about the percentages, reading
    100.0% by construction, and neither does an unrelated build:
    `run14-lookrts` against a `-g3` twin shares 1013 loops and still reads
    100.0% both ways, the libraries genuinely sitting still. What does
    discriminate, 2026-08-16: shifting one half's loops by a byte inside
    the reader takes the same pair to 0.0% phase and 97.8% straddle.
    """
    def heads(path):
        # Keyed by the LOOP and not by the symbol carrying it. Keying by
        # symbol collapsed every symbol holding more than one short loop
        # to whichever address iterated last -- 268 of 953 symbols here,
        # 776 of 1729 loops dropped -- so the percentages below covered
        # 55% of the library and said 953 where they had found 1729. The
        # body pairs the same code across the two halves, which is what
        # the comparison is for, and the repeat counter separates two
        # identical loops in one symbol; a loop present in one half only
        # falls out of `common` and is visible in the count.
        out, seen = {}, collections.Counter()
        for f in sorted(innermost(path).values(), key=lambda f: f['start']):
            sym = f['sym'] or ''
            if '_Main_' in sym:
                continue
            seen[sym, f['bytes']] += 1
            out[sym, f['bytes'], seen[sym, f['bytes']]] = f
        return out
    A, X = heads(a), heads(b)
    common = set(A) & set(X)
    if not common:
        sys.exit('no library symbol carries a short loop in both binaries')
    phase = 100.0 * sum(1 for s in common if A[s]['mod'] == X[s]['mod'])
    strad = 100.0 * sum(1 for s in common
                        if A[s]['straddles'] == X[s]['straddles'])
    print(f'{a} vs {b}: {len(common)} library self-loops in both')
    print(f'   same offset in line: {phase / len(common):.1f}%')
    print(f'   same straddle state: {strad / len(common):.1f}%')


def main():
    p = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    p.add_argument('binary', nargs='+')
    p.add_argument('--len', type=int, default=28,
                   help='loop length in bytes, or 0 for every length a cache '
                        'line can hold (default 28)')
    p.add_argument('--min-copies', type=int, default=2,
                   help='only report groups with at least this many copies')
    p.add_argument('--survey', action='store_true',
                   help='every self-loop of any length in this binary\'s own '
                        'compiled code, and how many can still straddle')
    p.add_argument('--delta', action='store_true',
                   help='how far a rebuild moved the tracked loops: OLD NEW,'
                        ' matched by body bytes -- the pinning claim\'s'
                        ' reading, which the run chapter asks for at every'
                        ' build bringing a new timed function')
    p.add_argument('--code', default='_Main_', metavar='SUBSTR',
                   help='--delta\'s population: loops in code whose symbol'
                        ' carries SUBSTR, _Main_ by default as --survey and'
                        ' --match take it; --code \'\' is every loop')
    p.add_argument('--library', action='store_true',
                   help='how far two halves agree about where the LINKED '
                        'libraries\' loops sit, which a pair must not move')
    p.add_argument('--match', metavar='TWIN', nargs='+',
                   help='name the binary\'s straddling loops off these -g3 '
                        'twins by byte identity, refusing where none holds '
                        'an identical copy -- post-run step 3a. Give the '
                        'other half\'s twin too: it names what a half\'s own '
                        'cannot')
    p.add_argument('--loose', action='store_true',
                   help='--match only: for what no twin holds byte-identical,'
                        ' a second pass over the register-masked signature,'
                        ' printing the family rather than a name')
    p.add_argument('--source', metavar='REV',
                   help='read a twin\'s source lines at REV rather than in '
                        'the working tree, for a twin older than the tree')
    args = p.parse_args()

    # ONE REPORT an invocation. The dispatch below is an if/return
    # chain, so `--survey --library A B` printed the library report and
    # dropped --survey without a word -- read-run.py's one-mode family,
    # found 2026-08-23 by hunting that family here. And the two
    # grouped-report knobs are refused where nothing reads them:
    # --survey scans every length up to the line by design and
    # --library keys on the loop bytes, so under either a --len or
    # --min-copies was accepted and honoured by nobody --
    # `--survey --len 24` answered with the at-most-64 report.
    if args.delta:
        # Its own mode and not a flavour of the plain report: that one takes
        # any number of binaries and prints each alone, where this one is a
        # subtraction and wants exactly two, in the order OLD NEW.
        if sum((args.survey, args.library, bool(args.match))):
            sys.exit('--delta is its own mode: not with --survey, --library'
                     ' or --match')
        if len(args.binary) != 2:
            sys.exit('--delta takes exactly two binaries, OLD then NEW')
        delta(args.binary[0], args.binary[1],
              None if args.len == 0 else args.len, args.min_copies,
              args.code)
        return
    if args.survey and args.library:
        p.error('--survey and --library are two reports, not one: the'
                ' dispatch runs --library and drops --survey without a'
                ' word')
    unread = [n for n, v, d in (('--len', args.len, 28),
                                ('--min-copies', args.min_copies, 2),
                                ('--code', args.code, '_Main_'))
              if v != d]
    if '--code' in unread:
        p.error('--code is read by --delta alone')
    if unread and (args.survey or args.library):
        p.error('%s %s read only by the grouped report: under --survey or'
                ' --library it would be accepted and honoured by nobody'
                % (' and '.join(unread),
                   'is' if len(unread) == 1 else 'are'))

    if args.match and (args.survey or args.library):
        p.error('--match is a report of its own and takes one timed binary')
    if args.match:
        if len(args.binary) != 1:
            p.error('--match TWIN takes exactly one timed binary')
        if unread:
            p.error('%s read only by the grouped report' % ' and '.join(unread))
        match(args.binary[0], args.match, args.loose, args.source)
        return
    # The two knobs --match alone reads, refused elsewhere for the reason
    # --len and --min-copies are: accepted and honoured by nobody.
    if args.loose or args.source:
        p.error('--loose and --source are read by --match alone')

    if args.library:
        # SEVERAL PAIRS IN ONE CALL, since 2026-09-15. The open entry on
        # this column asks for the whole surviving series re-derived under
        # ONE tool, because the per-run recorded figures and today's
        # reading disagree -- and a shell loop over pairs is what a session
        # wrote instead, which timed out at two minutes and had to be
        # backgrounded. An odd count is refused rather than pairing the
        # last binary with nothing.
        if len(args.binary) < 2 or len(args.binary) % 2:
            p.error('--library compares binaries two at a time, so it wants'
                    ' an even number of them; got %d' % len(args.binary))
        for i in range(0, len(args.binary), 2):
            library(args.binary[i], args.binary[i + 1])
        return

    if args.survey:
        for path in args.binary:
            survey(path)
        return

    # `--len 0` widens the grouped report to every loop a line can hold.
    # The 28 the default names is the run-fill loop this README prices, and
    # for four runs it was also the whole tracked set -- which is what the
    # NOPs question tripped over on 2026-08-14: the arms that lose most to
    # an unconditional shim carry no 28-byte loop at all, so the report
    # that would attribute the loss could not see them
    # (README.md#what-is-open). The length then varies within the report,
    # so each group prints its own.
    want = None if args.len == 0 else args.len
    for path in args.binary:
        found = scan(path, want)
        # One pass gives the count and the members together, where a
        # Counter gave the count and every group then rescanned `found`
        # for its own. Insertion order is first-encountered either way, so
        # the sort below prints what `most_common` printed.
        groups = collections.defaultdict(list)
        for f in found:
            groups[f['bytes']].append(f)
        named = arms(path, [f['start'] for f in found])
        span = span_label(want)
        print(f'== {path}: {len(found)} self-loops of {span} in '
              f'{len(groups)} distinct byte-sequences')
        # A group under the threshold is COUNTED, not merely skipped: the
        # docstring's own `--len 24` example reports a singleton, which at
        # the default of 2 printed the header and nothing else, with nothing
        # saying a group had been suppressed. Found 2026-08-17 by review.
        suppressed = 0
        for body, fs in sorted(groups.items(), key=lambda kv: -len(kv[1])):
            count = len(fs)
            if count < args.min_copies:
                suppressed += 1
                continue
            print(f'   {count} copies, {fs[0]["len"]} B, '
                  f'{fs[0]["ninsn"]} insns, '
                  f'offsets {[f["mod"] for f in fs]}')
            for f in fs:
                print(f'      0x{f["start"]:x}  mod {LINE} = {f["mod"]:2d}  '
                      f'{"STRADDLES" if f["straddles"] else "fits     "}  '
                      f'{named.get(f["start"]) or f["sym"]}')
        if suppressed:
            print(f'   {suppressed} group(s) suppressed, having fewer than '
                  f'{args.min_copies} copies: --min-copies 1 lists them')


if __name__ == '__main__':
    main()
