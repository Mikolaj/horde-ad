#!/usr/bin/env python3
"""Instructions, allocation and code a call of a benchmark binary, from
the instructions callgrind saw it execute, read against the binary's
symbols and disassembly.

Usage: python3 tools/cg-read.py allocs [--min C] BIN RUN N
       python3 tools/cg-read.py bysym [--top K] BIN_A RUN_A BIN_B RUN_B N
       python3 tools/cg-read.py incr [--top K] BIN_A RUN_A_N RUN_A_2N
                                     BIN_B RUN_B_N RUN_B_2N N
       python3 tools/cg-read.py region [--min C] BIN_A RUN_A BIN_B RUN_B SYM N
       python3 tools/cg-read.py seq [--raw] BIN RUN SYM N LO HI
       python3 tools/cg-read.py sweep BIN LO HI SAMPLES
       python3 tools/cg-read.py --self-test

Each RUN is the output of `valgrind --tool=callgrind --dump-instr=yes
--compress-strings=no --compress-pos=no` over BIN, run with `--iters N` (or
2N for incr's second run of each binary), which gives every executed
address its own count; the line after a `calls=` line, a call's inclusive
cost, is not counted. Callgrind writes an address relative to the object
holding it, so a library's addresses can lie in BIN's range: a cost line is
BIN's where the `ob=` above it names BIN --- the same file, or one of its
name where that path no longer exists --- and where its address lies in
BIN's `.text` section, whose bounds are taken from `objdump -h`; the others
count as `other`. Symbols are BIN's text symbols, from `nm -n`, an address
belonging to the nearest at or before it, and their z-encoded unit prefix
--- the package, its version and its hash or `inplace` component, any of
them, such as `orthotopezm0zi2zi0zi0zminplace_` --- is stripped, so that
one function of two builds whose unit ids differ carries one name.

Counts are over N, so one run's figures are high by (N + 2)/N where, as in
orthotope's specialisation benchmark, the harness evaluates a row twice
before its batch of N; incr's differences between the N and 2N runs are not.

allocs: the heap-pointer bumps (`add $X,%r12`, a negative X a give-back)
executed at least C times a call (0.5 by default), each with its count a
call and its place, their bytes a call summed, and the info pointers stored
relative to `%r12`, `movq $INFO,D(%r12)`, by the symbol they name.
bysym: instructions a call by symbol in two runs, the K largest
differences (14 by default) and the whole run's.
incr: the same between N and 2N calls, (I(2N) - I(N))/N for each binary,
which cancels the process's setup; the K largest differences (10).
region: the instructions of the code from symbol SYM to the next symbol
executed at least C times a call (0.25 by default) in both runs, in
address order, each `INSTRUCTION xCOUNT` with immediates of five hex digits
or more written ADDR, diffed by difflib, after the two runs' sums. SYM is a
symbol's full or stripped name, or a suffix of exactly one.
seq: one run's instructions of SYM's code run between LO and HI times a
call, with their addresses; `--raw` keeps the instruction text as objdump
prints it and names the symbol an immediate's address is, an info pointer
most often.

The disassembly is objdump's linear sweep, restarted at every executed
address a sweep did not decode as an instruction start: a sweep through one
of GHC's info tables, which sit in the code before continuations nm names
no symbol for, falls out of step with the code after it, so a sweep from a
symbol alone left executed instructions out and printed info-table bytes as
instructions (cg-read-01), and a sweep over each range of executed
addresses left heap-pointer bumps uncounted (cg-read-02).

sweep: whether a linear sweep from LO, with no restart, decodes every
address SAMPLES gives in [LO, HI) as an instruction start; SAMPLES is a
callgrind output or lines `COUNT ADDRESS`, as `perf script -F ip | sort |
uniq -c` writes them. It is the check to run before reading a hot loop off
`perf record` samples and objdump at the hot addresses: where it fails,
read the loop from callgrind's `seq` instead.

Exit 0 when the figures were printed (for sweep: every sampled address an
instruction start), 1 when sweep found a sampled address the linear sweep
missed, 2 when the run did not happen: a missing or unreadable input, a RUN
written without `--dump-instr=yes` or with `--compress-pos=yes`, objdump or
nm missing or failing, a binary without a `.text` section or text symbols,
a RUN that names no object that is its binary or none of whose addresses
lies in its text section, a SYM matching no symbol or several, or nothing
executed often enough to read.
"""

import bisect
import collections
import contextlib
import difflib
import functools
import io
import math
import os
import re
import shutil
import subprocess
import sys
import tempfile

# The self-test points these at what it needs.
OBJDUMP = 'objdump'
NM = 'nm'

# A sweep stops where the next executed address is further on than this.
GAP = 256

# A z-encoded unit id ending in the `_` before a module: one beginning with
# a lower-case letter, as base, ghczminternal and most packages', or any
# holding a `zm`, an encoded dash, which no module name carries.
UNIT = re.compile(r'^(?:[a-z][a-z0-9]*|[A-Za-z0-9]*zm[A-Za-z0-9]*)_(?=[A-Z])')
INSN = re.compile(r'\s+([0-9a-f]+):\s+(.*)')
BUMP = re.compile(r'add\s+\$(-?0x[0-9a-f]+),%r12$')
INFO = re.compile(r'movq\s+\$(0x[0-9a-f]+),(?:-?0x[0-9a-f]+)?\(%r12\)')
IMM = re.compile(r'\$(0x[0-9a-f]+)')
BIG = re.compile(r'0x[0-9a-f]{5,}|\b[0-9a-f]{6,}\b')


class Unreadable(Exception):
    """The run cannot happen; the message says why."""


def strip_unit(name):
    return UNIT.sub('', name)


def tool(cmd):
    """The stdout of cmd, or Unreadable."""
    try:
        r = subprocess.run(cmd, capture_output=True, text=True,
                           errors='replace')
    except OSError as e:
        raise Unreadable(f'{cmd[0]} could not be run: {e.strerror}')
    if r.returncode != 0:
        raise Unreadable(f'{" ".join(cmd)} exited {r.returncode}: '
                         + r.stderr.strip()[:300])
    return r.stdout


def same_object(ob, binary):
    """Whether a run's object path names binary: the same file where the
    path still exists, else a file of the same name."""
    if os.path.exists(ob):
        return os.path.samefile(ob, binary)
    return os.path.basename(ob) == os.path.basename(binary)


def callgrind_counts(path, binary=None):
    """Address -> its own instructions, the first event, in a callgrind
    output written with --dump-instr=yes and --compress-pos=no; with binary,
    those of the cost lines under an `ob=` naming it, where the output names
    objects at all."""
    positions, events, cnt, skip = ['line'], None, collections.Counter(), False
    mine, names, cur, obs = collections.Counter(), {}, None, {}
    try:
        fh = open(path, errors='replace')
    except OSError as e:
        raise Unreadable(f'{path}: {e.strerror}')
    with fh:
        for k, line in enumerate(fh, 1):
            if skip:
                skip = False
                continue
            if line.startswith('calls='):
                skip = True
            elif line.startswith('positions:'):
                positions = line.split()[1:]
            elif line.startswith('events:'):
                events = line.split()[1:]
            elif line.startswith('ob='):
                cur = line[3:].strip()
                m = re.match(r'\((\d+)\)\s*(.*)$', cur)
                if m:
                    if m.group(2):
                        names[m.group(1)] = m.group(2)
                    cur = names.get(m.group(1), cur)
                if binary is not None and cur not in obs:
                    obs[cur] = same_object(cur, binary)
            elif line[:1] in ('+', '-', '*'):
                raise Unreadable(f'{path}:{k}: a relative position: written'
                                 ' with --compress-pos=yes')
            elif line.startswith('0x'):
                if positions[:1] != ['instr']:
                    raise Unreadable(f'{path}: positions {" ".join(positions)}'
                                     ': written without --dump-instr=yes')
                f = line.split()
                try:
                    a = int(f[0], 16)
                    c = int(f[len(positions)]) if len(f) > len(positions) \
                        else 0
                except ValueError:
                    raise Unreadable(f'{path}:{k}: not a cost line: '
                                     + line.strip()[:80])
                cnt[a] += c
                if obs.get(cur):
                    mine[a] += c
    if events is None or events[:1] != ['Ir']:
        raise Unreadable(f'{path}: no `events: Ir ...` line; not a callgrind'
                         ' output counting instructions')
    if not cnt:
        raise Unreadable(f'{path}: no cost line')
    if binary is None or not obs:
        return cnt
    if not mine:
        raise Unreadable(f'{path} names no object that is {binary}, only '
                         + ', '.join(sorted(obs)[:3]))
    return mine


def samples(path, binary):
    """Address -> count, from a callgrind output or from `COUNT ADDRESS`
    lines."""
    try:
        with open(path, errors='replace') as fh:
            first = fh.readline()
    except OSError as e:
        raise Unreadable(f'{path}: {e.strerror}')
    if first.startswith(('# callgrind format', 'version:')):
        return callgrind_counts(path, binary)
    cnt = collections.Counter()
    with open(path, errors='replace') as fh:
        for k, line in enumerate(fh, 1):
            f = line.split()
            if not f:
                continue
            try:
                if len(f) != 2:
                    raise ValueError
                cnt[int(f[1], 16)] += int(f[0])
            except ValueError:
                raise Unreadable(f'{path}:{k}: not `COUNT ADDRESS`: '
                                 + line.strip()[:80])
    if not cnt:
        raise Unreadable(f'{path}: no sample')
    return cnt


class Binary:
    """A binary's text section bounds and text symbols."""

    def __init__(self, path):
        if not os.path.isfile(path):
            raise Unreadable(f'{path}: no such file')
        self.path = path
        self.lo = self.hi = None
        for line in tool([OBJDUMP, '-h', path]).splitlines():
            f = line.split()
            if len(f) >= 4 and f[1] == '.text':
                self.lo = int(f[3], 16)
                self.hi = self.lo + int(f[2], 16)
        if self.lo is None:
            raise Unreadable(f'{path}: objdump -h lists no .text section')
        self.syms, self.exact = [], {}
        for line in tool([NM, '-n', path]).splitlines():
            p = line.split()
            if len(p) == 3:
                a = int(p[0], 16)
                self.exact[a] = p[2]
                if p[1] in ('T', 't', 'W', 'w'):
                    self.syms.append((a, p[2]))
        if not self.syms:
            raise Unreadable(f'{path}: nm lists no text symbol; stripped?')
        self.syms.sort()
        self.addrs = [a for a, _ in self.syms]

    def inside(self, a):
        return self.lo <= a < self.hi

    def owner(self, a):
        """The stripped name of the text symbol at or before a, and a's
        offset from it, or ('other', 0) outside the text section."""
        i = bisect.bisect_right(self.addrs, a) - 1
        if i < 0 or not self.inside(a):
            return 'other', 0
        return strip_unit(self.syms[i][1]), a - self.syms[i][0]

    def place(self, a):
        s, off = self.owner(a)
        return s if off == 0 else f'{s}+{off:#x}'

    def region(self, sym):
        """[lo, hi) of the code from the symbol named sym, by its full or
        stripped name or a suffix of exactly one, to the next symbol."""
        names = sorted({n for _, n in self.syms})
        hit = [n for n in names if sym in (n, strip_unit(n))]
        if not hit:
            hit = [n for n in names if n.endswith(sym)]
        if len(hit) != 1:
            raise Unreadable(f'{self.path}: '
                             + (f'no symbol ends in {sym}' if not hit else
                                f'{len(hit)} symbols end in {sym}: '
                                + ', '.join(hit[:5])))
        lo = min(a for a, n in self.syms if n == hit[0])
        later = [a for a in self.addrs if a > lo]
        return lo, min(later + [self.hi])

    def decode(self, addrs):
        """Address -> instruction text of each of addrs, by objdump sweeps:
        each starts at the lowest address no sweep has decoded and runs over
        the addresses after it while each lies within GAP bytes of the
        last; an address a sweep did not decode starts the next."""
        hot = sorted(set(addrs))
        text, todo = {}, set(hot)
        while todo:
            start = stop = min(todo)
            for a in hot[bisect.bisect_left(hot, start):]:
                if a - stop > GAP:
                    break
                stop = a
            out = tool([OBJDUMP, '-d', '--no-show-raw-insn',
                        f'--start-address={start:#x}',
                        f'--stop-address={stop + 16:#x}', self.path])
            for line in out.splitlines():
                m = INSN.match(line)
                if m:
                    text.setdefault(int(m.group(1), 16), m.group(2).strip())
            if start not in text:
                raise Unreadable(f'{self.path}: objdump decoded nothing at'
                                 f' {start:#x}')
            todo.difference_update(text)
        return {a: text[a] for a in hot if a in text}


def counts_of(b, run):
    """RUN's counts of b, refused where none of their addresses is in b's
    text."""
    cnt = callgrind_counts(run, b.path)
    if not any(b.inside(a) for a in cnt):
        raise Unreadable(f'{run}: no executed address lies in the text'
                         f' section [{b.lo:#x}, {b.hi:#x}) of {b.path}')
    return cnt


def often(b, cnt, n, least, lo=None, hi=None):
    """The addresses of b's text, or of [lo, hi), executed at least
    floor(least * n) times."""
    k = math.floor(least * n)
    return sorted(a for a, c in cnt.items() if c >= k and b.inside(a)
                  and (lo is None or lo <= a < hi))


def allocs(b, cnt, n, least=0.5):
    """(bytes a call, [(place, bump, count a call)], [(info symbol, count
    a call)])."""
    hot = often(b, cnt, n, least)
    if not hot:
        raise Unreadable(f'no instruction of {b.path} executed {least} times'
                         ' a call')
    total, bumps, objs = 0.0, [], collections.Counter()
    for a, ins in b.decode(hot).items():
        c = cnt[a]
        mb = BUMP.match(ins)
        if mb:
            x = int(mb.group(1), 16)
            if x >= 1 << 63:
                x -= 1 << 64
            total += x * c / n
            bumps.append((b.place(a), x, c / n))
        mi = INFO.match(ins)
        if mi and int(mi.group(1), 16) in b.exact:
            objs[strip_unit(b.exact[int(mi.group(1), 16)])] += c / n
    return total, bumps, sorted(objs.items(), key=lambda kv: -kv[1])


def bysym(b, cnt):
    """Stripped symbol, or 'other' -> instructions."""
    by = collections.Counter()
    for a, c in cnt.items():
        by[b.owner(a)[0]] += c
    return by


def region_seq(b, cnt, sym, n, least=0.25, raw=False):
    """[(instruction, count a call to two decimals, address)] of the code
    from sym to the next symbol executed at least least * n times."""
    lo, hi = b.region(sym)
    hot = often(b, cnt, n, least, lo, hi)
    if not hot:
        raise Unreadable(f'{b.path}: nothing from {sym} to the next symbol'
                         f' executed {least} times a call')
    seq = []
    for a, ins in b.decode(hot).items():
        if not raw:
            ins = re.sub(r'<[^>]*>', '', BIG.sub('ADDR', ins)).strip()
        seq.append((ins, round(cnt[a] / n, 2), a))
    return seq


def sweep(b, lo, hi, cnt):
    """(sampled {address: count} in [lo, hi), those a linear objdump sweep
    from lo decodes as no instruction start)."""
    out = tool([OBJDUMP, '-d', '--no-show-raw-insn',
                f'--start-address={lo:#x}', f'--stop-address={hi:#x}', b.path])
    starts = {int(m.group(1), 16) for m in map(INSN.match, out.splitlines())
              if m}
    hot = {a: c for a, c in cnt.items() if lo <= a < hi}
    return hot, {a: c for a, c in hot.items() if a not in starts}


def binaries():
    return functools.lru_cache(maxsize=None)(Binary)


def number(s, what, kind=int):
    try:
        v = kind(s)
    except ValueError:
        raise Unreadable(f'{what} {s!r} is not a number')
    if v <= 0 and what == 'N':
        raise Unreadable('N must be positive')
    return v


def address(s):
    try:
        return int(s, 16)
    except ValueError:
        raise Unreadable(f'{s!r} is not a hex address')


def option(argv, flag, kind, default):
    if flag in argv:
        i = argv.index(flag)
        if i + 1 >= len(argv):
            raise Unreadable(f'{flag} needs a value')
        v = number(argv[i + 1], flag, kind)
        return v, argv[:i] + argv[i + 2:]
    return default, argv


def run(argv):
    """The subcommand's lines to print and its exit status."""
    get = binaries()
    cmd, argv = argv[0], argv[1:]
    out = []
    if cmd == 'allocs':
        least, argv = option(argv, '--min', float, 0.5)
        need(argv, 3)
        b = get(argv[0])
        n = number(argv[2], 'N')
        total, bumps, objs = allocs(b, counts_of(b, argv[1]), n, least)
        out.append(f'bytes a call by %r12 bumps: {total:.1f}')
        out += [f'  bump {x:5d} x {k:6.2f}  at {s}' for s, x, k in bumps]
        out += [f'  obj {k:6.2f}  {s}' for s, k in objs]
    elif cmd == 'bysym':
        top, argv = option(argv, '--top', int, 14)
        need(argv, 5)
        n = number(argv[4], 'N')
        ba, bb = get(argv[0]), get(argv[2])
        A = bysym(ba, counts_of(ba, argv[1]))
        B = bysym(bb, counts_of(bb, argv[3]))
        d = {k: (B[k] - A[k]) / n for k in set(A) | set(B)}
        out.append(f'total {(sum(B.values()) - sum(A.values())) / n:.2f}')
        for k, v in sorted(d.items(),
                           key=lambda kv: (-abs(kv[1]), kv[0]))[:top]:
            out.append(f'{v:9.2f}  A {A[k] / n:9.2f}  B {B[k] / n:9.2f}'
                       f'  {k[:100]}')
    elif cmd == 'incr':
        top, argv = option(argv, '--top', int, 10)
        need(argv, 7)
        n = number(argv[6], 'N')
        ba, bb = get(argv[0]), get(argv[3])
        A1, A2 = (bysym(ba, counts_of(ba, r)) for r in argv[1:3])
        B1, B2 = (bysym(bb, counts_of(bb, r)) for r in argv[4:6])
        keys = set(A1) | set(A2) | set(B1) | set(B2)
        ia = {k: (A2[k] - A1[k]) / n for k in keys}
        ib = {k: (B2[k] - B1[k]) / n for k in keys}
        sa, sb = sum(ia.values()), sum(ib.values())
        out.append(f'total A {sa:.2f} B {sb:.2f} B-A {sb - sa:.2f}')
        for k in sorted(keys, key=lambda k: (-abs(ib[k] - ia[k]), k))[:top]:
            out.append(f'{ib[k] - ia[k]:11.2f}  A {ia[k]:12.2f}'
                       f'  B {ib[k]:12.2f}  {k[:90]}')
    elif cmd == 'region':
        least, argv = option(argv, '--min', float, 0.25)
        need(argv, 6)
        n = number(argv[5], 'N')
        ba, bb = get(argv[0]), get(argv[2])
        A = region_seq(ba, counts_of(ba, argv[1]), argv[4], n, least)
        B = region_seq(bb, counts_of(bb, argv[3]), argv[4], n, least)
        sums = [sum(c for _, c, _ in x) for x in (A, B)]
        out.append('executed instructions (count a call, summed): '
                   f'{sums[0]:.2f} {sums[1]:.2f}')
        sa = [f'{i} x{c}' for i, c, _ in A]
        sb = [f'{i} x{c}' for i, c, _ in B]
        for op, i1, i2, j1, j2 in difflib.SequenceMatcher(
                None, sa, sb, autojunk=False).get_opcodes():
            if op != 'equal':
                out.append(f'== {op}')
                out += ['   A ' + x for x in sa[i1:i2]]
                out += ['   B ' + x for x in sb[j1:j2]]
    elif cmd == 'seq':
        raw = '--raw' in argv
        argv = [a for a in argv if a != '--raw']
        need(argv, 6)
        n = number(argv[3], 'N')
        lo, hi = number(argv[4], 'LO', float), number(argv[5], 'HI', float)
        b = get(argv[0])
        k = 0
        for ins, c, a in region_seq(b, counts_of(b, argv[1]), argv[2], n,
                                    min(lo, 0.25), raw):
            if lo <= c <= hi:
                k += 1
                m = IMM.search(ins) if raw else None
                name = strip_unit(b.exact.get(int(m.group(1), 16), '')) \
                    if m else ''
                out.append(f'{a:#x} {c:7.2f} {ins}' + (f'  {name}' if name
                                                        else ''))
        out.append(f'count {k}')
    elif cmd == 'sweep':
        need(argv, 4)
        b = get(argv[0])
        lo, hi = address(argv[1]), address(argv[2])
        hot, miss = sweep(b, lo, hi, samples(argv[3], b.path))
        if not hot:
            raise Unreadable(f'{argv[3]}: no sampled address in'
                             f' [{lo:#x}, {hi:#x})')
        out.append(f'{b.path} {lo:#x}-{hi:#x}: sampled {len(hot)} addresses,'
                   f' {sum(hot.values())} samples; the linear sweep missed'
                   f' {len(miss)} addresses, {sum(miss.values())} samples'
                   + (': ' + ' '.join(f'{a:#x}' for a in sorted(miss)[:6])
                      if miss else ''))
        return out, 1 if miss else 0
    else:
        raise Unreadable(f'no subcommand {cmd}')
    return out, 0


def need(argv, k):
    if len(argv) != k:
        raise Unreadable('usage:\n' + __doc__.split('\n\n')[1])


FIXTURE = r'''
        .text
        .globl _start
_start:
        nop
        ret
        .org 0x100, 0x90
        .globl pkgzm1zi0zminplace_ModA_foo_info
pkgzm1zi0zminplace_ModA_foo_info:
        add $0x10, %r12
        .org 0x110, 0x90
        movq $pkgzm1zi0zminplace_ModA_bar_info, -0x8(%r12)
        .org 0x120, 0x90
        jmp 1f
        # An info table's bytes, which a linear sweep decodes as a movabs
        # taking the first four bytes of the movq after it.
        .org 0x13a, 0x90
        .byte 0x48, 0xb8
        .org 0x140, 0x00
1:      movq $basezm4zi0_GHCziBase_baz_info, -0x10(%r12)
        .org 0x150, 0x90
        add $-0x18, %r12
        .org 0x160, 0x90
        mov %rbx, %rax
        .org 0x170, 0x90
        ret
        .org 0x200, 0x90
pkgzm1zi0zminplace_ModA_bar_info:
        add $0x20, %r12
        .org 0x210, 0x90
        ret
        .org 0x300, 0x90
basezm4zi0_GHCziBase_baz_info:
        ret
        .org 0x400, 0x90
stg_gc_noregs:
        ret
'''
BASE = 0x401000
# Run A's counts at N = 10, by offset from BASE: foo's code once a call
# but its give-back at 0x150 every other call, bar's once a call, and setup
# code, baz, the collector and an address outside the binary rarely.
RUN_A = {0x000: 1, 0x100: 10, 0x110: 10, 0x120: 10, 0x140: 10, 0x150: 5,
         0x160: 10, 0x170: 10, 0x200: 10, 0x210: 10, 0x300: 1, 0x400: 3}
OUTSIDE = 0x7000000


def write_run(path, fix, offsets, outside=50, scale=1,
              setup=(0x000, 0x300, 0x400)):
    """A callgrind output of the fixture fix: each offset's count, those not
    in setup times scale, a call from 0x170 whose inclusive cost line must
    be skipped, an address of the binary outside its text section, and a
    library's address inside the binary's text range, which is not the
    binary's."""
    lines = ['# callgrind format', 'version: 1', 'creator: callgrind-3.22.0',
             'cmd: ./fix --iters 10', 'part: 1', '', 'positions: instr line',
             'events: Ir', 'summary: 1', '', 'ob=(1) /lib/libc.so.6',
             'fn=memcpy', f'{BASE + 0x100:#x} 0 7777', f'ob=(2) {fix}',
             'fl=???', 'fn=foo']
    for off, c in sorted(offsets.items()):
        lines.append(f'{BASE + off:#x} 0 {c if off in setup else c * scale}')
        if off == 0x170:
            lines += [f'calls=10 {BASE + 0x200:#x} 0',
                      f'{BASE + 0x170:#x} 0 9999']
    lines += ['ob=(1)', f'{BASE + 0x110:#x} 0 7777', 'ob=(2)',
              f'{OUTSIDE:#x} 0 {outside}', '']
    with open(path, 'w') as fh:
        fh.write('\n'.join(lines))
    return path


def checks(bad, td):
    """The self-test's cases, each failure appended to bad; a status
    to exit with where the fixtures cannot be built."""
    global OBJDUMP
    for t in ('as', 'ld', OBJDUMP, NM):
        if shutil.which(t) is None:
            print(f'{t} is not on PATH; the fixture cannot be built')
            return 2
    src, obj, fix = (os.path.join(td, f) for f in ('fix.s', 'fix.o', 'fix'))
    with open(src, 'w') as fh:
        fh.write(FIXTURE)
    for cmd in (['as', '-o', obj, src],
                ['ld', '-static', f'-Ttext={BASE:#x}', '-e', '_start',
                 '-o', fix, obj]):
        r = subprocess.run(cmd, capture_output=True, text=True)
        if r.returncode != 0:
            print(f'{" ".join(cmd)} failed: {r.stderr.strip()}')
            return 2
    b = Binary(fix)
    if b.region('foo_info') != (BASE + 0x100, BASE + 0x200):
        bad.append(f'region of foo: {b.region("foo_info")}')
    if (b.lo, b.hi) != (BASE, BASE + 0x401):
        bad.append(f'text bounds {b.lo:#x} {b.hi:#x}')
    names = sorted(strip_unit(n) for _, n in b.syms)
    if not {'ModA_foo_info', 'ModA_bar_info', 'GHCziBase_baz_info',
            'stg_gc_noregs'} <= set(names):
        bad.append(f'unit prefixes not stripped: {names}')
    a = write_run(os.path.join(td, 'a.cg'), fix, RUN_A)
    if callgrind_counts(a)[BASE + 0x100] != 10 + 7777:
        bad.append('without a binary, not every object counted')
    cnt = callgrind_counts(a, fix)
    if cnt[BASE + 0x170] != 10:
        bad.append(f"a call's inclusive cost counted: {cnt[BASE + 0x170]}")
    total, bumps, objs = allocs(b, cnt, 10)
    if (total, bumps) != (36.0, [('ModA_foo_info', 16, 1.0),
                                 ('ModA_foo_info+0x50', -24, 0.5),
                                 ('ModA_bar_info', 32, 1.0)]):
        bad.append(f'allocs: {total} {bumps}')
    if objs != [('ModA_bar_info', 1.0), ('GHCziBase_baz_info', 1.0)]:
        bad.append(f'allocs, info pointers: {objs}')
    by = bysym(b, cnt)
    if (by['ModA_foo_info'], by['ModA_bar_info'], by['other']) != (65, 20, 50):
        bad.append(f'bysym: {dict(by)}')
    # B runs foo's mov twice a call and bar three times.
    rb = {**RUN_A, 0x160: 20, 0x200: 30, 0x210: 30}
    bcg = write_run(os.path.join(td, 'b.cg'), fix, rb)
    out, rc = run(['bysym', fix, a, fix, bcg, '10'])
    if rc != 0 or out[:3] != [
            'total 5.00',
            '     4.00  A      2.00  B      6.00  ModA_bar_info',
            '     1.00  A      6.50  B      7.50  ModA_foo_info']:
        bad.append(f'bysym output: {out[:3]}')
    a2 = write_run(os.path.join(td, 'a2.cg'), fix, RUN_A, scale=2)
    b2 = write_run(os.path.join(td, 'b2.cg'), fix, rb, scale=2)
    out, rc = run(['incr', fix, a, a2, fix, bcg, b2, '10'])
    if rc != 0 or out[:3] != [
            'total A 8.50 B 13.50 B-A 5.00',
            '       4.00  A         2.00  B         6.00  ModA_bar_info',
            '       1.00  A         6.50  B         7.50  ModA_foo_info']:
        bad.append(f'incr output: {out[:3]}')
    seq = region_seq(b, cnt, 'foo_info', 10)
    if [(i, c) for i, c, _ in seq] != [
            ('add    $0x10,%r12', 1.0), ('movq   $ADDR,-0x8(%r12)', 1.0),
            ('jmp    ADDR', 1.0), ('movq   $ADDR,-0x10(%r12)', 1.0),
            ('add    $ADDR,%r12', 0.5), ('mov    %rbx,%rax', 1.0),
            ('ret', 1.0)]:
        bad.append(f'region of foo: {seq}')
    out, rc = run(['region', fix, a, fix, bcg, 'ModA_foo_info', '10'])
    if rc != 0 or out != [
            'executed instructions (count a call, summed): 6.50 7.50',
                          '== replace', '   A mov    %rbx,%rax x1.0',
                          '   B mov    %rbx,%rax x2.0']:
        bad.append(f'region output: {out}')
    out, rc = run(['seq', fix, a, 'foo_info', '10', '0.4', '0.6'])
    if rc != 0 or out != [f'{BASE + 0x150:#x}    0.50 add    $ADDR,%r12',
                          'count 1']:
        bad.append(f'seq output: {out}')
    out, rc = run(['seq', '--raw', fix, a, 'foo_info', '10', '1', '1'])
    if rc != 0 or out[1] != (f'{BASE + 0x110:#x}    1.00 movq   '
                             '$0x401200,-0x8(%r12)  ModA_bar_info') \
            or out[3] != (f'{BASE + 0x140:#x}    1.00 movq   '
                          '$0x401300,-0x10(%r12)  GHCziBase_baz_info') \
            or out[-1] != 'count 6':
        bad.append(f'seq --raw output: {out}')
    ips = os.path.join(td, 'ips')
    with open(ips, 'w') as fh:
        fh.write(f'3 {BASE + 0x100:x}\n5 {BASE + 0x140:x}\n'
                 f'2 {BASE + 0x150:x}\n7 {BASE + 0x200:x}\n')
    out, rc = run(['sweep', fix, f'{BASE + 0x100:#x}', f'{BASE + 0x200:#x}',
                   ips])
    if rc != 1 or not out[0].endswith('sampled 3 addresses, 10 samples;'
                                      ' the linear sweep missed 1'
                                      ' addresses, 5 samples: 0x401140'):
        bad.append(f'sweep through the info table: {rc} {out}')
    out, rc = run(['sweep', fix, f'{BASE + 0x200:#x}', f'{BASE + 0x300:#x}',
                   a])
    if rc != 0 or 'missed 0 addresses' not in out[0]:
        bad.append(f'sweep over callgrind samples in step: {rc} {out}')
    out, rc = run(['sweep', fix, f'{BASE + 0x100:#x}', f'{BASE + 0x200:#x}',
                   a])
    if rc != 1 or not out[0].endswith('sampled 7 addresses, 65 samples;'
                                      ' the linear sweep missed 1'
                                      ' addresses, 10 samples: 0x401140'):
        bad.append(f"sweep over callgrind samples, the library's left"
                   f' out: {rc} {out}')
    # What the run did not happen for.
    head = 'events: Ir\nfn=f\n'
    cases = [(['bysym', fix, a, fix, bcg, '10'], 'compressed positions',
              'positions: instr line\n' + head + '0x401100 0 1\n+3 0 1\n'),
             (['allocs', fix, a, '10'], 'positions without instr',
              'positions: line\n' + head + '0x401100 1\n'),
             (['allocs', fix, a, '10'], 'a run outside the text section',
              'positions: instr line\n' + head + '0x501100 0 10\n'),
             (['allocs', fix, a, '10'], 'a run of another binary',
              f'positions: instr line\nevents: Ir\nob={obj}\n'
              '0x401100 0 10\n'),
             (['allocs', fix, a, '10'], 'a run counting no Ir',
              'positions: instr line\nevents: Dr\n0x401100 0 10\n'),
             (['allocs', fix, os.path.join(td, 'none'), '10'],
              'a missing run', None),
             (['region', fix, a, fix, a, '_info', '10'],
              'a symbol suffix matching several', None),
             (['region', fix, a, fix, a, 'nosuch', '10'],
              'a symbol matching none', None),
             (['allocs', fix, a], 'too few arguments', None),
             (['allocs', fix, a, 'ten'], 'N not a number', None),
             (['allocs', src, a, '10'], 'a binary objdump cannot read',
              None)]
    for argv, what, text in cases:
        if text is not None:
            p = os.path.join(td, 'bad.cg')
            with open(p, 'w') as fh:
                fh.write(text)
            argv = [p if x == a else x for x in argv]
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            rc = main(argv)
        if rc != 2 or not err.getvalue().startswith('cg-read: '):
            bad.append(f'{what} did not exit 2 with a reason: {rc}')
    saved, OBJDUMP = OBJDUMP, os.path.join(td, 'no-objdump')
    try:
        with contextlib.redirect_stderr(io.StringIO()):
            if main(['allocs', fix, a, '10']) != 2:
                bad.append('objdump missing did not exit 2')
    finally:
        OBJDUMP = saved


def self_test():
    """Each subcommand over a fixture binary assembled here, whose symbols
    carry z-encoded unit prefixes and whose one function holds an info
    table's bytes that put a linear sweep out of step with the code after
    them, and over callgrind outputs written for it."""
    bad = []
    try:
        with tempfile.TemporaryDirectory() as td:
            rc = checks(bad, td)
            if rc is not None:
                return rc
    except Unreadable as e:
        bad.append(f'a run the self-test needs did not happen: {e}')
    for x in bad:
        print('FAIL', x)
    print('self-test', 'FAILED' if bad else 'passed')
    return 1 if bad else 0


def main(argv):
    if argv == ['--self-test']:
        return self_test()
    if not argv:
        print(__doc__.split('\n\n')[1], file=sys.stderr)
        return 2
    try:
        out, rc = run(argv)
    except Unreadable as e:
        print(f'cg-read: {e}', file=sys.stderr)
        return 2
    for line in out:
        print(line)
    return rc


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
