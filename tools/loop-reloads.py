#!/usr/bin/env python3
"""Find loops whose every iteration reloads values from the enclosing frame.

Usage: python3 tools/loop-reloads.py DUMPS [--module SUBSTRING] [--min N]
       python3 tools/loop-reloads.py --self-test

DUMPS is a dump tree, a build directory or a `-dumpdir` tree, whose modules
were compiled with `-ddump-asm -ddump-to-file` by GHC's native code
generator for x86-64, without `-dsuppress-uniques`, which names every
return point `.Lblock_info`; `--module` keeps the modules whose dump path
contains SUBSTRING, and a module's `X.dyn.dump-asm`, which `-dynamic-too`
writes beside `X.dump-asm`, is read only where it has no other. Within each
procedure, from one `_info` symbol to the next, this builds the
control-flow graph of its blocks: jumps to labels, fall-through, and a
call's return, read off the store of `$.Lblock_L_info`, or under `-fPIC`
the `leaq` of its address, that pushes the return point L. A return point
is the label right after a `.Lblock..._info` label, and one inside a cycle
is the continuation of a call made on every iteration, such as the
evaluation of a boxed element, whose fast path jumps to it when the element
is already evaluated. Its block pops the frame the call pushed,
`addq $K,%rbp`, and every load from `N(%rbp)` with N >= K before that,
from a slot no block of the cycle stores to, reloads a value from the
enclosing frame: one live across the loop, which the loop's own frame did
not save, reloaded on every iteration. A slot is named the same in every
block by following the stack pointer's offset around the cycle. Prints the
module, the procedure, the return point, K, the number of such loads and
their offsets, for each return point with at least N of them (2 by
default), most first.

A loop costs only as often as it runs, so a finding is ranked by how often
its return point runs at a client before it is read: `cg-read.py seq` gives
each address's executions a call. A procedure labelled `.L` has no symbol in
the binary, and callgrind books its code under the nearest global symbol
before it in the dump, so `seq` runs over that symbol, and the return point
is the one whose loads match the offsets printed here (docs/perf-checklist.md,
B2).

Exit 0 when nothing was found, 1 when something was, 2 when DUMPS holds no
`.dump-asm`, no module's path contains SUBSTRING, a dump names its return
points `.Lblock_info`, none holds x86-64 code, or N is no number.
"""

import contextlib
import io
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dumps  # noqa: E402

# A label: GHC writes a symbol unencoded, a prime or an operator's
# characters in it (loop-reloads-02).
LABEL = re.compile(r'^(\S+):\s*$')
INFO = re.compile(r'_info:\s*$')
JUMP = re.compile(r'^\s+(j[a-z]+)\s+(\.L[\w$.]+)\s*$')
UNCOND = re.compile(r'^\s+(jmp\s|ret\b|ud2\b)')
# A call's return point pushed: its info pointer stored, or under -fPIC its
# address loaded into a register, which is then stored (loop-reloads-04).
PUSH_RET = re.compile(r'^\s+movq\s+\$\.Lblock_([\w$.]+)_info,')
LEA_RET = re.compile(r'^\s+leaq\s+\.Lblock_([\w$.]+)_info\(%rip\),(%\w+)')
UNNAMED = re.compile(r'^\.Lblock_info:', re.M)
ADJ = re.compile(r'^\s+addq\s+\$(-?\d+),%rbp\s*$')
LOAD = re.compile(r'^\s+mov\w*\s+(-?\d*)\(%rbp\),%')
STORE = re.compile(r'^\s+mov\w*\s+([^,\s]+),(-?\d*)\(%rbp\)\s*$')


def procedures(lines):
    """Yield (name, [(label, [lines])], return points) for each procedure."""
    name, blocks, rets, info = None, [], set(), False
    for line in lines:
        m = LABEL.match(line)
        if m and INFO.search(line) and not line.startswith('.Lblock_'):
            if name is not None:
                yield name, blocks, rets
            name, blocks, rets, info = m.group(1), [(m.group(1), [])], set(), False
            continue
        if name is None:
            continue
        if m and line.startswith('.Lblock_'):
            info = True
            blocks[-1][1].append(line)
        elif m:
            blocks.append((m.group(1), []))
            if info:
                rets.add(m.group(1))
            info = False
        else:
            blocks[-1][1].append(line)
    if name is not None:
        yield name, blocks, rets


def cyclic(labels, succ):
    """Each label on a cycle mapped to its component: Tarjan's components of
    more than one node, or of one with an edge to itself."""
    index, low, on, stack, out, n = {}, {}, set(), [], {}, 0
    for v0 in labels:
        if v0 in index:
            continue
        index[v0] = low[v0] = n
        n += 1
        stack.append(v0)
        on.add(v0)
        work = [(v0, iter(succ.get(v0, ())))]
        while work:
            v, it = work[-1]
            for w in it:
                if w not in index:
                    index[w] = low[w] = n
                    n += 1
                    stack.append(w)
                    on.add(w)
                    work.append((w, iter(succ.get(w, ()))))
                    break
                if w in on:
                    low[v] = min(low[v], index[w])
            else:
                work.pop()
                if work:
                    low[work[-1][0]] = min(low[work[-1][0]], low[v])
                if low[v] == index[v]:
                    comp = set()
                    while True:
                        w = stack.pop()
                        on.discard(w)
                        comp.add(w)
                        if w == v:
                            break
                    if len(comp) > 1 or v in succ.get(v, ()):
                        out.update(dict.fromkeys(comp, v))
    return out


def edges_of(blocks):
    """Each block's successors with the adjustment of %rbp on the way: a
    jump's where it jumps and a fall-through's at the block's end; a call
    returns to its return point with the stack pointer at the slot the
    return point was pushed to, a callee popping its stack arguments."""
    labels = [b[0] for b in blocks]
    known = set(labels)
    out = {}
    for i, (lab, body) in enumerate(blocks):
        es, held, d, falls = [], {}, 0, True
        for line in body:
            m = ADJ.match(line)
            if m:
                d += int(m.group(1))
            m = JUMP.match(line)
            if m and m.group(2) in known:
                es.append((m.group(2), d))
            m = LEA_RET.match(line)
            if m:
                held[m.group(2)] = '.L' + m.group(1)
            m = STORE.match(line)
            if m:
                p = PUSH_RET.match(line)
                ret = '.L' + p.group(1) if p else held.get(m.group(1))
                if ret in known:
                    es.append((ret, d + int(m.group(2) or 0)))
            if UNCOND.match(line):
                falls = False
        if falls and i + 1 < len(blocks):
            es.append((labels[i + 1], d))
        out[lab] = es
    return out


def stored(blocks, edges, start, loop):
    """The stack slots, as offsets from START's stack pointer on entry, that
    a block of START's cycle stores to: the offset followed along the
    cycle's edges, the first path to a block deciding it."""
    off, todo = {start: 0}, [start]
    while todo:
        b = todo.pop()
        for t, d in edges[b]:
            if loop.get(t) == loop[start] and t not in off:
                off[t] = off[b] + d
                todo.append(t)
    out = set()
    for lab, body in blocks:
        if lab in off:
            o = off[lab]
            for line in body:
                m = ADJ.match(line) or STORE.match(line)
                if m and m.re is ADJ:
                    o += int(m.group(1))
                elif m:
                    out.add(o + int(m.group(2) or 0))
    return out


def findings(text, least):
    """[(procedure, return point, K, [offsets])], most offsets first."""
    out = []
    for proc, blocks, rets in procedures(text.split('\n')):
        edges = edges_of(blocks)
        succ = {lab: {t for t, _ in es} for lab, es in edges.items()}
        loop = cyclic([b[0] for b in blocks], succ)
        for lab, body in blocks:
            if lab not in loop or lab not in rets:
                continue
            k, o, loads = None, 0, []
            for line in body:
                m = ADJ.match(line)
                if m and int(m.group(1)) > 0:
                    k = int(m.group(1))
                    break
                if m:
                    o += int(m.group(1))
                m = LOAD.match(line)
                if m:
                    n = int(m.group(1) or 0)
                    loads.append((n, o + n))
            if k is None:
                continue
            # A slot the cycle stores to is the loop's own state, saved by
            # the loop and reloaded (loop-reloads-05).
            mine = stored(blocks, edges, lab, loop)
            outer = sorted(n for n, slot in loads
                           if n >= k and slot not in mine)
            if len(outer) >= least:
                out.append((proc, lab, k, outer))
    return sorted(out, key=lambda f: -len(f[3]))


def report(root, sub, least):
    """(rows, modules read, a dump printing its return points unnamed or
    None, whether any procedure of x86-64 code was recognised)."""
    paths = dumps.walk(root, '.dump-asm')
    have = {p for p, _ in paths}
    rows, read, unnamed, x86 = [], 0, None, False
    for path, key in paths:
        if sub is not None and sub not in path:
            continue
        # -dynamic-too writes X.dyn.dump-asm beside X.dump-asm: one module,
        # read once (loop-reloads-04).
        twin = path.replace('.dyn.dump-asm', '.dump-asm')
        if twin != path and twin in have:
            continue
        read += 1
        text = dumps.read_text(path)
        if UNNAMED.search(text):
            unnamed = unnamed or path
            continue
        x86 = x86 or ('%rbp' in text and any(procedures(text.split('\n'))))
        for proc, lab, k, outer in findings(text, least):
            rows.append((len(outer),
                         f'{key}\t{proc}\t{lab}\t{k}\t{len(outer)}\t'
                         + ','.join(map(str, outer))))
    rows.sort(key=lambda r: -r[0])
    return [r[1] for r in rows], read, unnamed, x86


ASM = '''
.Lf_info:
.Lc1:
\tmovq %rbx,%rax
.Lc3:
\tcmpq %r14,%rdx
\tjge .Lc4
.Lc5:
\tmovq $.Lblock_c2_info,-16(%rbp)
\tmovq %rax,-8(%rbp)
\taddq $-16,%rbp
\ttestb $7,%bl
\tjne .Lc2
.Lc6:
\tjmp *(%rbx)
\t.long\t30
.Lblock_c2_info:
.Lc2:
\tmovq 8(%rbp),%rax
\tmovq 16(%rbp),%rcx
\tmovq 24(%rbp),%rsi
\tmovq 40(%rbp),%rdi
\tincq %rdx
\taddq $16,%rbp
\tjmp .Lc3
.Lc4:
\tjmp *(%rbp)
.Lg_info:
.Lc7:
\tmovq $.Lblock_c8_info,-8(%rbp)
\taddq $-8,%rbp
\tjmp *(%rbx)
\t.long\t30
.Lblock_c8_info:
.Lc8:
\tmovq 8(%rbp),%rax
\tmovq 16(%rbp),%rcx
\tmovq 24(%rbp),%rsi
\taddq $8,%rbp
\tjmp *(%rbp)
M.$w<+>_info:
.Lc10:
\tcmpq %r14,%rdx
\tjge .Lc13
.Lc11:
\tleaq .Lblock_c12_info(%rip),%rax
\tmovq %rax,-8(%rbp)
\taddq $-8,%rbp
\tjmp *%rbx
\t.long\t30
.Lblock_c12_info:
.Lc12:
\tmovq 8(%rbp),%rax
\tmovq 16(%rbp),%rcx
\taddq $8,%rbp
\tjmp .Lc10
.Lc13:
\tjmp *(%rbp)
.Lk_info:
.Lc20:
\tmovq $.Lblock_c21_info,-16(%rbp)
\taddq $-16,%rbp
\tjmp *(%rbx)
\t.long\t30
.Lblock_c21_info:
.Lc21:
\tmovq 8(%rbp),%rax
\tmovq $.Lblock_c22_info,8(%rbp)
\tmovq 16(%rbp),%rcx
\tmovq 24(%rbp),%rdx
\tmovq 32(%rbp),%rsi
\taddq %rbx,%rcx
\tmovq %rcx,16(%rbp)
\taddq $8,%rbp
\tjmp *(%rax)
\t.long\t30
.Lblock_c22_info:
.Lc22:
\tmovq $.Lblock_c21_info,-8(%rbp)
\taddq $-8,%rbp
\tjmp M.$wwork_info
'''


def self_test():
    """Four procedures: f, a loop whose continuation, reached by the fast
    path's jump, reloads three values from the enclosing frame and one from
    its own; g, a return point on no cycle; an operator's worker, a loop
    closed only through its return point's address loaded by -fPIC's leaq;
    and k, a loop closed through two calls' returns that reloads two values
    it never stores and two it stores on every iteration. And trees: one
    whose module -dynamic-too dumped twice, one naming no return point, and
    one of another architecture's code."""
    import tempfile
    bad = []
    got = findings(ASM, 2)
    want = [('.Lf_info', '.Lc2', 16, [16, 24, 40]),
            ('M.$w<+>_info', '.Lc12', 8, [8, 16]),
            ('.Lk_info', '.Lc21', 8, [24, 32])]
    if got != want:
        bad.append(f'findings: {got}')
    if findings(ASM, 3) != want[:1]:
        bad.append('--min 3 kept the two-value loops')
    with tempfile.TemporaryDirectory() as td, \
            tempfile.TemporaryDirectory() as tx:
        d = os.path.join(td, 'b', 'build', 'Client')
        os.makedirs(d)
        for name in ('Ops.dump-asm', 'Ops.dyn.dump-asm'):
            with open(os.path.join(d, name), 'w') as fh:
                fh.write(ASM)
        if len(report(td, None, 2)[0]) != 3:
            bad.append('a module dumped twice by -dynamic-too read twice')
        e = os.path.join(td, 'empty')
        os.makedirs(e)
        u, a = os.path.join(tx, 'u'), os.path.join(tx, 'a')
        for where, name, text in (
                (u, 'M', ASM.replace('_c2_info', '_info')), (u, 'N', ASM),
                (a, 'M', 'M_foo_info:\n\tldr x0, [x20, #8]\n')):
            os.makedirs(where, exist_ok=True)
            with open(os.path.join(where, name + '.dump-asm'), 'w') as fh:
                fh.write(text)
        for argv, code, why in (
                ([td], 1, 'findings'),
                ([td, '--min', '4'], 0, 'nothing at --min 4'),
                ([td, '--module', 'Client'], 1, 'a --module'),
                ([td, '--module', 'NoSuch'], 2, 'a --module matching nothing'),
                ([td, '--min', 'x'], 2, 'a --min that is no number'),
                ([e], 2, 'a tree without dumps'),
                ([u], 2, 'a dump naming no return point'),
                ([a], 2, 'a dump of no x86-64 code')):
            with contextlib.redirect_stderr(io.StringIO()):
                if main(argv) != code:
                    bad.append(f'{why} did not exit {code}')
    for b in bad:
        print('FAIL', b)
    print('self-test', 'FAILED' if bad else 'passed')
    return 1 if bad else 0


def main(argv):
    if argv == ['--self-test']:
        return self_test()
    sub, least, rest, i = None, 2, [], 0
    while i < len(argv):
        if argv[i] in ('--module', '--min'):
            if i + 1 >= len(argv):
                print(__doc__.split('\n\n')[1], file=sys.stderr)
                return 2
            if argv[i] == '--module':
                sub = argv[i + 1]
            else:
                try:
                    least = int(argv[i + 1])
                except ValueError:
                    print(f'--min {argv[i + 1]!r} is no number', file=sys.stderr)
                    return 2
            i += 2
        else:
            rest.append(argv[i])
            i += 1
    if len(rest) != 1 or rest[0].startswith('--'):
        print(__doc__.split('\n\n')[1], file=sys.stderr)
        return 2
    if not dumps.walk(rest[0], '.dump-asm'):
        print(f'no .dump-asm file under {rest[0]}; was it built with '
              '-ddump-asm -ddump-to-file?', file=sys.stderr)
        return 2
    lines, read, unnamed, x86 = report(rest[0], sub, least)
    if not read:
        print(f"no module's path contains {sub}", file=sys.stderr)
        return 2
    # Without uniques no push names its return point, so a loop closed
    # through a call, B2's, was missed in silence (loop-reloads-01).
    if unnamed:
        print(f'{unnamed} names every return point `.Lblock_info`, so no call '
              'can be followed to its return; build it without '
              '-dsuppress-uniques', file=sys.stderr)
        return 2
    if not x86:      # an exit 0 before (loop-reloads-03)
        print('no x86-64 code of GHC\'s native code generator in the dumps '
              'read', file=sys.stderr)
        return 2
    if lines:
        print('\n'.join(lines))
    return 1 if lines else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
