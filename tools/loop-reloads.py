#!/usr/bin/env python3
"""Find loops whose every iteration reloads values from the enclosing frame.

Usage: python3 tools/loop-reloads.py DUMPS [--module SUBSTRING] [--min N]
       python3 tools/loop-reloads.py --self-test

DUMPS is a dump tree, a build directory or a `-dumpdir` tree, whose modules
were compiled with `-ddump-asm -ddump-to-file` by GHC's native code
generator for x86-64, with or without `-dsuppress-uniques`, block labels
surviving it; `--module` keeps the modules whose dump path contains
SUBSTRING. Within each procedure, from one `_info` symbol to the next, this
builds the control-flow graph of its blocks: jumps to labels, fall-through,
and, where the dump keeps uniques, a call's return, read off the store of
`$.Lblock_L_info` that pushes the return point L. A return point is the
label right after a `.Lblock..._info` label, and one inside a cycle is the
continuation of a call made on every iteration, such as the evaluation of
a boxed element, whose fast path jumps to it when the element is already
evaluated. Its block pops the frame the call pushed, `addq $K,%rbp`, and
every load from `N(%rbp)` with N >= K before that reloads a value from the
enclosing frame: one live across the loop, which the loop's own frame did
not save, reloaded on every iteration. Prints the module, the procedure,
the return point, K, the number of such loads and their offsets, for each
return point with at least N of them (2 by default), most first.

A loop costs only as often as it runs, so a finding is ranked by how often
its return point runs at a client before it is read: `cg-read.py seq` gives
each address's executions a call. A procedure labelled `.L` has no symbol in
the binary, and callgrind books its code under the nearest global symbol
before it in the dump, so `seq` runs over that symbol, and the return point
is the one whose loads match the offsets printed here (docs/perf-checklist.md,
B2).

Exit 0 when nothing was found, 1 when something was, 2 when DUMPS holds no
`.dump-asm`, no module's path contains SUBSTRING, or N is no number.
"""

import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dumps  # noqa: E402

LABEL = re.compile(r'^(\.?L?[\w$.]+):\s*$')
INFO = re.compile(r'_info:\s*$')
JUMP = re.compile(r'^\s+(j[a-z]+)\s+(\.L[\w$.]+)\s*$')
UNCOND = re.compile(r'^\s+(jmp\s|ret\b|ud2\b)')
PUSH_RET = re.compile(r'^\s+movq\s+\$\.Lblock_([\w$.]+)_info,')
POP = re.compile(r'^\s+addq\s+\$(\d+),%rbp\s*$')
LOAD = re.compile(r'^\s+mov\w*\s+(-?\d*)\(%rbp\),%')


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
    """The labels on a cycle: Tarjan's components of more than one node, or
    of one with an edge to itself."""
    index, low, on, stack, out, n = {}, {}, set(), [], set(), 0
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
                        out |= comp
    return out


def findings(text, least):
    """[(procedure, return point, K, [offsets])], most offsets first."""
    out = []
    for proc, blocks, rets in procedures(text.split('\n')):
        labels = [b[0] for b in blocks]
        known = set(labels)
        succ, pushed = {}, set(rets)
        for i, (lab, body) in enumerate(blocks):
            s, falls = set(), True
            for line in body:
                m = JUMP.match(line)
                if m and m.group(2) in known:
                    s.add(m.group(2))
                m = PUSH_RET.match(line)
                if m and '.L' + m.group(1) in known:
                    s.add('.L' + m.group(1))
                    pushed.add('.L' + m.group(1))
                if UNCOND.match(line):
                    falls = False
            if falls and i + 1 < len(blocks):
                s.add(labels[i + 1])
            succ[lab] = s
        loop = cyclic(labels, succ)
        for lab, body in blocks:
            if lab not in loop or lab not in pushed:
                continue
            k, loads = None, []
            for line in body:
                m = POP.match(line)
                if m:
                    k = int(m.group(1))
                    break
                m = LOAD.match(line)
                if m:
                    loads.append(int(m.group(1) or 0))
            if k is None:
                continue
            outer = sorted(o for o in loads if o >= k)
            if len(outer) >= least:
                out.append((proc, lab, k, outer))
    return sorted(out, key=lambda f: -len(f[3]))


def report(root, sub, least):
    rows, read = [], 0
    for path, key in dumps.walk(root, '.dump-asm'):
        if sub is not None and sub not in path:
            continue
        read += 1
        for proc, lab, k, outer in findings(dumps.read_text(path), least):
            rows.append((len(outer), f'{key}\t{proc}\t{lab}\t{k}\t{len(outer)}\t'
                                     + ','.join(map(str, outer))))
    rows.sort(key=lambda r: -r[0])
    return [r[1] for r in rows], read


ASM = '''
.Lf_info:
.Lc1:
\tmovq %rbx,%rax
.Lc3:
\tcmpq %r14,%rdx
\tjge .Lc4
.Lc5:
\tmovq $.Lblock_info,-16(%rbp)
\tmovq %rax,-8(%rbp)
\taddq $-16,%rbp
\ttestb $7,%bl
\tjne .Lc2
.Lc6:
\tjmp *(%rbx)
\t.long\t30
.Lblock_info:
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
\tmovq $.Lblock_info,-8(%rbp)
\taddq $-8,%rbp
\tjmp *(%rbx)
\t.long\t30
.Lblock_info:
.Lc8:
\tmovq 8(%rbp),%rax
\tmovq 16(%rbp),%rcx
\tmovq 24(%rbp),%rsi
\taddq $8,%rbp
\tjmp *(%rbp)
.Lh_info:
.Lc10:
\tcmpq %r14,%rdx
\tjge .Lc13
.Lc11:
\tmovq $.Lblock_c12_info,-8(%rbp)
\taddq $-8,%rbp
\tjmp *%rax
\t.long\t30
.Lblock_c12_info:
.Lc12:
\tmovq 8(%rbp),%rax
\tmovq 16(%rbp),%rcx
\taddq $8,%rbp
\tjmp .Lc10
.Lc13:
\tjmp *(%rbp)
'''


def self_test():
    """Three procedures: f, a loop whose continuation, reached by the fast
    path's jump, reloads three values from the enclosing frame and one from
    its own; g, a return point on no cycle; h, a loop closed only through the
    store of its named return point, as a dump with uniques prints it."""
    import tempfile
    bad = []
    got = findings(ASM, 2)
    want = [('.Lf_info', '.Lc2', 16, [16, 24, 40]), ('.Lh_info', '.Lc12', 8, [8, 16])]
    if got != want:
        bad.append(f'findings: {got}')
    if findings(ASM, 3) != want[:1]:
        bad.append('--min 3 kept the two-value loop')
    with tempfile.TemporaryDirectory() as td:
        d = os.path.join(td, 'b', 'build', 'Client')
        os.makedirs(d)
        with open(os.path.join(d, 'Ops.dump-asm'), 'w') as fh:
            fh.write(ASM)
        e = os.path.join(td, 'empty')
        os.makedirs(e)
        for argv, code, why in (([td], 1, 'findings'),
                                ([td, '--min', '4'], 0, 'nothing at --min 4'),
                                ([td, '--module', 'Client'], 1, 'a --module'),
                                ([td, '--module', 'NoSuch'], 2, 'a --module matching nothing'),
                                ([td, '--min', 'x'], 2, 'a --min that is no number'),
                                ([e], 2, 'a tree without dumps')):
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
    lines, read = report(rest[0], sub, least)
    if not read:
        print(f"no module's path contains {sub}", file=sys.stderr)
        return 2
    if lines:
        print('\n'.join(lines))
    return 1 if lines else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
