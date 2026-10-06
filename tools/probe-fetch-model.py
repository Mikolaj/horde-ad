#!/usr/bin/env python3
"""Score the Zen 3 guide's front-end rules against measured cycles, offset by
offset, on generated loops: the experiments README's placement section
registers, run as one probe.

Written for orthotope's micro-regime3 benchmark and kept there until
2026-10-06, so the README, the Runs and fillStage2 named below are that
directory's, at
https://github.com/Mikolaj/orthotope/tree/speedup-strided-tovector/micro-regime3

A kernel is generated from a description, its head swept over the 64
residues of a line with `.p2align 6; .skip K`, and per residue four
counters are read per iteration, the fill differenced over two iteration
counts and the straight loop read from one process of twenty million:
cycles, op-cache fetch blocks (0x28F), L1 BTB overrides (0x8A) and L2 BTB
overrides (0x8B). From the assembled layout, read off objdump, the probe
predicts each residue's cost under rules read off section 2.8 of the
Zen 3 optimization guide and the nine sweeps of 2026-09-15 (README, the
placement section):

  blocks   one aligned 64-byte fetch block a cycle: a segment of the
           executed path is cut at every line boundary, each piece a
           block, and a first instruction astride the boundary leaves an
           empty block behind that is fetched like any other
  cut      a whole cycle: a segment's taken conditional branch, or the
           fused pair it belongs to, astride the boundary or ending in a
           different line from the segment's previous predicted branch --
           the guide's rule that two branches share a BTB entry only when
           their last bytes share a line. A not-taken conditional or an
           unconditional jmp cut the same way pays nothing beyond its block
  head     a whole cycle: the loop head within HEAD_TAIL bytes of its
           line's end, the guide's shortened fetch block; a tail or
           re-entry segment entered there pays only the empty block
  half     half cycles: a cut that leaves a last block of three or fewer
           instructions starting in its line, a block holding only a jmp,
           and a quarter for a taken conditional that is not fused

and a fourth, the dispatcher's six ops a cycle, as a floor. Predicted
cycles are max(ops / 6, blocks) plus the penalties, whole where the
fetch bounds the loop and halved where the dispatcher does, and a
residue is a MISS where the measurement is more than half a cycle away. The verdict
of a sweep is how many residues miss and which rule the misses implicate,
which is what the model needs before the shim can carry a cost built on
it.

Kernels:
  straight N W END   N register ops of width W bytes (3 or 6), one loop,
                     ending END: `fused` (dec; jnz), `split` (dec; op; jnz)
                     or `jmp` (jz out early, jmp back), 20M iterations
  fill R             fillStage2's per-run cycle as Run 32 laid it out,
                     runs of R elements (2, 4, 8, ...), 1.8M elements

    ./probe-fetch-model.py straight 12 3 fused | tee probe-fetch-model-s12.txt
    ./probe-fetch-model.py fill 2 --only 5 9 22 32 60
    ./probe-fetch-model.py rescore probe-fetch-model-s12.txt   # rules only

A saved table carries the kernel and its assembled layout, so `rescore`
re-applies the rules as they stand in this file to the measurements
without the machine, which is how a rule is changed and judged.

Needs gcc, objdump and a perf that counts user cycles; exit 2 when one is
missing or stops answering, or a table to rescore is unreadable, 1 when a
build fails. Writes only under a temporary directory.
Written 2026-09-15; the rules are the guide's sentences and the scoring
is the probe's own, so a rule that scores is evidence and one that does
not is a rule the sweep refutes on this core.
"""
import argparse
import collections
import os
import re
import shutil
import subprocess
import sys
import tempfile


def die(msg):
    """Exit 2 -- did not run -- rather than `sys.exit(str)`'s 1, which is
    the code a finding gets (2026-09-25, by review)."""
    sys.stderr.write(msg.rstrip('\n') + '\n')
    sys.exit(2)


PROBE_NAME = 'probe-fetch-model'

EVENTS = 'cycles:u,r20000078f:u,r08a:u,r08b:u'
NAMES = ['cyc', 'blocks', 'l1btb', 'l2btb']
REGS = ['%rcx', '%rdx', '%rsi', '%r8', '%r9', '%r10', '%r11', '%r12',
        '%r13', '%r14', '%r15', '%rbx']
REGS32 = ['%ecx', '%edx', '%esi', '%r8d', '%r9d', '%r10d', '%r11d', '%r12d',
          '%r13d', '%r14d', '%r15d', '%ebx']
ELEMS = 1800000
DEBUG = os.environ.get('FETCH_MODEL_DEBUG', '') not in ('', '0')
FUSABLE = {'cmp', 'test', 'add', 'sub', 'and', 'or', 'xor', 'inc', 'dec'}

PROLOGUE = '''
    .text
    .globl kern
    .type kern,@function
kern:
    push %rbx; push %r12; push %r13; push %r14; push %r15
'''
EPILOGUE = '''
    pop %r15; pop %r14; pop %r13; pop %r12; pop %rbx
    ret
    .section .note.GNU-stack,"",@progbits
'''


def straight(n, width, end):
    if width == 3:
        ops = ['    mov %%rax,%s' % REGS[i % len(REGS)] for i in range(n)]
    else:
        ops = ['    and $0x7fffffff,%s' % REGS32[i % len(REGS32)]
               for i in range(n)]
    body = '\n'.join(ops)
    if end == 'fused':
        tail = '    dec %edi\n    jnz head'
        pre = ''
    elif end == 'split':
        tail = '    dec %edi\n    mov %rax,%rcx\n    jnz head'
        pre = ''
    else:
        pre = '    dec %edi\n    jz out\n'
        tail = '    jmp head'
    return (PROLOGUE + '    .p2align 6\n    .skip K, 0x90\nhead:\n' + pre
            + body + '\n' + tail + '\nout:' + EPILOGUE)


FILL = '''
    sub $0x48,%rsp
    mov %rsi,0x40(%rsp)
    mov %rcx,%r9
    mov %rdi,%rcx
    mov %rdx,%r10
    mov $R,%rdx
    xor %edi,%edi
    xor %ebx,%ebx
    xor %esi,%esi
    mov $R,%rax
    jmp L2
    .p2align 6
    .skip K, 0x90
head:
    mov 0x40(%rsp),%r11
    movsd (%r11,%rbx,8),%xmm0
    movsd %xmm0,(%rcx,%rsi,8)
    add %r9,%rbx
    movsd (%r11,%rbx,8),%xmm0
    lea 1(%rsi),%r14
    movsd %xmm0,(%rcx,%r14,8)
    add %r9,%rbx
    add $2,%rsi
L2: lea 1(%rsi),%r11
    cmp %rax,%r11
    jl head
    cmp %rax,%rsi
    jge L3
    mov 0x40(%rsp),%r11
    movsd (%r11,%rbx,8),%xmm0
    movsd %xmm0,(%rcx,%rsi,8)
L3: add %r8,%rdi
    dec %r10
    mov %rax,%rsi
    test %r10,%r10
    jle done
    mov %rsi,%rax
    add %rdx,%rax
    mov %rdi,%rbx
    jmp L2
done:
    add $0x48,%rsp
'''
FILL_MAIN = '''
#include <stdlib.h>
#include <stdio.h>
extern void kern(double *out, double *v, long n, long stride, long st);
int main(int argc, char **argv) {
  long reps = atol(argv[1]), n = %d, r = %d;   /* n runs of r elements */
  double *out = malloc(r * n * sizeof(double));
  double *v = malloc(r * n * sizeof(double));
  for (long i = 0; i < r * n; i++) v[i] = i;
  for (long r = 0; r < reps; r++) kern(out, v, n, n, 1);
  printf("%%f\\n", out[3]);
  return 0;
}
'''
STRAIGHT_MAIN = 'extern void kern(long);\nint main(void){kern(20000000);return 0;}\n'


def build(tmp, asm, cmain, k):
    s, c, b = (os.path.join(tmp, f) for f in ('k.S', 'main.c', 'k%d' % k))
    with open(s, 'w') as f:
        f.write(asm)
    with open(c, 'w') as f:
        f.write(cmain)
    got = subprocess.run(['gcc', '-O1', '-DK=%d' % k, c, s, '-o', b],
                         capture_output=True, text=True)
    if got.returncode:
        print('probe-fetch-model: gcc failed at K=%d: %s'
              % (k, got.stderr.strip().split('\n')[-1]), file=sys.stderr)
        return None
    return b


def counts(binary, arg):
    with tempfile.NamedTemporaryFile(delete=False) as f:
        out = f.name
    ran = subprocess.run(['perf', 'stat', '-x,', '-e', EVENTS, '-o', out,
                          binary, str(arg)], stdout=subprocess.DEVNULL,
                         stderr=subprocess.DEVNULL)
    if ran.returncode:
        os.unlink(out)
        return None
    vals = []
    with open(out) as f:
        for line in f:
            p = line.split(',')
            if len(p) > 3 and p[0].strip().isdigit():
                vals.append(int(p[0]))
    os.unlink(out)
    return vals if len(vals) == len(NAMES) else None


def layout(binary):
    """[(abs address, length, mnemonic, label-or-None)] from head to ret."""
    got = subprocess.run(['objdump', '-d', binary], capture_output=True,
                         text=True)
    if got.returncode:
        die('%s: objdump -d %s exited %d' % (PROBE_NAME, binary,
                                             got.returncode))
    out = got.stdout
    sec = out[out.index('<head>:'):]
    sec = sec[:sec.index('\tret')]
    rows, label = [], 'head'
    for line in sec.split('\n'):
        m = re.match(r'^[0-9a-f]+ <(\w+)>:', line)
        if m:
            label = m.group(1)
            continue
        m = re.match(r'^\s*([0-9a-f]+):\t([0-9a-f ]+?)\t(\S+)', line)
        if not m:
            continue
        rows.append((int(m.group(1), 16), len(m.group(2).split()),
                     m.group(3), label))
        label = None
    return rows


def path_straight(rows, end):
    """The executed path as segments, each a list of instruction indices
    ending in a taken branch: head through the backward jump, the
    epilogue after `out` excluded; under `jmp` the jz is not taken."""
    out = next(i for i, row in enumerate(rows) if row[3] == 'out')
    return [list(range(out))]


def path_fill(rows, r):
    lab = {row[3]: i for i, row in enumerate(rows) if row[3]}
    head, l2, l3 = lab['head'], lab['L2'], lab['L3']
    jl = next(i for i in range(l2, len(rows)) if rows[i][2] == 'jl')
    jge = next(i for i in range(jl, len(rows)) if rows[i][2] == 'jge')
    jmp = next(i for i in range(l3, len(rows)) if rows[i][2] == 'jmp')
    entry = list(range(l2, jl + 1))                    # lea; cmp; jl taken
    body_taken = list(range(head, jl + 1))             # ... jl taken
    body_exit = list(range(head, jge + 1))             # jl not taken; jge taken
    tail = list(range(l3, jmp + 1))
    return [entry] + [body_taken] * (r // 2 - 1) + [body_exit, tail]


HEAD_TAIL = 8             # a head this close to the line's end pays a cycle


def is_cond(mn):
    return mn.startswith('j') and mn != 'jmp'


def whole_in_last(pieces):
    """Instructions of a segment's last block that start in its line: a
    straddler counted by its last byte belongs to the block's line but
    not to what the block delivers."""
    line, ins = list(pieces.items())[-1]
    return sum(1 for i in ins if ROWS_K[i] // 64 == line)


def predict(rows, segs, k, head_addr, body_first=True):
    """-> (ops, blocks, whole, half, predicted cycles) for head offset k.

    Whole-cycle penalties, the rules the sweeps of 2026-09-15 bear out
    in every regime: `cut`, a segment's taken conditional branch, or the
    fused pair it belongs to, astride a line boundary or in a different
    line from the segment's previous predicted branch; `head`, the loop
    head within HEAD_TAIL bytes of its line's end, charged on the body
    alone since a tail or re-entry entered there reads nothing. Half
    ones: a last block with three or fewer instructions starting in its
    line, a block holding only an unconditional jump, and a quarter for
    an unfused taken conditional. A first instruction astride the
    boundary adds the empty block it leaves. Predicted cycles are
    max(ops / 6, blocks) plus the penalties, whole where the fetch bounds
    the loop and halved where the dispatcher does; a residue fits within
    half a cycle.
    """
    global ROWS_K
    ROWS_K = {i: row[0] - head_addr + k for i, row in enumerate(rows)}
    ops = blocks = whole = half = 0
    for n_seg, seg in enumerate(segs):
        n = len(seg)
        for a, b in zip(seg, seg[1:]):
            if rows[a][2] in FUSABLE and rows[b][2].startswith('j'):
                n -= 1
        ops += n
        pieces = collections.OrderedDict()
        for i in seg:
            off = rows[i][0] - head_addr + k
            pieces.setdefault((off + rows[i][1] - 1) // 64, []).append(i)
        blocks += len(pieces)
        last = seg[-1]
        last_mn = rows[last][2]
        fused = (last - 1 >= seg[0] and rows[last - 1][2] in FUSABLE
                 and is_cond(last_mn))
        first_byte = rows[last - 1 if fused else last][0] - head_addr + k
        last_byte = rows[last][0] - head_addr + k + rows[last][1] - 1
        if is_cond(last_mn):
            cut = first_byte // 64 != last_byte // 64
            prev = [i for i in seg[:-1] if rows[i][2].startswith('j')
                    and not (fused and i == last - 1)]
            if not cut and prev:
                pe = rows[prev[-1]][0] - head_addr + k + rows[prev[-1]][1] - 1
                cut = pe // 64 != last_byte // 64
            if cut:
                whole += 1
            if not fused:
                half += 0.5            # an unfused taken conditional, a quarter
            if len(pieces) > 1 and whole_in_last(pieces) <= 3 and not cut:
                half += 1              # a cut leaving a short last block
        elif last_mn == 'jmp':
            if whole_in_last(pieces) <= 1:
                half += 1
        # a segment whose first instruction straddles the boundary leaves
        # an empty fetch block behind, fetched like any other: 19..21 and
        # 54..55 of the fill read one block more than the pieces. The loop
        # head pays a cycle beyond that when its block holds fewer than
        # two whole instructions, 56..63; a tail or re-entry does not.
        fo = rows[seg[0]][0] - head_addr + k
        straddles = fo // 64 != (fo + rows[seg[0]][1] - 1) // 64
        if straddles:
            blocks += 1
        if body_first and n_seg == 0 or rows[seg[0]][3] == 'head':
            if fo % 64 >= 64 - HEAD_TAIL:
                whole += 1
    # penalties are whole cycles where the fetch bounds the loop and half
    # where the dispatcher does: the 64-byte straight loop pays 0.5 at a
    # cut its 3.5-cycle dispatch floor absorbs, the fill pays 1 at 4
    # blocks over a 3.67 floor
    floor = max(ops / 6.0, blocks)
    w = 1.0 if blocks >= ops / 6.0 else 0.5
    pred = floor + w * (whole + half / 2.0)
    return ops, blocks, whole, half, pred


def fits(cyc, pred):
    """Within half a cycle, rather than rounding both: a loop whose floor
    is 2.5 cycles reads 2.4 or 2.6 by the machine's mood."""
    return abs(cyc - pred) <= 0.5


def rescore(path):
    """Re-apply the rules to a saved table: the layout line rebuilds the
    rows, the kernel line the path, and every K row is scored again, so a
    rule can be changed and judged without the machine."""
    rows, kernel, args, meas = [], None, [], []
    for line in open(path):
        if line.startswith('# kernel:'):
            p = line.split()[2:]
            kernel, args = p[0], p[1:]
        elif line.startswith('# layout:'):
            for tok in line.split()[2:]:
                lab = None
                if ':' in tok:
                    lab, tok = tok.split(':', 1)
                mn, rest = tok.rsplit('+', 1)
                off, ln = rest.split('/')
                rows.append((int(off), int(ln), mn, lab))
        elif line[:1].isdigit() or line[:2].strip().isdigit():
            f = line.split()
            if len(f) >= 5 and f[0].isdigit():
                meas.append((int(f[0]), float(f[1]), float(f[2]),
                             float(f[3]), float(f[4])))
    if not rows or not meas:
        die('probe-fetch-model: %s carries no layout or no rows' % path)
    if kernel == 'fill':
        segs = path_fill(rows, int(args[0]) if args else 2)
    else:
        segs = path_straight(rows, args[2])
    miss = []
    print('# rescored %s: %s %s' % (path, kernel, ' '.join(args)))
    for k, cyc, blk, l1, l2 in meas:
        ops, blocks, split, short, pred = predict(rows, segs, k, 0, body_first=False)
        ok = fits(cyc, pred)
        if not ok:
            miss.append(k)
        print('%2d %6.2f %6.2f %6.2f %6.2f | %4d %6d %5d %5d %6.2f %s'
              % (k, cyc, blk, l1, l2, ops, blocks, split, short, pred,
                 'ok' if ok else 'MISS'))
    print('# %d of %d residues miss%s' % (len(miss), len(meas),
          ': ' + ' '.join(map(str, miss)) if miss else ''))
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('kernel', choices=['straight', 'fill', 'rescore'])
    ap.add_argument('args', nargs='*')
    ap.add_argument('--only', type=int, nargs='+', metavar='K')
    ap.add_argument('--pairs', type=int, default=2)
    args = ap.parse_args()
    if args.kernel == 'rescore':
        return rescore(args.args[0])
    for tool in ('gcc', 'perf', 'objdump'):
        if shutil.which(tool) is None:
            die('probe-fetch-model: %s is not on PATH; nothing ran' % tool)
    if counts('/bin/true', '') is None:
        die('probe-fetch-model: perf does not count %s here; nothing ran'
            % EVENTS)
    if args.kernel == 'straight':
        n, w, end = int(args.args[0]), int(args.args[1]), args.args[2]
        asm, cmain, per, iters = straight(n, w, end), STRAIGHT_MAIN, 20000000, (2, 1)
        title = 'straight N=%d W=%d %s' % (n, w, end)
    else:
        r = int(args.args[0]) if args.args else 2
        asm = PROLOGUE + FILL.replace('$R', '$%d' % r) + EPILOGUE
        cmain, per, iters = FILL_MAIN % (ELEMS // r, r), ELEMS // r, (200, 100)
        title = 'fill R=%d' % r
    ks = args.only or list(range(64))
    tmp = tempfile.mkdtemp(prefix='fetch-model-')
    print('# %s; per iteration: measured cycles, fetch blocks, L1 and L2 BTB'
          ' overrides; predicted ops, blocks, whole, half, cycles' % title)
    print('%2s %6s %6s %6s %6s | %4s %6s %5s %5s %6s %s'
          % ('K', 'cyc', 'blk', 'l1', 'l2', 'ops', 'blocks', 'whole',
             'half', 'pred', 'verdict'))
    miss = []
    try:
        for k in ks:
            b = build(tmp, asm, cmain, k)
            if b is None:
                return 1
            reads = []
            for _ in range(args.pairs):
                hi, lo = counts(b, iters[0]), counts(b, iters[1])
                if hi is None or lo is None:
                    die('probe-fetch-model: perf stopped counting at K=%d' % k)
                if args.kernel == 'fill':
                    reads.append(tuple((h - l) / 100 / per for h, l in zip(hi, lo)))
                else:
                    reads.append(tuple(h / per for h in hi))
            m = [min(r[i] for r in reads) for i in range(len(NAMES))]
            rows = layout(b)
            head_addr = rows[0][0]
            if k == ks[0]:
                print('# kernel: %s %s' % (args.kernel, ' '.join(args.args)))
                print('# layout: ' + ' '.join('%s%s+%d/%d' % (
                    (row[3] + ':') if row[3] else '', row[2],
                    row[0] - head_addr, row[1]) for row in rows))
            if args.kernel == 'fill':
                segs = path_fill(rows, r)
            else:
                segs = path_straight(rows, end)
            ops, blocks, split, short, pred = predict(rows, segs, k, head_addr, body_first=False)
            ok = fits(m[0], pred)
            if not ok:
                miss.append(k)
            print('%2d %6.2f %6.2f %6.2f %6.2f | %4d %6d %5d %5d %6.2f %s'
                  % (k, m[0], m[1], m[2], m[3], ops, blocks, split, short,
                     pred, 'ok' if ok else 'MISS'), flush=True)
        print('# %s: %d of %d residues miss%s'
              % (title, len(miss), len(ks),
                 ': ' + ' '.join(map(str, miss)) if miss else ''))
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    return 0


if __name__ == '__main__':
    sys.exit(main())
