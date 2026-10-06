#!/usr/bin/env python3
"""Sweep a loop's head over every offset of a cache line and read what each
costs: the exhaustive instrument behind align-as.py's LOOP_ENTRIES.

Written for orthotope's micro-regime3 benchmark and kept there until
2026-10-06, so the README, the Runs and fillStage2 named below are that
directory's, at
https://github.com/Mikolaj/orthotope/tree/speedup-strided-tovector/micro-regime3

A probe: an input to README's placement section, run by hand. It builds a
standalone copy of a loop, steps its head through the 64 residues with a
`.p2align 6; .skip K` in front, and reads two counters per iteration off
`perf stat` -- the fill kernel differenced over two iteration counts so
that the process's own startup cancels, the straight one read from one
process of twenty million iterations, against which its startup is
nothing: cycles, and the op-cache fetches of raw event 0x28F,
which count taken branches plus window crossings on this Zen 3. For the
fill kernel it also prints what the entry count of align-as.py predicts
at each residue and the residues where the prediction and the cycles
part, which is the model's accuracy, offset by offset, independent of
the shim.

Two kernels. `fill` is the per-run cycle of `fillStage2`'s stepping loop
as Run 32's binaries laid it out, instruction for instruction: the
by-two body, the exit test, the run loop's tail and its re-entry, with
n runs of two elements read from two streams n elements apart. `straight`
is N register moves and a `dec; jnz`, one taken branch and nothing else,
which is where the smaller-piece reading came from: a cut is free with
five or more ops on each side and costs up to a cycle where a side holds
a lone branch.

    ./probe-entries-sweep.py fill                # the 64-row table, ~2 min
    ./probe-entries-sweep.py straight --movs 12  # the 40-byte control
    ./probe-entries-sweep.py fill --only 9 10 22 # a few residues

Measured 2026-09-15 on the Ryzen 7 5800X: the fill runs 4 cycles a run
at 0..8 and 22..31 and 5 or 6 elsewhere, 9 reading as 10; the entry
count reproduces 51 to 54 of the 64, missing 18, 22, 32..35 and 60..63
on every run and 19..21 on some. Needs gcc, objdump and a perf that
counts user cycles; exit 2 when one is missing or stops answering, 1 when
a build fails, 0 otherwise.
Writes only under a temporary directory. A MISS on a lone offset can be
the machine's: re-read it with `--only K --pairs 4` before believing it.
"""
import argparse
import collections
import math
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


PROBE_NAME = 'probe-entries-sweep'

RUNS = 900000
FILL = r'''
    .text
    .globl kern
    .type kern,@function
kern:
    push %rbx; push %r12; push %r13; push %r14; push %r15
    sub $0x48,%rsp
    mov %rsi,0x40(%rsp)
    mov %rcx,%r9
    mov %rdi,%rcx
    mov %rdx,%r10
    mov $2,%rdx
    xor %edi,%edi
    xor %ebx,%ebx
    xor %esi,%esi
    mov $2,%rax
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
    pop %r15; pop %r14; pop %r13; pop %r12; pop %rbx
    ret
    .section .note.GNU-stack,"",@progbits
'''
FILL_MAIN = r'''
#include <stdlib.h>
#include <stdio.h>
extern void kern(double *out, double *v, long n, long stride, long st);
int main(int argc, char **argv) {
  long reps = atol(argv[1]), n = %d;
  double *out = malloc(2 * n * sizeof(double));
  double *v = malloc(2 * n * sizeof(double));
  for (long i = 0; i < 2 * n; i++) v[i] = i;
  for (long r = 0; r < reps; r++) kern(out, v, n, n, 1);
  printf("%%f\n", out[3]);
  return 0;
}
''' % RUNS
REGS = ['%rcx', '%rdx', '%rsi', '%r8', '%r9', '%r10', '%r11', '%r12',
        '%r13', '%r14', '%r15', '%rbx']
STRAIGHT_MAIN = 'extern void kern(long);\nint main(void){kern(%d);return 0;}\n'
EVENTS = 'cycles:u,r20000078f:u'


def straight(n):
    body = '\n'.join('    mov %%rax,%s' % REGS[i % len(REGS)] for i in range(n))
    return '''
    .text
    .globl kern
    .type kern,@function
kern:
    push %%rbx; push %%r12; push %%r13; push %%r14; push %%r15
    .p2align 6
    .skip K, 0x90
head:
%s
    dec %%edi
    jnz head
    pop %%r15; pop %%r14; pop %%r13; pop %%r12; pop %%rbx
    ret
    .section .note.GNU-stack,"",@progbits
''' % body


def build(tmp, asm, cmain, k):
    """-> the binary for head offset k, or None with the error printed."""
    s, c, b = (os.path.join(tmp, f) for f in ('k.S', 'main.c', 'k%d' % k))
    with open(s, 'w') as f:
        f.write(asm)
    with open(c, 'w') as f:
        f.write(cmain)
    got = subprocess.run(['gcc', '-O1', '-DK=%d' % k, c, s, '-o', b],
                         capture_output=True, text=True)
    if got.returncode:
        print('probe-entries-sweep: gcc failed at K=%d: %s'
              % (k, got.stderr.strip().split('\n')[-1]), file=sys.stderr)
        return None
    return b


def counts(binary, arg):
    """The two counters over one process, or None when perf did not count."""
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
    return vals if len(vals) == 2 else None


def layout(binary):
    """(offset from head, length, mnemonic) of every instruction from `head`
    to the `ret`, read off objdump, so the model prices the bytes the
    assembler emitted and not the bytes the source names."""
    got = subprocess.run(['objdump', '-d', binary], capture_output=True,
                         text=True)
    if got.returncode:
        die('%s: objdump -d %s exited %d' % (PROBE_NAME, binary,
                                             got.returncode))
    out = got.stdout
    sec = out[out.index('<head>:'):]
    sec = sec[:sec.index('\tret')]
    rows, head = [], None
    for line in sec.split('\n'):
        m = re.match(r'^\s*([0-9a-f]+):\t([0-9a-f ]+?)\t(\S+)', line)
        if not m:
            continue
        a = int(m.group(1), 16)
        if head is None:
            head = a
        rows.append((a - head, len(m.group(2).split()), m.group(3)))
    return rows


def segments(rows):
    """The fill cycle's straight segments as (start, end) lists: the body
    through `jge`, the tail from `L3` through `jmp`, the re-entry `lea; cmp;
    jl` -- executed in that order once a run, each ended by a taken branch."""
    ends = [(o, o + n) for o, n, _ in rows]
    names = [m for _, _, m in rows]
    jl = names.index('jl')
    jge = names.index('jge')
    jmp = names.index('jmp')
    body = ends[:jge + 1]
    tail = ends[jge + 4:jmp + 1]
    entry = ends[jl - 2:jl + 1]
    return [body, tail, entry]


def entries(seg, k, window=64, per=8):
    pieces = collections.Counter((k + end - 1) // window for _, end in seg)
    return sum(math.ceil(n / per) for n in pieces.values())


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('kernel', choices=['fill', 'straight'])
    ap.add_argument('--movs', type=int, default=12,
                    help='register moves in the straight loop (default 12)')
    ap.add_argument('--only', type=int, nargs='+', metavar='K',
                    help='these head offsets only (default all 64); the'
                         ' fill kernel reads 0 first regardless, as the base')
    ap.add_argument('--pairs', type=int, default=2,
                    help='differenced pairs per offset, the least taken'
                         ' (default 2)')
    args = ap.parse_args()
    for tool in ('gcc', 'perf', 'objdump'):
        if shutil.which(tool) is None:
            die('probe-entries-sweep: %s is not on PATH; nothing ran'
                % tool)
    probe = counts('/bin/true', '')
    if probe is None:
        die('probe-entries-sweep: perf does not count %s here'
            ' (kernel.perf_event_paranoid?); nothing ran' % EVENTS)
    ks = args.only or list(range(64))
    if args.kernel == 'fill' and ks[0] != 0:
        ks = [0] + ks              # the model's base is residue 0, measured
    if args.kernel == 'fill':
        asm, cmain, iters, per = FILL, FILL_MAIN, (200, 100), RUNS
    else:
        asm, cmain, per = straight(args.movs), STRAIGHT_MAIN % 20000000, 20000000
        iters = (2, 1)         # one process read whole, the second ignored
    tmp = tempfile.mkdtemp(prefix='entries-sweep-')
    print('K  cycles/iter  fetches/iter' + ('  entries  model  verdict'
                                             if args.kernel == 'fill' else ''))
    base = None
    mism = []
    try:
        for k in ks:
            b = build(tmp, asm, cmain, k)
            if b is None:
                return 1
            readings = []
            for _ in range(args.pairs):
                hi, lo = counts(b, iters[0]), counts(b, iters[1])
                if hi is None or lo is None:
                    die('probe-entries-sweep: perf stopped counting at'
                        ' K=%d; the rows above stand' % k)
                if args.kernel == 'fill':
                    d = 100
                else:
                    d, lo = 1, [0, 0]     # one process carries every iteration
                readings.append(tuple((h - l) / d / per for h, l in zip(hi, lo)))
            cyc = min(r[0] for r in readings)
            opc = min(r[1] for r in readings)
            row = '%2d  %10.2f  %12.2f' % (k, cyc, opc)
            if args.kernel == 'fill':
                segs = segments(layout(b))
                e = sum(entries(s, k) for s in segs)
                if base is None:      # residue 0: the cycles and entries
                    base = (e, round(cyc))     # every other row is read against
                model = base[1] + e - base[0]
                verdict = 'ok' if round(cyc) == model else 'MISS'
                if verdict == 'MISS':
                    mism.append(k)
                row += '  %7d  %5d  %s' % (e, model, verdict)
            print(row, flush=True)
        if args.kernel == 'fill':
            print('entry count against the cycles: %d of %d offsets miss%s'
                  % (len(mism), len(ks),
                     ': ' + ' '.join(map(str, mism)) if mism else ''))
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    return 0


if __name__ == '__main__':
    sys.exit(main())
