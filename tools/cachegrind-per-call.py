#!/usr/bin/env python3
"""Instructions and estimated cycles per call of one criterion benchmark,
from cachegrind, for where `perf stat` cannot run.

Usage: python3 tools/cachegrind-per-call.py BENCH_BINARY NAME N [--no-cache-sim]
       python3 tools/cachegrind-per-call.py --self-test

Runs the benchmark binary twice under `valgrind --tool=cachegrind`, with
`--iters 2N` and with `--iters N`, selecting NAME exactly (`-m glob NAME`),
and prints the difference over N: the instructions per call and, with the
cache simulation on (the default), the estimated cycles per call,

    Ir + 10 * (I1mr + D1mr + D1mw) + 100 * (ILmr + DLmr + DLmw)

the usual estimate from L1 and last-level misses. The difference of the two
runs cancels the process's setup, which for `shortProdForCI` alone is some
40 G instructions; cachegrind is deterministic up to the program's own
nondeterminism, so N need not be large --- the measured program runs about
50 times slower under it, the simulation slower still, so size N for well
under a second of native work. Two builds are compared by running this on
each; for a banned-or-not decision about a slowdown, this is the instrument
to back an interleaved wall-time A/B with (docs/perf-checklist.md).

The cachegrind output is written under the system temporary directory and
removed. Exit 0 when the figures were printed, 2 when they could not be:
valgrind missing, a run failing, or its output without the counts.
"""

import os
import shutil
import subprocess
import sys
import tempfile

WEIGHTS = {'Ir': 1, 'I1mr': 10, 'D1mr': 10, 'D1mw': 10,
           'ILmr': 100, 'DLmr': 100, 'DLmw': 100}


def counts(path):
    """Event name -> total, from a cachegrind output file."""
    events = summary = None
    with open(path) as fh:
        for line in fh:
            if line.startswith('events:'):
                events = line.split()[1:]
            elif line.startswith('summary:'):
                summary = [int(x) for x in line.split()[1:]]
    if events is None or summary is None or len(events) != len(summary):
        raise ValueError(f'{path} has no events and summary lines to match')
    return dict(zip(events, summary))


def cycles(c):
    """Estimated cycles, or None without the cache simulation's events."""
    if not all(k in c for k in WEIGHTS):
        return None
    return sum(w * c[k] for k, w in WEIGHTS.items())


def per_call(c1, c2, n):
    """(instructions, estimated cycles or None) per call from the N and 2N
    runs."""
    y1, y2 = cycles(c1), cycles(c2)
    return ((c2['Ir'] - c1['Ir']) / n,
            None if y1 is None or y2 is None else (y2 - y1) / n)


def run(binary, name, iters, sim, out):
    cmd = ['valgrind', '--tool=cachegrind',
           f'--cache-sim={"yes" if sim else "no"}',
           f'--cachegrind-out-file={out}',
           binary, '--iters', str(iters), '-m', 'glob', name]
    r = subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
                       text=True)
    if r.returncode != 0:
        raise ValueError(f'{" ".join(cmd)} exited {r.returncode}:\n'
                         + r.stderr[-2000:])
    return counts(out)


def self_test():
    """The file parsing and the arithmetic, on two synthetic outputs."""
    bad = []
    with tempfile.TemporaryDirectory() as td:
        def write(name, ir, i1, d1r, d1w, il, dlr, dlw):
            p = os.path.join(td, name)
            with open(p, 'w') as fh:
                fh.write('desc: I1 cache: 32768 B, 64 B, 8-way associative\n'
                         'cmd: ./bench --iters 10\n'
                         'events: Ir I1mr ILmr Dr D1mr DLmr Dw D1mw DLmw\n'
                         'fl=x.c\nfn=main\n1 1 0 0 0 0 0 0 0 0\n'
                         f'summary: {ir} {i1} {il} 7 {d1r} {dlr} 9 {d1w} {dlw}\n')
            return p
        c1 = counts(write('n', 1000, 10, 20, 30, 1, 2, 3))
        c2 = counts(write('2n', 3000, 30, 60, 90, 3, 6, 9))
        if cycles(c1) != 1000 + 10 * 60 + 100 * 6:
            bad.append(f'cycles of the N run: {cycles(c1)}')
        got = per_call(c1, c2, 10)
        if got != (200.0, (3000 + 10 * 180 + 100 * 18 - 2200) / 10):
            bad.append(f'per call: {got}')
        nosim = os.path.join(td, 'nosim')
        with open(nosim, 'w') as fh:
            fh.write('events: Ir\nsummary: 500\n')
        if per_call(counts(nosim), {'Ir': 900}, 4) != (100.0, None):
            bad.append('without the cache simulation, cycles were not None')
        broken = os.path.join(td, 'broken')
        with open(broken, 'w') as fh:
            fh.write('events: Ir I1mr\nsummary: 5\n')
        try:
            counts(broken)
            bad.append('a summary shorter than its events was accepted')
        except ValueError:
            pass
    for b in bad:
        print('FAIL', b)
    print('self-test', 'FAILED' if bad else 'passed')
    return 1 if bad else 0


def main(argv):
    if argv == ['--self-test']:
        return self_test()
    sim = '--no-cache-sim' not in argv
    argv = [a for a in argv if a != '--no-cache-sim']
    if len(argv) != 3 or not argv[2].isdigit() or int(argv[2]) < 1:
        print(__doc__.split('\n\n')[1], file=sys.stderr)
        return 2
    binary, name, n = argv[0], argv[1], int(argv[2])
    if shutil.which('valgrind') is None:
        print('valgrind is not on PATH; nothing measured', file=sys.stderr)
        return 2
    with tempfile.TemporaryDirectory() as td:
        try:
            c1 = run(binary, name, n, sim, os.path.join(td, 'n.out'))
            c2 = run(binary, name, 2 * n, sim, os.path.join(td, '2n.out'))
        except (ValueError, OSError) as e:
            print(e, file=sys.stderr)
            return 2
    ins, cyc = per_call(c1, c2, n)
    print(f'{name}: instructions/call {ins:.0f}'
          + (f'  estimated cycles/call {cyc:.0f}' if cyc is not None else ''))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
