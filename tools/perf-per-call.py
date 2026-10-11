#!/usr/bin/env python3
"""Instructions and cycles per call of one criterion benchmark across
builds, from `perf stat`.

Usage: python3 tools/perf-per-call.py [--cpu CPU] [--reps R]
                                      BIN [BIN ...] NAME N
       python3 tools/perf-per-call.py --self-test

Each BIN is the same benchmark executable from another build, labelled A,
B, ... in the order given. Runs each under `perf stat -e
instructions:u,cycles:u` with `--iters N` and with `--iters 2N`, selecting
NAME exactly (`-m glob NAME`), and takes the difference over N, which
cancels the process's setup: the instructions and cycles per call. Every
BIN runs at both counts once a repetition, R repetitions (3 by default),
the builds' order rotated by one and the two counts' order swapped from
repetition to repetition; with `--cpu`, every run is pinned to CPU by
`taskset -c`. Prints, per BIN, its instructions and cycles per call with
the range of the repetitions' differences and, for each BIN after the
first, its figures over A's.

Instructions repeat closely but for a fixed amount the RTS clock adds to
some processes (56M on top of 39750M in five runs of fourteen of one
benchmark built by GHC 10.1.20260918, and in none of eight under
GHCRTS=-V0, which stops the clock). It lifts a repetition's difference by
that amount over N whenever one of its two runs carries it and the other
does not. So the instructions per call are the lowest 2N count less the
lowest N count, over N, and they are what decides --- unless every run at
one count carries the amount, as all nine 2N runs of one build did on one
row of that benchmark. The differences then spread by the amount unless
no run at the other count carries it either, and where they spread over
more than 1% of the figure the tool says so. Cycles carry the machine's
noise: their figure is the repetitions' median, the range showing the
noise. This is the native counterpart of tools/cachegrind-per-call.py,
which estimates cycles from a cache model where `perf stat` cannot run,
at fifty times the run time or more.

Exit 0 when the figures were printed, 1 when they were and some build's
instruction differences spread over more than 1% of its figure, 2 when
they could not be: perf, or taskset with `--cpu`, missing, a run failing,
or its output without a counted instructions:u and cycles:u.
"""

import os
import shutil
import statistics
import subprocess
import sys
import tempfile

EVENTS = ('instructions', 'cycles')

# How far a build's instruction differences may spread, as a fraction of
# its figure, before the tool says so.
SPAN = 0.01

# The self-test runs a fake in its place.
PERF = ['perf']


def command(binary, name, iters, out, cpu):
    """One counted run, pinned to cpu unless it is None."""
    return ((['taskset', '-c', cpu] if cpu is not None else []) + PERF
            + ['stat', '-x', ',', '-o', out,
               '-e', ','.join(e + ':u' for e in EVENTS), '--',
               binary, '--iters', str(iters), '-m', 'glob', name])


def counts(path):
    """Event -> count, from a `perf stat -x ,` output file."""
    found = {}
    with open(path) as fh:
        for line in fh:
            f = line.rstrip('\n').split(',')
            if len(f) < 3 or line.startswith('#'):
                continue
            event = f[2].split(':')[0]
            if event in EVENTS:
                if not f[0].isdigit():
                    raise ValueError(f'{path}: {f[2]} reads {f[0]!r}')
                found[event] = int(f[0])
    missing = [e for e in EVENTS if e not in found]
    if missing:
        raise ValueError(f'{path} has no count of {", ".join(missing)}')
    return found


def per_call(c1, c2, n):
    """Event -> count per call, from the N and 2N runs."""
    return {e: (c2[e] - c1[e]) / n for e in EVENTS}


def estimate(runs, n):
    """Event -> (per call, lowest, highest), from one BIN's runs: the
    instructions the lowest 2N count less the lowest N count, the cycles
    the median of the repetitions' differences, the bounds theirs."""
    diffs = [per_call(c1, c2, n) for c1, c2 in zip(runs[1], runs[2])]
    est = {}
    for e in EVENTS:
        xs = [d[e] for d in diffs]
        if e == 'instructions':
            mid = (min(c[e] for c in runs[2]) - min(c[e] for c in runs[1])) / n
        else:
            mid = statistics.median(xs)
        est[e] = (mid, min(xs), max(xs))
    return est


def run(binary, name, iters, cpu, out):
    cmd = command(binary, name, iters, out, cpu)
    r = subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
                       text=True)
    if r.returncode != 0:
        raise ValueError(f'{" ".join(cmd)} exited {r.returncode}:\n'
                         + r.stderr[-2000:])
    return counts(out)


def measure(bins, name, n, reps, cpu, td):
    """Per BIN, k -> the counts of its runs at k * N, one a repetition."""
    got = [{1: [], 2: []} for _ in bins]
    out = os.path.join(td, 'perf.txt')
    for r in range(reps):
        for i in range(len(bins)):
            j = (i + r) % len(bins)
            for k in ((1, 2) if r % 2 == 0 else (2, 1)):
                got[j][k].append(run(bins[j], name, k * n, cpu, out))
    return got


FAKE = '''#!/usr/bin/env python3
import sys
a = sys.argv
out, rest = a[a.index('-o') + 1], a[a.index('--') + 1:]
binary, iters = rest[0], int(rest[rest.index('--iters') + 1])
tag = binary.rsplit('/', 1)[-1]
with open({calls!r}, 'a') as fh:
    fh.write(tag + ' ' + str(iters) + chr(10))
if tag == 'F':
    sys.exit(1)
ins, cyc = {{'A': (7, 3), 'B': (9, 4), 'U': (7, 3), 'M': (7, 3),
            'Q': (7, 3), 'W': (7, 3)}}[tag]
with open({calls!r}) as fh:
    k = [line.split()[0] for line in fh].count(tag)
xi, xc = {{'Q': (500 if k in (2, 3) else 0, 500 if k == 2 else 0),
          'W': (500 if iters == 20 or k == 1 else 0, 0)}}.get(tag, (0, 0))
with open(out, 'w') as fh:
    fh.write('# started on Mon Oct  6 12:00:00 2026' + chr(10) + chr(10))
    fh.write(str(1000 + xi + ins * iters) + ',,instructions:u,100,100.00,,'
             + chr(10))
    if tag != 'M':
        fh.write(('<not counted>' if tag == 'U'
                  else str(500 + xc + cyc * iters))
                 + ',,cycles:u,100,100.00,,' + chr(10))
'''


def self_test():
    """The parsing, the differencing and the order of the runs, with a fake
    perf whose counts are a setup plus a fixed cost per call, for build Q
    a setup that its second and third runs add to, the second in cycles
    too, and for build W one that its 2N runs and its first run add to."""
    global PERF
    bad = []
    with tempfile.TemporaryDirectory() as td:
        calls = os.path.join(td, 'calls')
        fake = os.path.join(td, 'perf')
        with open(fake, 'w') as fh:
            fh.write(FAKE.format(calls=calls))
        os.chmod(fake, 0o755)
        saved, PERF = PERF, [fake]
        try:
            a, b = os.path.join(td, 'A'), os.path.join(td, 'B')
            got = [estimate(g, 10)
                   for g in measure([a, b], 'g/x', 10, 2, None, td)]
            if got != [{'instructions': (7.0, 7.0, 7.0),
                        'cycles': (3.0, 3.0, 3.0)},
                       {'instructions': (9.0, 9.0, 9.0),
                        'cycles': (4.0, 4.0, 4.0)}]:
                bad.append(f'per call: {got}')
            with open(calls) as fh:
                order = [tuple(line.split()) for line in fh]
            if order != [('A', '10'), ('A', '20'), ('B', '10'), ('B', '20'),
                         ('B', '20'), ('B', '10'), ('A', '20'), ('A', '10')]:
                bad.append(f'not rotated and swapped: {order}')
            q = os.path.join(td, 'Q')
            got = estimate(measure([q], 'g/x', 10, 3, None, td)[0], 10)
            if got != {'instructions': (7.0, 7.0, 57.0),
                       'cycles': (3.0, 3.0, 53.0)}:
                bad.append(f'a setup some runs add to: {got}')
            if main([os.path.join(td, 'W'), 'g/x', '10']) != 1:
                bad.append('a spread of the differences did not exit 1')
            if main([a, b, 'g/x', '10']) != 0:
                bad.append('a clean reading did not exit 0')
            if command('x', 'g/x', 5, 'o', '3')[:4] != ['taskset', '-c', '3',
                                                       fake]:
                bad.append('--cpu did not pin the run')
            if command('x', 'g/x', 5, 'o', None)[0] != fake:
                bad.append('a run without --cpu was pinned')
            for tag, what in (('U', 'a count not counted'),
                              ('M', 'a count missing'),
                              ('F', 'a failing run')):
                if main([os.path.join(td, tag), 'g/x', '10']) != 2:
                    bad.append(f'{what} did not exit 2')
            if main(['g/x', '10']) != 2:
                bad.append('no build did not exit 2')
        finally:
            PERF = saved
    for b in bad:
        print('FAIL', b)
    print('self-test', 'FAILED' if bad else 'passed')
    return 1 if bad else 0


def main(argv):
    if argv == ['--self-test']:
        return self_test()
    cpu, reps = None, 3
    while argv[:1] in (['--cpu'], ['--reps']):
        if len(argv) < 2 or (argv[0] == '--reps' and not argv[1].isdigit()):
            print(f'{argv[0]} needs a value', file=sys.stderr)
            return 2
        if argv[0] == '--cpu':
            cpu = argv[1]
        else:
            reps = int(argv[1])
        argv = argv[2:]
    if (len(argv) < 3 or not argv[-1].isdigit() or int(argv[-1]) < 1
            or reps < 1):
        print(__doc__.split('\n\n')[1], file=sys.stderr)
        return 2
    bins, name, n = argv[:-2], argv[-2], int(argv[-1])
    for tool in [PERF[0]] + (['taskset'] if cpu is not None else []):
        if shutil.which(tool) is None:
            print(f'{tool} is not on PATH; nothing measured', file=sys.stderr)
            return 2
    with tempfile.TemporaryDirectory() as td:
        try:
            got = measure(bins, name, n, reps, cpu, td)
        except (ValueError, OSError) as e:
            print(e, file=sys.stderr)
            return 2
    print(f"{name}, per call [lowest..highest of {reps} repetitions'"
          " differences]:")
    est = [estimate(g, n) for g in got]
    wide = []
    for j, (b, g) in enumerate(zip(bins, est)):
        label = chr(ord('A') + j)
        cells = []
        for e in EVENTS:
            mid, lo, hi = g[e]
            base = est[0][e][0]
            cells.append(f'{e} {mid:.1f} [{lo:.1f}..{hi:.1f}]'
                         + (f' {label}/A {mid / base:.4f}'
                            if j and base else ''))
        print(f'{label} {"  ".join(cells)}  {b}')
        mid, lo, hi = g['instructions']
        if hi - lo > SPAN * abs(mid):
            wide.append(label)
    if wide:
        print(f'{", ".join(wide)}: instruction differences spread over more'
              f' than {SPAN:.0%} of the figure, so an amount the RTS clock'
              ' adds to some runs may be in it; GHCRTS=-V0 stops the clock')
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
