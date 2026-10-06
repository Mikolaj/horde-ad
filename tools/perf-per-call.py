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
`taskset -c`. Prints, per BIN, the medians over the repetitions with their
range and, for each BIN after the first, its medians over A's.

Instructions repeat closely, so their median is what decides; cycles
carry the machine's noise, which the range shows. This is the native
counterpart of tools/cachegrind-per-call.py, which estimates cycles from
a cache model where `perf stat` cannot run, at fifty times the run time or
more.

Exit 0 when the figures were printed, 2 when they could not be: perf, or
taskset with `--cpu`, missing, a run failing, or its output without
a counted instructions:u and cycles:u.
"""

import os
import shutil
import statistics
import subprocess
import sys
import tempfile

EVENTS = ('instructions', 'cycles')

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


def spread(xs):
    """(median, lowest, highest)."""
    return statistics.median(xs), min(xs), max(xs)


def run(binary, name, iters, cpu, out):
    cmd = command(binary, name, iters, out, cpu)
    r = subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
                       text=True)
    if r.returncode != 0:
        raise ValueError(f'{" ".join(cmd)} exited {r.returncode}:\n'
                         + r.stderr[-2000:])
    return counts(out)


def measure(bins, name, n, reps, cpu, td):
    """Per BIN, event -> the per-call counts of the repetitions."""
    got = [{e: [] for e in EVENTS} for _ in bins]
    out = os.path.join(td, 'perf.txt')
    for r in range(reps):
        for i in range(len(bins)):
            j = (i + r) % len(bins)
            c = {}
            for k in ((1, 2) if r % 2 == 0 else (2, 1)):
                c[k] = run(bins[j], name, k * n, cpu, out)
            for e, v in per_call(c[1], c[2], n).items():
                got[j][e].append(v)
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
ins, cyc = {{'A': (7, 3), 'B': (9, 4), 'U': (7, 3), 'M': (7, 3)}}[tag]
with open(out, 'w') as fh:
    fh.write('# started on Mon Oct  6 12:00:00 2026' + chr(10) + chr(10))
    fh.write(str(1000 + ins * iters) + ',,instructions:u,100,100.00,,' + chr(10))
    if tag != 'M':
        fh.write(('<not counted>' if tag == 'U' else str(500 + cyc * iters))
                 + ',,cycles:u,100,100.00,,' + chr(10))
'''


def self_test():
    """The parsing, the differencing and the order of the runs, with a fake
    perf whose counts are a setup plus a fixed cost per call."""
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
            got = measure([a, b], 'g/x', 10, 2, None, td)
            if got != [{'instructions': [7.0, 7.0], 'cycles': [3.0, 3.0]},
                       {'instructions': [9.0, 9.0], 'cycles': [4.0, 4.0]}]:
                bad.append(f'per call: {got}')
            with open(calls) as fh:
                order = [tuple(line.split()) for line in fh]
            if order != [('A', '10'), ('A', '20'), ('B', '10'), ('B', '20'),
                         ('B', '20'), ('B', '10'), ('A', '20'), ('A', '10')]:
                bad.append(f'not rotated and swapped: {order}')
            if spread([3, 1, 9]) != (3, 1, 9):
                bad.append(f'spread of 3, 1, 9: {spread([3, 1, 9])}')
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
    print(f'{name}, per call, median [lowest..highest] of {reps}:')
    base = {e: spread(got[0][e])[0] for e in EVENTS}
    for j, (b, g) in enumerate(zip(bins, got)):
        label = chr(ord('A') + j)
        cells = []
        for e in EVENTS:
            med, lo, hi = spread(g[e])
            cells.append(f'{e} {med:.1f} [{lo:.1f}..{hi:.1f}]'
                         + (f' {label}/A {med / base[e]:.4f}'
                            if j and base[e] else ''))
        print(f'{label} {"  ".join(cells)}  {b}')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
