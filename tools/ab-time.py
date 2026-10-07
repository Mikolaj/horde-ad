#!/usr/bin/env python3
"""Interleaved wall time and allocation of criterion benchmarks across builds.

Usage: python3 tools/ab-time.py [--log TSV] [--cpu CPU]
                                BIN BIN [BIN ...] ROUNDS NAME [NAME ...]
       python3 tools/ab-time.py --self-test

Each BIN is the same benchmark executable from another build, labelled A,
B, C, ... in the order given. For each NAME in turn, runs every BIN once
a round, ROUNDS rounds, the order rotated by one from round to round, so
that each build goes first as often as the next where ROUNDS is a multiple
of their number --- two builds alternate. One benchmark per process
(`-m glob NAME`, criterion's default time limit, `--regress allocated:iters`,
`--json` with `+RTS -T`), each pinned to CPU by `taskset -c` with `--cpu`.
Reads criterion's OLS slopes of seconds and of bytes allocated per iteration
from each run, and prints, for each BIN after the first, the median of its
ROUNDS time ratios to A's, each ratio within one round, with their range,
and the median bytes allocated per iteration of the two. `--log` also writes
every run, one line each. Run it from the directory the benchmark expects
as its working directory: the MNIST suites read `samplesData/`.

This is docs/perf-checklist.md's A/B procedure as a script: interleaved, so
drift over the run cancels within each round, and the order rotated, so
no build always runs first; one benchmark per process, so
no predecessor's RTS pool state reaches the measured one
(docs/position-effect.md); the median, because single pairs on a loaded or
virtual machine scatter widely --- 0.42 to 1.36 around a true 1.00 on the
VM docs/overloaded-unfoldings.md was measured on. Compare allocation first,
which is exact, and back any time ratio that decides something with
instructions or cycles (tools/perf-per-call.py, or
tools/cachegrind-per-call.py where perf cannot run).

Exit 0 when every run happened, 2 when one did not: a run failing, taskset
missing with `--cpu`, or its JSON without one report carrying a time and
an allocation regression.
"""

import os
import shutil
import statistics
import subprocess
import sys
import tempfile

# Beside this file, which a path import (a defect case's unit) leaves off
# sys.path.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common  # noqa: E402


def command(binary, name, path, cpu):
    """The run of one benchmark, pinned to cpu unless it is None."""
    return ((['taskset', '-c', cpu] if cpu is not None else [])
            + [binary, '-m', 'glob', name, '--regress', 'allocated:iters',
               '--json', path, '+RTS', '-T'])


def slopes(binary, name, cpu):
    """Seconds and bytes allocated per iteration of one benchmark, from
    a fresh process."""
    fd, path = tempfile.mkstemp(suffix='.json')
    os.close(fd)
    try:
        r = subprocess.run(command(binary, name, path, cpu),
                           stdout=subprocess.DEVNULL,
                           stderr=subprocess.PIPE, text=True)
        if r.returncode != 0:
            raise ValueError(f'{binary} on {name} exited {r.returncode}: '
                             + r.stderr[-500:])
        reports = common.criterion_reports(path)
    finally:
        os.unlink(path)
    if len(reports) != 1:
        raise ValueError(f'{name} matched {len(reports)} benchmarks, not 1')
    _, regs, _ = reports[0]
    if 'time' not in regs:
        raise ValueError(f'{name}: no time regression in the report')
    # A CriterionError is a ValueError, so main's exit 2 covers it.
    t = common.slope(path, name, regs['time'])
    if 'allocated' not in regs:
        raise ValueError(f'{name}: no allocated regression in the report')
    return t, common.slope(path, name, regs['allocated'])


def rounds(bins, n, name, cpu, log):
    """Per BIN after the first: (median time ratio to the first, lowest,
    highest, median allocation of the first, median allocation)."""
    times = [[None] * n for _ in bins]
    allocs = [[None] * n for _ in bins]
    for r in range(n):
        for i in range(len(bins)):
            j = (i + r) % len(bins)
            t, a = slopes(bins[j], name, cpu)
            times[j][r], allocs[j][r] = t, a
            if log:
                log.write(f'{name}\t{r}\t{chr(ord("A") + j)}\t{t:.6e}'
                          f'\t{a:.6e}\n')
                log.flush()
    out = []
    for j in range(1, len(bins)):
        ratios = [tb / ta for ta, tb in zip(times[0], times[j])]
        out.append((statistics.median(ratios), min(ratios), max(ratios),
                    statistics.median(allocs[0]),
                    statistics.median(allocs[j])))
    return out


FAKE = '''#!/usr/bin/env python3
import json, sys
secs = {secs!r}
a = sys.argv
name, out = a[a.index('-m') + 2], a[a.index('--json') + 1]
with open({calls!r}, 'a') as fh:
    fh.write({tag!r} + ' ' + name + chr(10))
n = sum(1 for _ in open({calls!r}))
if name == 'none':
    reps = []
else:
    t = secs[n % len(secs)]
    regs = [{{'regResponder': 'time', 'regCoeffs': {{'iters': {{'estPoint': t}}}}}}]
    if a[a.index('--regress') + 1:a.index('--regress') + 2] == ['allocated:iters']:
        regs.append({{'regResponder': 'allocated',
                     'regCoeffs': {{'iters': {{'estPoint': {alloc!r}}}}}}})
    reps = [{{'reportName': name, 'reportAnalysis': {{'anRegress': regs}}}}]
json.dump(['criterion', '1.6', reps], open(out, 'w'))
'''


def self_test():
    """Fake benchmark binaries that log their calls and report times."""
    bad = []
    with tempfile.TemporaryDirectory() as td:
        calls = os.path.join(td, 'calls')

        def fake(tag, secs, alloc):
            p = os.path.join(td, tag)
            with open(p, 'w') as fh:
                fh.write(FAKE.format(secs=secs, calls=calls, tag=tag,
                                     alloc=alloc))
            os.chmod(p, 0o755)
            return p
        # A always 1.0; B's and C's times are indexed by the global call
        # number modulo 10. Rotated, three rounds run A B C, B C A, C A B,
        # so B makes calls 2, 4 and 9, its ratios 1.5, 1.2 and 0.8 --- a
        # median of 1.2 that neither the first ratio nor the mean equals
        # --- and C calls 3, 5 and 7, all 2.0; unrotated, both would read
        # the 9.0s.
        bins = [fake('A', [1.0], 100.0),
                fake('B', [9, 9, 1.5, 9, 1.2, 9, 9, 9, 9, 0.8], 50.0),
                fake('C', [9, 9, 9, 2.0, 9, 2.0, 9, 2.0, 9, 9], 100.0)]
        got = rounds(bins, 3, 'g/x', None, None)
        if got != [(1.2, 0.8, 1.5, 100.0, 50.0),
                   (2.0, 2.0, 2.0, 100.0, 100.0)]:
            bad.append(f'medians and ranges: {got}')
        with open(calls) as fh:
            order = [line.split()[0] for line in fh]
        if order != ['A', 'B', 'C', 'B', 'C', 'A', 'C', 'A', 'B']:
            bad.append(f'not rotated: {order}')
        if command('x', 'g/x', 'j', '3')[:4] != ['taskset', '-c', '3', 'x']:
            bad.append('--cpu did not pin the run')
        if command('x', 'g/x', 'j', None)[0] != 'x':
            bad.append('a run without --cpu was pinned')
        if main([bins[0], bins[1], '1', 'none']) != 2:
            bad.append('a name matching no benchmark did not exit 2')
        if main([bins[0], '1', 'g/x']) != 2:
            bad.append('a single build did not exit 2')
        nul = fake('N', [None], 100.0)
        if main([bins[0], nul, '1', 'g/x']) != 2:
            bad.append('a null slope did not exit 2')
    for b in bad:
        print('FAIL', b)
    print('self-test', 'FAILED' if bad else 'passed')
    return 1 if bad else 0


def main(argv):
    if argv == ['--self-test']:
        return self_test()
    log_path = cpu = None
    while argv[:1] in (['--log'], ['--cpu']):
        if len(argv) < 2:
            print(f'{argv[0]} needs a value', file=sys.stderr)
            return 2
        if argv[0] == '--log':
            log_path = argv[1]
        else:
            cpu = argv[1]
        argv = argv[2:]
    k = next((i for i, a in enumerate(argv) if a.isdigit()), None)
    if k is None or k < 2 or int(argv[k]) < 1 or k == len(argv) - 1:
        print(__doc__.split('\n\n')[1], file=sys.stderr)
        return 2
    bins, n, names = argv[:k], int(argv[k]), argv[k + 1:]
    if cpu is not None and shutil.which('taskset') is None:
        print('taskset is not on PATH; nothing measured', file=sys.stderr)
        return 2
    for j, b in enumerate(bins):
        print(f'{chr(ord("A") + j)} = {b}')
    log = open(log_path, 'w') if log_path else None
    try:
        for name in names:
            for j, (med, lo, hi, a0, aj) in enumerate(
                    rounds(bins, n, name, cpu, log), start=1):
                print(f'{name:60s} {chr(ord("A") + j)}/A time {med:.4f}'
                      f'  range {lo:.3f}..{hi:.3f}'
                      f'  allocated {aj:.6g} against {a0:.6g} bytes/iter',
                      flush=True)
    except (ValueError, OSError) as e:
        print(e, file=sys.stderr)
        return 2
    finally:
        if log:
            log.close()
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
