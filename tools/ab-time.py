#!/usr/bin/env python3
"""Interleaved A/B wall-time pairs of criterion benchmarks across two builds.

Usage: python3 tools/ab-time.py [--log TSV] BIN_A BIN_B PAIRS NAME [NAME ...]
       python3 tools/ab-time.py --self-test

BIN_A and BIN_B are the same benchmark executable from two builds. For each
NAME in turn, runs A then B, PAIRS times, one benchmark per process
(`-m glob NAME`, criterion's default time limit, `--json` with `+RTS -T`),
reads criterion's OLS slope of seconds per iteration from each run, and
prints the median of the PAIRS ratios B/A with their range. `--log` also
writes every pair, one line each. Run it from the directory the benchmark
expects as its working directory: the MNIST suites read `samplesData/`.

This is bench/CLAUDE.md's A/B procedure as a script: pairs interleaved, so
drift over the run cancels within each pair; one benchmark per process, so
no predecessor's RTS pool state reaches the measured one
(docs/position-effect.md); the median, because single pairs on a loaded or
virtual machine scatter widely --- 0.42 to 1.36 around a true 1.00 on the
VM docs/overloaded-unfoldings.md was measured on. It gives time only;
compare allocation first, which is exact, and back any ratio that decides
something with cycles or instructions (tools/cachegrind-per-call.py).

Exit 0 when every pair ran, 2 when one did not: a run failing, or its JSON
without one report carrying a time regression.
"""

import json
import os
import statistics
import subprocess
import sys
import tempfile


def slope(binary, name):
    """Seconds per iteration of one benchmark, from a fresh process."""
    fd, path = tempfile.mkstemp(suffix='.json')
    os.close(fd)
    try:
        r = subprocess.run([binary, '-m', 'glob', name, '--json', path,
                            '+RTS', '-T'], stdout=subprocess.DEVNULL,
                           stderr=subprocess.PIPE, text=True)
        if r.returncode != 0:
            raise ValueError(f'{binary} on {name} exited {r.returncode}: '
                             + r.stderr[-500:])
        with open(path) as fh:
            reports = json.load(fh)[2]
    finally:
        os.unlink(path)
    if len(reports) != 1:
        raise ValueError(f'{name} matched {len(reports)} benchmarks, not 1')
    regs = {g['regResponder']: g
            for g in reports[0]['reportAnalysis']['anRegress']}
    if 'time' not in regs:
        raise ValueError(f'{name}: no time regression in the report')
    return regs['time']['regCoeffs']['iters']['estPoint']


def pairs(a, b, n, name, log):
    ratios = []
    for i in range(n):
        ta, tb = slope(a, name), slope(b, name)
        ratios.append(tb / ta)
        if log:
            log.write(f'{name}\t{i}\t{ta:.6e}\t{tb:.6e}\t{tb / ta:.4f}\n')
            log.flush()
    return statistics.median(ratios), min(ratios), max(ratios)


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
    reps = [{{'reportName': name, 'reportAnalysis': {{'anRegress': [
        {{'regResponder': 'time', 'regCoeffs': {{'iters': {{'estPoint': t}}}}}}]}}}}]
json.dump(['criterion', '1.6', reps], open(out, 'w'))
'''


def self_test():
    """Two fake benchmark binaries that log their calls and report times."""
    bad = []
    with tempfile.TemporaryDirectory() as td:
        calls = os.path.join(td, 'calls')
        bins = []
        # A always 1.0; B's time is indexed by the global call number modulo
        # 6, and B makes calls 2, 4 and 6, so its three ratios are 1.5, 1.2
        # and 0.8 in that order only if the runs interleave A, B, A, B ---
        # a median of 1.2 that neither the first ratio nor the mean equals.
        for tag, secs in (('A', [1.0]), ('B', [0.8, 0, 1.5, 0, 1.2, 0])):
            p = os.path.join(td, tag)
            with open(p, 'w') as fh:
                fh.write(FAKE.format(secs=secs, calls=calls, tag=tag))
            os.chmod(p, 0o755)
            bins.append(p)
        got = pairs(bins[0], bins[1], 3, 'g/x', None)
        if got != (1.2, 0.8, 1.5):
            bad.append(f'median and range: {got}')
        with open(calls) as fh:
            order = [line.split()[0] for line in fh]
        if order != ['A', 'B'] * 3:
            bad.append(f'not interleaved: {order}')
        if main([bins[0], bins[1], '1', 'none']) != 2:
            bad.append('a name matching no benchmark did not exit 2')
    for b in bad:
        print('FAIL', b)
    print('self-test', 'FAILED' if bad else 'passed')
    return 1 if bad else 0


def main(argv):
    if argv == ['--self-test']:
        return self_test()
    log_path = None
    if argv[:1] == ['--log']:
        if len(argv) < 2:
            print('--log needs a path', file=sys.stderr)
            return 2
        log_path, argv = argv[1], argv[2:]
    if len(argv) < 4 or not argv[2].isdigit() or int(argv[2]) < 1:
        print(__doc__.split('\n\n')[1], file=sys.stderr)
        return 2
    a, b, n, names = argv[0], argv[1], int(argv[2]), argv[3:]
    log = open(log_path, 'w') if log_path else None
    try:
        for name in names:
            med, lo, hi = pairs(a, b, n, name, log)
            print(f'{name:60s} median B/A {med:.4f}  range {lo:.3f}..{hi:.3f}',
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
