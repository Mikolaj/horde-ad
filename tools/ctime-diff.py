#!/usr/bin/env python3
"""Compare two builds' compile time per module, against the noise of the run.

Usage: python3 tools/ctime-diff.py DIR_A DIR_B [--min-ms MS]
       python3 tools/ctime-diff.py --self-test

DIR_A and DIR_B are two build directories, or two trees written with
`-dumpdir`, built alone one after the other with `--ghc-options="-ddump-timings
-ddump-simpl -ddump-to-file -dsuppress-uniques"` and `-dsuppress-all` or
`-dsuppress-idinfo` (tools/core-diff.py says how to keep two builds apart).
For each module it sums the `time=` and `alloc=` of every pass GHC reports,
the `.dyn` dump of `-dynamic-too`'s second code generation included, and
prints both builds' milliseconds and gigabytes, the time ratio B/A and the
module's Core verdict from tools/core-diff.py: `same`, `literals` or
`differs`. Then the pooled ratios --- summed B over summed A --- of the
controls, the modules whose Core is the same in both builds, of the modules
whose Core differs, and of all; and the controls' per-module time ratios,
over those taking at least MS milliseconds in A (default 1000).

A control compiles the same Core twice, so its time ratio is the noise of
the run: a total ratio inside the controls' range is no measured change.
GHC's allocation is close to deterministic, so its ratio is the steadier
measure of compile cost where the Core moved, and a control's should be 1.
On one pair of builds of orthotope's test suite whose Core shrank by 2.3%,
the total time ratio, 1.005, sat inside the controls' 1.004 to 1.114, while
GHC's allocation fell by 2.2% and the controls' did not move.

Exit 0 when the comparison was printed, 2 when it could not be: a tree with
no `.dump-timings` file or no `.dump-simpl` dump to take the verdicts from,
or two trees with no module in common.
"""

import collections
import importlib.util
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import dumps  # noqa: E402

_spec = importlib.util.spec_from_file_location(
    'core_diff', os.path.join(HERE, 'core-diff.py'))
core_diff = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(core_diff)

PASS = re.compile(r'^.*? \[.*?\]: alloc=(\d+) time=([\d.]+)\s*$')


def timings(root):
    """Module key -> [milliseconds, bytes allocated], each module's `.dyn`
    dump summed into its own."""
    out = collections.defaultdict(lambda: [0.0, 0])
    for p, key in dumps.walk(root, '.dump-timings'):
        if key.endswith('.dyn'):
            key = key[:-len('.dyn')]
        for line in dumps.read_text(p).split('\n'):
            m = PASS.match(line)
            if m:
                out[key][0] += float(m.group(2))
                out[key][1] += int(m.group(1))
    return dict(out)


def ratio(b, a):
    return f'{b / a:6.3f}' if a else '     -'


def report(ta, tb, vs, min_ms):
    keys = sorted(set(ta) & set(tb), key=lambda k: (-ta[k][0], k))
    lines = [f'{"module":56s} {"ms A":>9s} {"ms B":>9s}  B/A  '
             f'{"GB A":>7s} {"GB B":>7s}  verdict']
    pools = collections.defaultdict(lambda: [0.0, 0.0, 0, 0])
    spread = []
    for k in keys:
        (ma, aa), (mb, ab) = ta[k], tb[k]
        v = vs.get(k, 'no Core')
        lines.append(f'{k:56s} {ma:9.0f} {mb:9.0f} {ratio(mb, ma)} '
                     f'{aa / 1e9:7.2f} {ab / 1e9:7.2f}  {v}')
        group = ('controls' if v in ('same', 'literals')
                 else 'changed' if v == 'differs' else None)
        for g in ((group,) if group else ()) + ('all',):
            p = pools[g]
            pools[g] = [p[0] + ma, p[1] + mb, p[2] + aa, p[3] + ab]
        if group == 'controls' and ma >= min_ms:
            spread.append(mb / ma)
    for k in sorted(set(ta) ^ set(tb)):
        lines.append(f'{k:56s} in {"A" if k in ta else "B"} only')
    for g in ('controls', 'changed', 'all'):
        n = sum(1 for k in keys if g == 'all' or
                (g == 'controls') == (vs.get(k) in ('same', 'literals'))
                and vs.get(k) in ('same', 'literals', 'differs'))
        ma, mb, aa, ab = pools[g]
        lines.append(f'{g:8s} {n:4d} modules: time {ma:9.0f} -> {mb:9.0f} ms, '
                     f'ratio {ratio(mb, ma)}; allocation ratio {ratio(ab, aa)}')
    if spread:
        lo, hi = min(spread), max(spread)
        tot = pools['all'][1] / pools['all'][0] if pools['all'][0] else 0
        where = 'inside' if lo <= tot <= hi else 'outside'
        lines.append(f'controls of at least {min_ms:g} ms: time ratios '
                     f'{lo:.3f} to {hi:.3f}; the total, {tot:.3f}, is {where} '
                     'that range')
    else:
        lines.append(f'no control takes {min_ms:g} ms in A: the noise of the '
                     'run is not measured')
    return lines


def self_test():
    """Two trees: a module whose Core changed and two controls, one
    identical and one moved by a literal, each with timings, one with a
    `.dyn` dump, and the session's own non-module timings."""
    import tempfile
    def core(terms, lit):
        return ('\nResult size of Tidy Core\n'
                f'  = {{terms: {terms}, types: 1}}\n\nf\n  = I# {lit}\n')
    def tim(mod, ms, alloc):
        return ''.join(f'{p} [{mod}]: alloc={alloc} time={ms / 2}\n'
                       for p in ('Simplifier', 'CodeGen'))
    bad = []
    with tempfile.TemporaryDirectory() as td:
        tree = {
            'A/build/M/Big.dump-simpl': core(100, '1#'),
            'A/build/M/Big.dump-timings': tim('M.Big', 4000, 10**9),
            'A/build/M/Same.dump-simpl': core(10, '1#'),
            'A/build/M/Same.dump-timings': tim('M.Same', 2000, 10**8),
            'A/build/M/Same.dyn.dump-timings': tim('M.Same', 200, 10**7),
            'A/build/M/Lit.dump-simpl': core(10, '5#'),
            'A/build/M/Lit.dump-timings': tim('M.Lit', 1000, 10**8),
            'A/build/M/Tiny.dump-simpl': core(1, '1#'),
            'A/build/M/Tiny.dump-timings': tim('M.Tiny', 10, 10**6),
            'A/build/non-module.dump-timings': tim('/x/y.hi', 50, 10**6),
            'B/build/M/Big.dump-simpl': core(80, '1#'),
            'B/build/M/Big.dump-timings': tim('M.Big', 3000, 8 * 10**8),
            'B/build/M/Same.dump-simpl': core(10, '1#'),
            'B/build/M/Same.dump-timings': tim('M.Same', 1900, 10**8),
            'B/build/M/Same.dyn.dump-timings': tim('M.Same', 200, 10**7),
            'B/build/M/Lit.dump-simpl': core(10, '6#'),
            'B/build/M/Lit.dump-timings': tim('M.Lit', 1050, 10**8),
            'B/build/M/Tiny.dump-simpl': core(1, '1#'),
            'B/build/M/Tiny.dump-timings': tim('M.Tiny', 20, 10**6),
            'B/build/non-module.dump-timings': tim('/x/y.hi', 50, 10**6),
        }
        for rel, text in tree.items():
            p = os.path.join(td, rel)
            os.makedirs(os.path.dirname(p), exist_ok=True)
            with open(p, 'w') as fh:
                fh.write(text)
        A, B = os.path.join(td, 'A'), os.path.join(td, 'B')
        ta, tb = timings(A), timings(B)
        if ta.get('M/Same') != [2200.0, 22 * 10**7]:
            bad.append(f'M/Same with its .dyn dump: {ta.get("M/Same")}')
        vs = core_diff.verdicts(core_diff.scan(A), core_diff.scan(B))
        got = report(ta, tb, vs, 1000)
        # M/Tiny is a control below the 1000 ms bar: pooled, not in the range.
        want_tail = [
            f'{"controls":8s} {3:4d} modules: time {3210:9.0f} -> '
            f'{3170:9.0f} ms, ratio {3170 / 3210:6.3f}; allocation ratio '
            f'{1:6.3f}',
            f'{"changed":8s} {1:4d} modules: time {4000:9.0f} -> '
            f'{3000:9.0f} ms, ratio {0.75:6.3f}; allocation ratio {0.8:6.3f}',
            # A 2.424 GB: Big 2, Same 0.22, Lit 0.2, Tiny and non-module
            # 0.002 each; B 2.024 GB, Big 1.6.
            f'{"all":8s} {5:4d} modules: time {7260:9.0f} -> {6220:9.0f} ms, '
            f'ratio {6220 / 7260:6.3f}; allocation ratio {2.024 / 2.424:6.3f}',
            f'controls of at least 1000 ms: time ratios {2100 / 2200:.3f} to '
            f'{1.05:.3f}; the total, {6220 / 7260:.3f}, is outside that range']
        if got[-4:] != want_tail:
            bad.append('summary:\n  ' + '\n  '.join(got[-4:]))
        rows = {l.split()[0]: l.split()[-1] for l in got[1:6]}
        want = {'M/Big': 'differs', 'M/Same': 'same', 'M/Lit': 'literals',
                'non-module': 'Core', 'M/Tiny': 'same'}
        if rows != want:
            bad.append(f'rows and their verdicts: {rows}')
        empty = os.path.join(td, 'empty')
        os.makedirs(empty)
        nocore = os.path.join(td, 'nocore')
        # Timings of a module A has too, so that only the missing Core refuses.
        os.makedirs(os.path.join(nocore, 'build', 'M'))
        p = os.path.join(nocore, 'build', 'M', 'Big.dump-timings')
        with open(p, 'w') as fh:
            fh.write(tim('M.Big', 10, 10))
        for argv, why in (([A, empty], 'a tree without timings'),
                          ([A, nocore], 'a tree without Core dumps')):
            if main(argv) != 2:
                bad.append(f'{why} did not exit 2')
    for b_ in bad:
        print('FAIL', b_)
    print('self-test', 'FAILED' if bad else 'passed')
    return 1 if bad else 0


def main(argv):
    if argv == ['--self-test']:
        return self_test()
    min_ms = 1000.0
    if len(argv) == 4 and argv[2] == '--min-ms':
        try:
            min_ms = float(argv[3])
        except ValueError:
            print(f'--min-ms {argv[3]} is not a number', file=sys.stderr)
            return 2
        argv = argv[:2]
    if len(argv) != 2:
        print(__doc__.split('\n\n')[1], file=sys.stderr)
        return 2
    ts, cores = [], []
    for d in argv:
        t = timings(d)
        if not t:
            print(f'no .dump-timings file under {d}; was it built with '
                  '-ddump-timings -ddump-to-file?', file=sys.stderr)
            return 2
        try:
            c = core_diff.scan(d)
        except ValueError as e:
            print(e, file=sys.stderr)
            return 2
        if not c:
            print(f'no .dump-simpl file under {d} to take the Core verdicts '
                  'from; was it built with -ddump-simpl?', file=sys.stderr)
            return 2
        ts.append(t)
        cores.append(c)
    if not set(ts[0]) & set(ts[1]):
        print('the two trees have no module in common', file=sys.stderr)
        return 2
    print('\n'.join(report(*ts, core_diff.verdicts(*cores), min_ms)))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
