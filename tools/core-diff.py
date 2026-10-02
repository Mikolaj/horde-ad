#!/usr/bin/env python3
"""Compare the optimised Core of two builds, module by module.

Usage: python3 tools/core-diff.py DIR_A DIR_B
       python3 tools/core-diff.py DIR_A DIR_B --module SUBSTRING
       python3 tools/core-diff.py --self-test

DIR_A and DIR_B are two build directories whose modules were compiled with
`--ghc-options="-ddump-simpl -ddump-to-file -dsuppress-all
-dsuppress-uniques"`, the dumps landing beside the objects; a separate
`--builddir` for each keeps the two apart. The first form prints, for every
module whose Core differs, the number of top-level bindings and the size in
terms of its Tidy Core, both builds, largest growth first, and the totals.
The second form lists, for the modules whose path contains SUBSTRING, the
binding names whose count differs --- the specialisations and workers one
build has and the other has not.

This is what shows where a flag or pragma puts its compile-time cost. Taking
`-fno-expose-overloaded-unfoldings` off `AstSimplify` left its own Core as it
was and grew its importers' 2.3-fold, `AstVectorize`'s 37-fold, which timing
the module itself cannot show (docs/overloaded-unfoldings.md).

Binding names are normalised as `-dsuppress-uniques` leaves them: the numeric
suffix GHC gives each specialisation or worker is dropped, so `$sf3` and
`$sf7` count as two of `$sf`, and a renumbering between builds is not a
difference. The size is the "Result size of Tidy Core" of each dump, which
`-dsuppress-all` keeps where it drops the per-binding size comments.

Exit 0 when the comparison was printed, 2 when it could not be: a directory
with no `.dump-simpl` file, or a dump without its result size, so that a
build made without the dump flags does not read as one with no differences;
and a SUBSTRING no module's path contains, which would read as a module
whose bindings did not move.
"""

import collections
import os
import re
import sys

SIZE = re.compile(r'Result size of Tidy Core\s*=\s*\{terms: ([\d,]+)')
SKIP = ('Rec {', 'end Rec', 'Result size')


def scan(root):
    """Module key -> (Counter of binding names, terms); key is the path below
    the last `/build/`. Raises ValueError on a dump without its size."""
    out = {}
    for dp, _, fs in os.walk(root):
        for f in fs:
            if not f.endswith('.dump-simpl'):
                continue
            p = os.path.join(dp, f)
            key = p.rsplit('/build/', 1)[-1][:-len('.dump-simpl')]
            with open(p, errors='replace') as fh:
                txt = fh.read()
            m = SIZE.search(txt)
            if not m:
                raise ValueError(f'{p} has no "Result size of Tidy Core" line')
            names = collections.Counter()
            for line in txt.split('\n'):
                if not line or line[0] in ' \t=-{' or line.startswith(SKIP):
                    continue
                tok = line.split(' ')[0]
                if re.match(r'[A-Za-z_$]', tok):
                    names[re.sub(r"([A-Za-z_$'])[0-9]+\b", r'\1', tok)] += 1
            out[key] = (names, int(m.group(1).replace(',', '')))
    return out


def summary(a, b):
    lines, tot = [], [0, 0, 0, 0]
    keys = sorted(set(a) | set(b), key=lambda k: (
        -(b.get(k, ({}, 0))[1] - a.get(k, ({}, 0))[1]), k))
    for k in keys:
        na, ta = a.get(k, (collections.Counter(), 0))
        nb, tb = b.get(k, (collections.Counter(), 0))
        ca, cb = sum(na.values()), sum(nb.values())
        tot = [tot[0] + ca, tot[1] + cb, tot[2] + ta, tot[3] + tb]
        if (ca, ta) != (cb, tb):
            ratio = f'{tb / ta:6.2f}' if ta else '   new'
            lines.append(f'{k:60s} bindings {ca:6d} -> {cb:6d}  '
                         f'terms {ta:9d} -> {tb:9d} {ratio}')
    ratio = f'{tot[3] / tot[2]:6.2f}' if tot[2] else '     -'
    lines.append(f'{"TOTAL":60s} bindings {tot[0]:6d} -> {tot[1]:6d}  '
                 f'terms {tot[2]:9d} -> {tot[3]:9d} {ratio}')
    return lines


def names_diff(a, b, sub):
    lines = []
    for k in sorted(set(a) | set(b)):
        if sub not in k:
            continue
        na = a.get(k, (collections.Counter(), 0))[0]
        nb = b.get(k, (collections.Counter(), 0))[0]
        rows = [(nb[n] - na[n], n) for n in set(na) | set(nb) if na[n] != nb[n]]
        lines.append(f'== {k}')
        for d, n in sorted(rows, key=lambda r: (-abs(r[0]), r[1])):
            lines.append(f'  {na[n]:5d} -> {nb[n]:5d}  {n}')
    return lines


def self_test():
    """Two synthetic dump trees: one module grows, one is unchanged."""
    import tempfile
    def dump(terms, binds):
        return ('\n==================== Tidy Core ====================\n'
                f'Result size of Tidy Core\n  = {{terms: {terms}, types: 1}}\n\n'
                + ''.join(f'{b}\n  = \\ x -> x\n\n' for b in binds)
                + 'Rec {\nloop = loop\nend Rec }\n')
    bad = []
    with tempfile.TemporaryDirectory() as td:
        tree = {
            'A/build/src/M/User.dump-simpl': dump('1,000', ['f', '$wf']),
            'A/build/src/M/Same.dump-simpl': dump('10', ['g']),
            'B/build/src/M/User.dump-simpl':
                dump('2,500', ['f', '$wf', '$sf1', '$sf2', '$w$sf3']),
            'B/build/src/M/Same.dump-simpl': dump('10', ['g']),
            'C/build/src/M/User.dump-simpl': 'no size line\n',
        }
        for rel, text in tree.items():
            os.makedirs(os.path.dirname(os.path.join(td, rel)), exist_ok=True)
            with open(os.path.join(td, rel), 'w') as fh:
                fh.write(text)
        a, b = scan(os.path.join(td, 'A')), scan(os.path.join(td, 'B'))
        got = summary(a, b)
        want = [f'{"src/M/User":60s} bindings {3:6d} -> {6:6d}  '
                f'terms {1000:9d} -> {2500:9d} {2.5:6.2f}',
                f'{"TOTAL":60s} bindings {5:6d} -> {8:6d}  '
                f'terms {1010:9d} -> {2510:9d} {2510 / 1010:6.2f}']
        if got != want:
            bad.append('summary:\n  ' + '\n  '.join(got))
        got = names_diff(a, b, 'User')
        want = ['== src/M/User', f'  {0:5d} -> {2:5d}  $sf',
                f'  {0:5d} -> {1:5d}  $w$sf']
        if got != want:
            bad.append('names:\n  ' + '\n  '.join(got))
        empty = os.path.join(td, 'empty')
        os.makedirs(empty)
        if main([os.path.join(td, 'A'), empty]) != 2:
            bad.append('a directory without dumps did not exit 2')
        if main([os.path.join(td, 'A'), os.path.join(td, 'C')]) != 2:
            bad.append('a dump without its result size did not exit 2')
        if main([os.path.join(td, 'A'), os.path.join(td, 'B'),
                 '--module', 'NoSuch']) != 2:
            bad.append('a --module matching no module did not exit 2')
    for b_ in bad:
        print('FAIL', b_)
    print('self-test', 'FAILED' if bad else 'passed')
    return 1 if bad else 0


def main(argv):
    if argv == ['--self-test']:
        return self_test()
    sub = None
    if len(argv) == 4 and argv[2] == '--module':
        sub, argv = argv[3], argv[:2]
    if len(argv) != 2:
        print(__doc__.split('\n\n')[1], file=sys.stderr)
        return 2
    trees = []
    for d in argv:
        try:
            t = scan(d)
        except ValueError as e:
            print(e, file=sys.stderr)
            return 2
        if not t:
            print(f'no .dump-simpl file under {d}; was it built with '
                  '-ddump-simpl -ddump-to-file?', file=sys.stderr)
            return 2
        trees.append(t)
    if sub is not None and not any(sub in k for t in trees for k in t):
        print(f"no module's path contains {sub}", file=sys.stderr)
        return 2
    lines = (names_diff(*trees, sub) if sub is not None
             else summary(*trees))
    print('\n'.join(lines))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
