#!/usr/bin/env python3
"""Diff the per-closure allocation of two ticky-ticky runs.

Usage: python3 tools/ticky-diff.py [--top N] A.txt B.txt
       python3 tools/ticky-diff.py --self-test

A and B are the files a ticky run writes with `+RTS -rFILE`: one benchmark,
at the same fixed `--iters`, from two builds compiled with
`--ghc-options=-ticky` for the library and the executable both. Prints the
totals and the N closures (default 40) whose allocation moved most, with
their entry counts, largest move first.

The closure names are normalised before matching, because two builds of the
same source name their closures differently: the `{v r1fgjA}` unique goes,
and so does the numeric suffix GHC gives each specialisation or worker
(`$w$w$sastTimesK5` in one build is `$w$w$sastTimesK8` in the other). So
same-named closures of one function are summed, and a move between two of
its specialisations nets out; what remains is a move between functions. A
local closure, `f_sat_s1fhYi{v}`, carries its unique in its own name, and
loses it too.
That is what attributed a whole 31.5 MB difference on `100/grad k L` to
`astTimesK` in one step (docs/overloaded-unfoldings.md).

Exit 0 when the diff was printed, 2 when it could not be: a file missing or
without the per-closure table, which a run of a binary built without
`-ticky` produces, and which must not read as "nothing moved".
"""

import collections
import re
import sys

HEADER = '    Entries'


def read(path):
    """Closure name -> [entries, bytes allocated], names normalised; None
    when the file has no per-closure table."""
    out = collections.defaultdict(lambda: [0, 0])
    seen = False
    with open(path, errors='replace') as fh:
        for line in fh:
            if line.startswith(HEADER):
                seen = True
                continue
            if not seen or line.startswith('---'):
                continue
            m = re.match(r'\s*(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+(.*)$', line)
            if not m:
                continue
            # The kinds word, one letter per non-void argument, is absent
            # when there is none.
            name = m.group(5)
            if int(m.group(4)) > 0:
                name = name.split(None, 1)[-1]
            out[normalise(name)][0] += int(m.group(1))
            out[normalise(name)][1] += int(m.group(2))
    return out if seen else None


def normalise(name):
    # The unique, `{v r1fgjA}` on a top-level closure and a bare `{v}` on
    # a local one, whose own name then carries its unique instead.
    name = re.sub(r'\{v[^}]*\}', '', name).strip()
    name = re.sub(r'_sat_s[0-9A-Za-z]+', '_sat', name)
    name = re.sub(r' in \S+$', '', name)
    return re.sub(r"([A-Za-z_$'])[0-9]+\b", r'\1', name)


def diff(a, b, top):
    ta = sum(v[1] for v in a.values())
    tb = sum(v[1] for v in b.values())
    lines = [f'total alloc {ta} -> {tb}'
             + (f'  ({tb / ta:.4f})' if ta else '')]
    names = sorted(set(a) | set(b),
                   key=lambda k: (-abs(b[k][1] - a[k][1]), k))
    for k in names[:top]:
        lines.append(f'{b[k][1] - a[k][1]:+12d}  alloc {a[k][1]:11d} -> '
                     f'{b[k][1]:11d}  entries {a[k][0]:9d} -> {b[k][0]:9d}'
                     f'  {k}')
    return lines


def self_test():
    """Two synthetic ticky tables of the same program from two builds."""
    import os
    import tempfile
    head = ('ENTERS: 1\n\n'
            '    Entries       Alloc     Alloc\'d  Non-void Arguments'
            '      STG Name\n'
            '--------------------------------------------------------\n')
    a = head + (
        '        10        1000           0   2 MM  '
        'M.$w$w$sf5{v rQPTU} (fun)\n'
        '         5         500           0   1 M   '
        'g_sat_s1a{v} (M) (fun) in r1\n'
        '         1          40           0   1 M   M.h{v r2} (fun)\n'
        '         1          16           0   0       M.k1{v r3} (fun)\n')
    b = head + (
        '         2         200           0   2 MM  '
        'M.$w$w$sf8{v rQPQy} (fun)\n'
        '         8         300           0   2 MM  '
        'N.$w$w$s$w$w$sf23{v r2b91k} (fun,se)\n'
        '         5         500           0   1 M   '
        'g_sat_s2b{v} (M) (fun) in r7\n'
        '         1          40           0   1 M   M.h{v r9} (fun)\n'
        '         1          16           0   0       M.k1{v r8} (fun)\n')
    bad = []
    with tempfile.TemporaryDirectory() as td:
        pa, pb, pn = (os.path.join(td, n) for n in ('a', 'b', 'none'))
        for p, text in ((pa, a), (pb, b), (pn, 'no table here\n')):
            with open(p, 'w') as fh:
                fh.write(text)
        ra, rb = read(pa), read(pb)
        want_a = {'M.$w$w$sf (fun)': [10, 1000], 'g_sat (M) (fun)': [5, 500],
                  'M.h (fun)': [1, 40], 'M.k (fun)': [1, 16]}
        if dict(ra) != want_a:
            bad.append(f'normalised A: {dict(ra)}')
        got = diff(ra, rb, 2)
        want = ['total alloc 1556 -> 1056  (0.6787)',
                f'{-800:+12d}  alloc {1000:11d} -> {200:11d}  entries '
                f'{10:9d} -> {2:9d}  M.$w$w$sf (fun)',
                f'{300:+12d}  alloc {0:11d} -> {300:11d}  entries '
                f'{0:9d} -> {8:9d}  N.$w$w$s$w$w$sf (fun,se)']
        if got != want:
            bad.append('diff:\n  ' + '\n  '.join(got))
        if read(pn) is not None:
            bad.append('a file without the table read as an empty table')
        if main([pa, pn]) != 2:
            bad.append('a file without the table did not exit 2')
    for b_ in bad:
        print('FAIL', b_)
    print('self-test', 'FAILED' if bad else 'passed')
    return 1 if bad else 0


def main(argv):
    if argv == ['--self-test']:
        return self_test()
    top = 40
    if argv[:1] == ['--top']:
        if len(argv) < 2 or not argv[1].isdigit():
            print('--top needs a number', file=sys.stderr)
            return 2
        top, argv = int(argv[1]), argv[2:]
    if len(argv) != 2:
        print(__doc__.split('\n\n')[1], file=sys.stderr)
        return 2
    tables = []
    for path in argv:
        try:
            t = read(path)
        except OSError as e:
            print(f'cannot read {path}: {e.strerror}', file=sys.stderr)
            return 2
        if t is None:
            print(f'{path} has no per-closure ticky table; was the binary '
                  'built with -ticky?', file=sys.stderr)
            return 2
        tables.append(t)
    print('\n'.join(diff(tables[0], tables[1], top)))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
