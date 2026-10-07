#!/usr/bin/env python3
"""List the lazy bindings a per-element computation reads.

Usage: python3 tools/lazy-reads.py TREE
       python3 tools/lazy-reads.py --self-test

For every `.hs` file under TREE and every top-level definition in it, this
lists each value binding with no bang and no parameters, in a `let`,
a `where` or a continuation line of their blocks, that the definition reads
inside a lambda, inside an operator section, or as an argument of
a per-element combinator (`map`, `foldl'`, `zipWith`, `generate`, `all`,
orthotope's `vMap` and `vZipWith` and the like), with the ways it is read.
Such a binding is a thunk that each element's code forces, or a boxed value
it unboxes, on every element, unless GHC proves it strict; an element
captured so is how 908 cost orthotope's `allSameT` (docs/perf-checklist.md,
L1 and L2).

A binding whose right-hand side is a lambda is a function and is passed
over. Each line printed is a candidate to read and not a defect: laziness
may be the contract, as for a boxed element a caller may leave undefined,
and a binding read once outside the loop costs nothing.

Exit 0 when nothing was found, 1 when something was, 2 when TREE holds
no `.hs` file.
"""

import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hssource import split_functions, strip_comments  # noqa: E402

PER_ELEM = (r"\b(vMap|vAll|vAny|vZipWith\w*|vGenerate|vFold\w*|vFromListN|"
            r"all|any|map|foldl'?|foldr|zipWith\w*|filter|iterate|"
            r"generate\w*|sum|product|maximum|minimum)\b")
BINDING = re.compile(r"^\s*(?:let\s+|where\s+|)([a-z_][\w']*)\s*=(?!=)\s*(.*)$")


def reads(tree):
    """(lines reported, number of files read)."""
    out, read = [], 0
    for dp, ds, fs in os.walk(tree):
        ds[:] = sorted(d for d in ds if not d.startswith(('.', 'dist')))
        for f in sorted(fs):
            if not f.endswith('.hs'):
                continue
            p = os.path.join(dp, f)
            read += 1
            with open(p, errors='replace') as fh:
                defs = split_functions(strip_comments(fh.read()))
            for fn, body in defs.items():
                lines = body.split('\n')
                for i, line in enumerate(lines):
                    m = BINDING.match(line)
                    if not m or line.startswith(fn):
                        continue
                    x, rhs = m.group(1), m.group(2)
                    if x == 'in' or not rhs or rhs.lstrip().startswith('\\'):
                        continue
                    e = re.escape(x)
                    tags = set()
                    for j, u in enumerate(lines):
                        if j == i or not re.search(r"\b" + e + r"\b", u):
                            continue
                        if re.search(r"\\[^->]*->.*\b" + e + r"\b", u):
                            tags.add('lambda')
                        if re.search(r"\(\s*" + e + r"\s*[^\w\s(),\[\]]+\s*\)"
                                     r"|\(\s*[^\w\s(),\[\]]+\s*" + e
                                     + r"\s*\)", u):
                            tags.add('section')
                        if re.search(PER_ELEM + r".*\b" + e + r"\b", u):
                            tags.add('per-elem-arg')
                    if tags:
                        out.append(f"{os.path.relpath(p, tree)}\t{fn}\t"
                                   f"{x} = {rhs[:70]}\t{','.join(sorted(tags))}")
    return out, read


def self_test():
    """A module whose bindings are read in a lambda, in a section, by
    a helper only, under a bang, and one that is itself a lambda."""
    import tempfile
    src = ('module M where\n'
           'f v xs = map (\\i -> i + x) xs\n'
           '  where x = expensive v\n'
           'g v xs = map (+ y) xs\n'
           '  where y = expensive v\n'
           'h v xs = foldl\' step 0 xs\n'
           '  where z = expensive v\n'
           '        step a b = a + b + z\n'
           'p v xs = map (\\i -> i + w) xs\n'
           '  where !w = expensive v\n'
           'q v = map r v\n'
           '  where r = \\a -> a\n')
    bad = []
    with tempfile.TemporaryDirectory() as td:
        os.makedirs(os.path.join(td, 'T', 'src'))
        os.makedirs(os.path.join(td, 'E'))
        with open(os.path.join(td, 'T', 'src', 'M.hs'), 'w') as fh:
            fh.write(src)
        got, read = reads(os.path.join(td, 'T'))
        want = ['src/M.hs\tf\tx = expensive v\tlambda,per-elem-arg',
                'src/M.hs\tg\ty = expensive v\tper-elem-arg,section']
        if got != want or read != 1:
            bad.append(f'reads ({read} read):\n  ' + '\n  '.join(got))
        if main([os.path.join(td, 'T')]) != 1:
            bad.append('findings did not exit 1')
        if main([os.path.join(td, 'E')]) != 2:
            bad.append('a tree without .hs files did not exit 2')
    for b in bad:
        print('FAIL', b)
    print('self-test', 'FAILED' if bad else 'passed')
    return 1 if bad else 0


def main(argv):
    if argv == ['--self-test']:
        return self_test()
    if len(argv) != 1 or argv[0].startswith('--'):
        print(__doc__.split('\n\n')[1], file=sys.stderr)
        return 2
    lines, read = reads(argv[0])
    if not read:
        print(f'no .hs file under {argv[0]}', file=sys.stderr)
        return 2
    if lines:
        print('\n'.join(lines))
    return 1 if lines else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
