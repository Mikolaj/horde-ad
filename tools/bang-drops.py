#!/usr/bin/env python3
"""Find the bangs a later version of a Haskell tree dropped.

Usage: python3 tools/bang-drops.py OLD NEW
       python3 tools/bang-drops.py --self-test

OLD and NEW are two versions of one source tree, two checkouts, say, or a
`git worktree` of the base beside the branch. For every `.hs` file in both
and every top-level definition in both versions of it, this reports each
name OLD's definition binds with a bang and NEW's binds without one, in a
`let`, a `where`, a continuation line of their blocks or a `<-`, with the
unbanged lines; and each banged name of OLD's definition that NEW's no
longer mentions, which a rewrite may have moved elsewhere.

This is how 908 was found in orthotope: `allSameT`'s `!x` dropped for
a reason a later guard removed, the element then unboxed again on every
iteration once a client specialised it (docs/perf-checklist.md, L1). A
dropped bang is a question and not a verdict: a bang that forced a boxed
element may have gone on purpose, laziness being the contract.
tools/bang-lazy-check.py asks the other question, of one tree: a bang
on some equations of a definition and not on others.

Exit 0 when no bang was dropped, 1 when one was, 2 when the comparison did
not happen: OLD or NEW not a directory, or no `.hs` file in both.
"""

import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hssource import split_functions, strip_comments  # noqa: E402

BANG = re.compile(r"(?:(?<=[\s(\[,])|^)!([a-z_][\w']*)")


def defs(path):
    with open(path, errors='replace') as fh:
        return split_functions(strip_comments(fh.read()))


def drops(old, new):
    """(lines reported, number of files compared)."""
    out, compared = [], 0
    for dp, ds, fs in os.walk(old):
        ds[:] = sorted(d for d in ds if not d.startswith(('.', 'dist')))
        for f in sorted(fs):
            if not f.endswith('.hs'):
                continue
            po = os.path.join(dp, f)
            rel = os.path.relpath(po, old)
            pn = os.path.join(new, rel)
            if not os.path.exists(pn):
                continue
            compared += 1
            o, n = defs(po), defs(pn)
            for fn, body in o.items():
                if fn not in n:
                    continue
                nb = n[fn]
                for x in sorted(set(BANG.findall(body))):
                    e = re.escape(x)
                    un = [ln.strip() for ln in nb.split('\n')
                          if re.search(r"(?:\blet\s+|\bwhere\s+|^\s+)" + e
                                       + r"\s*=(?!=)", ln)
                          or re.search(r"(?:^|[\s(,{;])" + e + r"\s*<-", ln)]
                    if un:
                        out.append(f'{rel}: {fn}: {x} banged in old, '
                                   f'unbanged in new: {un}')
                    elif not re.search(r"\b" + e + r"\b", nb):
                        out.append(f'{rel}: {fn}: {x} banged in old, '
                                   'gone from new')
    return out, compared


def self_test():
    """Two versions of a module: a bang dropped from a `let`, a `where`
    and a `<-`, a banged binding gone, one kept, and a file only in OLD."""
    import tempfile
    old = ('module M where\n'
           'f v = let !x = g v in x + 1\n'
           'h v = go v where !n = 3\n'
           'k v = do { !y <- get v; return y }\n'
           'gone v = let !z = 1 in z\n'
           'same v = let !s = 1 in s\n'
           '-- c v = let !c = 1 in c\n')
    new = ('module M where\n'
           'f v = let x = g v in x + 1\n'
           'h v = go v\n  where n = 3\n'
           'k v = do { y <- get v; return y }\n'
           'gone v = 1\n'
           'same v = let !s = 1 in s\n')
    bad = []
    with tempfile.TemporaryDirectory() as td:
        for rel, text in (('O/src/M.hs', old), ('N/src/M.hs', new),
                          ('O/src/Only.hs', 'module Only where\n'
                                            'o = let !q = 1 in q\n')):
            p = os.path.join(td, rel)
            os.makedirs(os.path.dirname(p), exist_ok=True)
            with open(p, 'w') as fh:
                fh.write(text)
        O, N = os.path.join(td, 'O'), os.path.join(td, 'N')
        got, compared = drops(O, N)
        want = ["src/M.hs: f: x banged in old, unbanged in new: "
                "['f v = let x = g v in x + 1']",
                "src/M.hs: h: n banged in old, unbanged in new: "
                "['where n = 3']",
                "src/M.hs: k: y banged in old, unbanged in new: "
                "['k v = do { y <- get v; return y }']",
                'src/M.hs: gone: z banged in old, gone from new']
        if got != want or compared != 1:
            bad.append(f'drops ({compared} compared):\n  ' + '\n  '.join(got))
        if main([N, N]) != 0:
            bad.append('a tree against itself did not exit 0')
        if main([O, N]) != 1:
            bad.append('dropped bangs did not exit 1')
        if main([O, os.path.join(td, 'nothing')]) != 2:
            bad.append('a missing NEW did not exit 2')
    for b in bad:
        print('FAIL', b)
    print('self-test', 'FAILED' if bad else 'passed')
    return 1 if bad else 0


def main(argv):
    if argv == ['--self-test']:
        return self_test()
    if len(argv) != 2 or any(a.startswith('--') for a in argv):
        print(__doc__.split('\n\n')[1], file=sys.stderr)
        return 2
    for d in argv:
        if not os.path.isdir(d):
            print(f'{d} is not a directory', file=sys.stderr)
            return 2
    lines, compared = drops(*argv)
    if not compared:
        print(f'no .hs file is in both {argv[0]} and {argv[1]}',
              file=sys.stderr)
        return 2
    if lines:
        print('\n'.join(lines))
    return 1 if lines else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
