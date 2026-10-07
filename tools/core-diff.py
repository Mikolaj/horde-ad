#!/usr/bin/env python3
"""Compare the optimised Core of two builds, module by module.

Usage: python3 tools/core-diff.py DIR_A DIR_B
       python3 tools/core-diff.py DIR_A DIR_B --module SUBSTRING
       python3 tools/core-diff.py DIR --module SUBSTRING
       python3 tools/core-diff.py DIR_A DIR_B --verdicts
       python3 tools/core-diff.py --self-test

DIR_A and DIR_B are two build directories whose modules were compiled with
`--ghc-options="-ddump-simpl -ddump-to-file -dsuppress-uniques"` and
`-dsuppress-all` or `-dsuppress-idinfo`, the dumps landing beside the
objects; a separate `--builddir` for each keeps the two apart. Two trees
written with `-dumpdir` serve as well. The first form prints, for every
module whose number of top-level bindings or size in terms of its Tidy Core
differs, both builds' figures, largest growth first, and the totals.
The second form lists, for the modules whose path contains SUBSTRING, the
binding names whose count or size differs --- the specialisations and
workers one build has and the other has not --- with the terms of each
name's bindings where both builds' dumps were made with `-dsuppress-idinfo`,
which keeps the per-binding size comments `-dsuppress-all` drops. The third
form gives every module a verdict: `same`, Core identical but for the
timestamps GHC writes; `literals`, identical once unboxed numeric literals
are blanked too, a call stack's source line moving with each line added
above it in a file the module inlined code from; or `differs`. Modules with
the same Core are the controls a timing comparison wants (tools/ctime-diff.py).
The fourth reads one build: for the modules whose path contains SUBSTRING,
every binding name with its count, and its terms where the dump has size
comments, largest first --- the copies of a function to set against
a prediction of them (docs/perf-checklist.md, S2).

This is what shows where a flag or pragma puts its compile-time cost. Taking
`-fno-expose-overloaded-unfoldings` off `AstSimplify` left its own Core as it
was and grew its importers' 2.3-fold, `AstVectorize`'s 37-fold, which timing
the module itself cannot show (docs/overloaded-unfoldings.md).

Binding names are normalised as `-dsuppress-uniques` leaves them: the module
qualifier and the numeric suffix GHC gives each specialisation or worker are
dropped, so `$sf3` and `$sf7` count as two of `$sf`, and a renumbering
between builds is not a difference. A dump made without `-dsuppress-all`
prints a binder at column 0 twice, in its type signature and at its
definition, so there a binding is counted from the size comment above it
(core-diff-03). The size is the "Result size of Tidy Core" of each dump.
Modules are matched by their dumps' paths below the last `build/` directory,
or below the tree's root where there is none (core-diff-02).

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

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dumps  # noqa: E402

SIZE = re.compile(r'Result size of Tidy Core\s*=\s*\{terms: ([\d,]+)')
RHS = re.compile(r'-- RHS size: \{terms: ([\d,]+)')
SKIP = ('Rec {', 'end Rec', 'Result size')


class Module:
    """One module's Core: binding counts and, where the dump carries size
    comments, terms by binding name; total terms; the two digests."""
    def __init__(self, names, sizes, terms, digests):
        self.names, self.sizes, self.terms, self.digests = (
            names, sizes, terms, digests)


def family(tok):
    """A binder as the name it is counted under: module qualifier dropped,
    and the numeric suffix after a name's letter."""
    tok = re.sub(r"^(?:[A-Z][\w']*\.)+(?=\S)", '', tok)
    return re.sub(r"([A-Za-z_$'])[0-9]+\b", r'\1', tok)


def bindings(txt):
    """(Counter of binder names, Counter of their terms or None) of a dump:
    from the size comment above each binding where the dump has them, else
    from the binders at column 0 of a -dsuppress-all dump."""
    names = collections.Counter()
    lines = txt.split('\n')
    if any(RHS.match(line) for line in lines):
        sizes, pending = collections.Counter(), None
        for line in lines:
            m = RHS.match(line)
            if m:
                pending = int(m.group(1).replace(',', ''))
            elif pending is not None and line and line[0] not in ' \t':
                tok = family(line.split(None, 1)[0])
                names[tok] += 1
                sizes[tok] += pending
                pending = None
        return names, sizes
    for line in lines:
        if not line or line[0] in ' \t=-{' or line.startswith(SKIP):
            continue
        tok = line.split(None, 1)[0]
        if re.match(r'[A-Za-z_$]', tok):
            names[family(tok)] += 1
    return names, None


def scan(root):
    """Module key -> Module. Raises ValueError on a dump without its size."""
    out = {}
    for p, key in dumps.walk(root, '.dump-simpl'):
        txt = dumps.read_text(p)
        m = SIZE.search(txt)
        if not m:
            raise ValueError(f'{p} has no "Result size of Tidy Core" line')
        names, sizes = bindings(txt)
        out[key] = Module(names, sizes, int(m.group(1).replace(',', '')),
                          dumps.core_digests(txt))
    return out


EMPTY = Module(collections.Counter(), None, 0, None)


def summary(a, b):
    lines, tot = [], [0, 0, 0, 0]
    keys = sorted(set(a) | set(b), key=lambda k: (
        -(b.get(k, EMPTY).terms - a.get(k, EMPTY).terms), k))
    for k in keys:
        ma, mb = a.get(k, EMPTY), b.get(k, EMPTY)
        ca, cb = sum(ma.names.values()), sum(mb.names.values())
        ta, tb = ma.terms, mb.terms
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
        ma, mb = a.get(k, EMPTY), b.get(k, EMPTY)
        sized = ma.sizes is not None and mb.sizes is not None
        sa = ma.sizes if sized else collections.Counter()
        sb = mb.sizes if sized else collections.Counter()
        rows = [(n, sb[n] - sa[n], mb.names[n] - ma.names[n])
                for n in set(ma.names) | set(mb.names)
                if ma.names[n] != mb.names[n] or sa[n] != sb[n]]
        lines.append(f'== {k}' + ('' if sized else
                                  '  (no size comments: counts only)'))
        rows.sort(key=lambda r: (-abs(r[1]), -abs(r[2]), r[0]))
        for n, _, _ in rows:
            terms = f'  terms {sa[n]:8d} -> {sb[n]:8d}' if sized else ''
            lines.append(f'  {ma.names[n]:5d} -> {mb.names[n]:5d}{terms}  {n}')
    return lines


def names_census(t, sub):
    lines = []
    for k in sorted(t):
        if sub not in k:
            continue
        m = t[k]
        sizes = m.sizes if m.sizes is not None else collections.Counter()
        lines.append(f'== {k}' + ('' if m.sizes is not None else
                                  '  (no size comments: counts only)'))
        for n in sorted(m.names, key=lambda n: (-sizes[n], -m.names[n], n)):
            terms = f'  terms {sizes[n]:8d}' if m.sizes is not None else ''
            lines.append(f'  {m.names[n]:5d}{terms}  {n}')
    return lines


def verdict(ma, mb):
    """same, literals or differs, for one module present in both builds."""
    if ma.digests[0] == mb.digests[0]:
        return 'same'
    return 'literals' if ma.digests[1] == mb.digests[1] else 'differs'


def verdicts(a, b):
    """{key: verdict}, a module in one build only being 'only A' or 'only B'."""
    return {k: (verdict(a[k], b[k]) if k in a and k in b
                else 'only A' if k in a else 'only B')
            for k in set(a) | set(b)}


def verdict_lines(a, b):
    vs = verdicts(a, b)
    lines = [f'{vs[k]:9s} {k:60s} terms {a.get(k, EMPTY).terms:9d} -> '
             f'{b.get(k, EMPTY).terms:9d}' for k in sorted(vs)]
    tally = collections.Counter(vs.values())
    lines.append(', '.join(f'{tally[v]} {v}' for v in
                           ('same', 'literals', 'differs', 'only A', 'only B')
                           if tally[v]))
    return lines


def self_test():
    """Synthetic dump trees: in cabal's layout with -dsuppress-all, one module
    growing and one unchanged; in -dumpdir's layout with size comments, a
    specialisation gained, a module moved only by a literal, and one equal."""
    import tempfile
    head = '\n==================== Tidy Core ====================\n'
    size = 'Result size of Tidy Core\n  = {{terms: {}, types: 1}}\n\n'
    def dump(terms, binds):
        return (head + size.format(terms)
                + ''.join(f'{b}\n  = \\ x -> x\n\n' for b in binds)
                + 'Rec {\nloop = loop\nend Rec }\n')
    def sized(terms, binds, stamp='2026-10-05 10:00:00.123 UTC', lit='7#'):
        rhs = '-- RHS size: {{terms: {}, types: 1, coercions: 0, joins: 0/0}}\n'
        return (head + f'{stamp}\n\n' + size.format(terms)
                + ''.join(rhs.format(t) + f'{b} :: Int\n{b} = I# {lit}\n\n'
                          for b, t in binds))
    bad = []
    with tempfile.TemporaryDirectory() as td:
        tree = {
            'A/build/src/M/User.dump-simpl': dump('1,000', ['f', '$wf']),
            'A/build/src/M/Same.dump-simpl': dump('10', ['g']),
            'B/build/src/M/User.dump-simpl':
                dump('2,500', ['f', '$wf', '$sf1', '$sf2', '$w$sf3']),
            'B/build/src/M/Same.dump-simpl': dump('10', ['g']),
            'C/build/src/M/User.dump-simpl': 'no size line\n',
            'D/M/User.dump-simpl': sized('5', [('M.f', 2), ('lvl1', 3)]),
            'D/M/Lit.dump-simpl': sized('2', [('h', 2)]),
            'D/M/Eq.dump-simpl': sized('2', [('e', 2)]),
            'E/M/User.dump-simpl':
                sized('9', [('M.f', 2), ('M.$sf12', 4), ('lvl7', 3)],
                      stamp='2026-10-05 11:11:11.456 UTC'),
            'E/M/Lit.dump-simpl': sized('2', [('h', 2)], lit='8#'),
            'E/M/Eq.dump-simpl.gz': sized('2', [('e', 2)],
                                          stamp='2026-10-06 09:00:00 UTC'),
        }
        import gzip
        for rel, text in tree.items():
            p = os.path.join(td, rel)
            os.makedirs(os.path.dirname(p), exist_ok=True)
            op = gzip.open if p.endswith('.gz') else open
            with op(p, 'wt') as fh:
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
        want = ['== src/M/User  (no size comments: counts only)',
                f'  {0:5d} -> {2:5d}  $sf', f'  {0:5d} -> {1:5d}  $w$sf']
        if got != want:
            bad.append('names:\n  ' + '\n  '.join(got))
        d, e = scan(os.path.join(td, 'D')), scan(os.path.join(td, 'E'))
        if sorted(d) != ['M/Eq', 'M/Lit', 'M/User'] or sorted(e) != sorted(d):
            bad.append(f'-dumpdir keys: {sorted(d)} and {sorted(e)}')
        got = summary(d, e)
        want = [f'{"M/User":60s} bindings {2:6d} -> {3:6d}  '
                f'terms {5:9d} -> {9:9d} {1.8:6.2f}',
                f'{"TOTAL":60s} bindings {4:6d} -> {5:6d}  '
                f'terms {9:9d} -> {13:9d} {13 / 9:6.2f}']
        if got != want:
            bad.append('summary over size comments:\n  ' + '\n  '.join(got))
        got = names_diff(d, e, 'User')
        want = ['== M/User', f'  {0:5d} -> {1:5d}  terms {0:8d} -> {4:8d}  $sf']
        if got != want:
            bad.append('names over size comments:\n  ' + '\n  '.join(got))
        got = verdicts(d, e)
        want = {'M/User': 'differs', 'M/Lit': 'literals', 'M/Eq': 'same'}
        if got != want:
            bad.append(f'verdicts: {got}')
        if verdicts(a, b)['src/M/Same'] != 'same':
            bad.append('an unchanged -dsuppress-all module is not the same')
        empty = os.path.join(td, 'empty')
        os.makedirs(empty)
        if main([os.path.join(td, 'A'), empty]) != 2:
            bad.append('a directory without dumps did not exit 2')
        if main([os.path.join(td, 'A'), os.path.join(td, 'C')]) != 2:
            bad.append('a dump without its result size did not exit 2')
        if main([os.path.join(td, 'A'), os.path.join(td, 'B'),
                 '--module', 'NoSuch']) != 2:
            bad.append('a --module matching no module did not exit 2')
        got = names_census(e, 'User')
        want = ['== M/User', f'  {1:5d}  terms {4:8d}  $sf',
                f'  {1:5d}  terms {3:8d}  lvl', f'  {1:5d}  terms {2:8d}  f']
        if got != want:
            bad.append('one-build names:\n  ' + '\n  '.join(got))
        got = names_census(b, 'User')
        want = ['== src/M/User  (no size comments: counts only)',
                f'  {2:5d}  $sf', f'  {1:5d}  $w$sf', f'  {1:5d}  $wf',
                f'  {1:5d}  f', f'  {1:5d}  loop']
        if got != want:
            bad.append('one-build names without size comments:\n  '
                       + '\n  '.join(got))
        if main([os.path.join(td, 'B'), '--module', 'NoSuch']) != 2:
            bad.append('a one-build --module matching no module did not '
                       'exit 2')
    for b_ in bad:
        print('FAIL', b_)
    print('self-test', 'FAILED' if bad else 'passed')
    return 1 if bad else 0


def main(argv):
    if argv == ['--self-test']:
        return self_test()
    sub, mode = None, 'summary'
    if len(argv) == 4 and argv[2] == '--module':
        sub, argv, mode = argv[3], argv[:2], 'module'
    elif len(argv) == 3 and argv[1] == '--module':
        sub, argv, mode = argv[2], argv[:1], 'census'
    elif len(argv) == 3 and argv[2] == '--verdicts':
        argv, mode = argv[:2], 'verdicts'
    if len(argv) != (1 if mode == 'census' else 2):
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
    lines = (names_census(trees[0], sub) if mode == 'census'
             else names_diff(*trees, sub) if mode == 'module'
             else verdict_lines(*trees) if mode == 'verdicts'
             else summary(*trees))
    print('\n'.join(lines))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
