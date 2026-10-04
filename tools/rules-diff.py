#!/usr/bin/env python3
"""Compare which rewrite rules fired, and what was inlined, in two builds.

Usage: python3 tools/rules-diff.py DIR_A DIR_B [--module SUBSTRING]
                                   [--unfolding NAME]...
       python3 tools/rules-diff.py --self-test

DIR_A and DIR_B are two build directories, or two trees written with
`-dumpdir`, whose modules were compiled with `--ghc-options="-ddump-simpl-stats
-ddump-to-file -dsuppress-uniques"` (tools/core-diff.py says how to keep two
builds apart, and the same build can carry its `-ddump-simpl` dumps too).
For every module whose counts differ it lists the rules whose firing count
differs, A against B, largest change first, the fusion rules marked; then the
totals of the fusion rules and of all rules. With `--module` only the modules
whose path contains SUBSTRING are shown. Each `--unfolding NAME` adds, per
module, the inlinings GHC counted as UnfoldingDone of every name containing
NAME: what an INLINE or a smaller unfolding changed at the call sites.

This answers whether what fused still fuses. A change that shares code may
lower a count only because a copy is gone --- one consumer fused once
instead of twice --- so read a fusion rule's drop against the module's Core
(tools/core-diff.py) before calling it lost fusion. The fusion rules are the
ones that fire where a consumer meets a producer: base's `fold/build`,
`foldr/augment`, `augment/build`, `augment/augment`, `foldr2/left` and
`foldr2/right`, and the vector package's, which it names for the two
operations meeting --- `stream/unstream [Vector]`, `clone/new [Vector]`,
`transform/unstream [New]` --- every name of the form `A/B [Vector]` or
`A/B [New]` in vector 0.13. The rules that only rewrite into and out of the
fusible forms, `map`, `mapList`, `inplace [Vector]` and the like, are listed
unmarked.

Only the "Grand total simplifier statistics" block of each dump is read, not
the FloatOut statistics before it; within it, a section header is a count and
a tick kind at column 0 and an entry is an indented count and a name, which
may hold spaces (`Class op ==`). Same-named entries are summed, a name
standing for every binding that prints alike. Modules are keyed as
tools/dumps.py says.

Exit 0 when the comparison was printed, 2 when it could not be: a tree with
no `.dump-simpl-stats` file, or one without the grand total, so that a build
made without the flag does not read as one where no rule moved; a SUBSTRING
no module's path contains; and a NAME no UnfoldingDone entry of either build
contains, which would read as a function never inlined.
"""

import collections
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dumps  # noqa: E402

GRAND = 'Grand total simplifier statistics'
HEADER = re.compile(r'^(\d+) (\S.*?)\s*$')
ENTRY = re.compile(r'^\s+(\d+) (\S.*?)\s*$')
FUSION_NAMES = {'fold/build', 'foldr/augment', 'augment/build',
                'augment/augment', 'foldr2/left', 'foldr2/right'}
# vector names its fusion rules for the two operations meeting, with a tag
# in brackets: `stream/unstream [Vector]`, `transform/unstream [New]`.
VECTOR_FUSION = re.compile(r'^\S+/\S+ \[(?:Vector|New)\]$')


def fusion(rule):
    return rule in FUSION_NAMES or bool(VECTOR_FUSION.match(rule))


def ticks(txt):
    """{tick kind: Counter of entry names} of a stats dump's grand total, or
    None when the dump has none."""
    start = txt.find('= ' + GRAND + ' =')
    if start < 0:
        return None
    out = collections.defaultdict(collections.Counter)
    kind = None
    for line in txt[start:].split('\n')[1:]:
        if line.startswith('===='):
            break
        m = HEADER.match(line)
        if m:
            kind = m.group(2)
            continue
        m = ENTRY.match(line)
        if m and kind is not None:
            out[kind][m.group(2)] += int(m.group(1))
    return out


def scan(root):
    """Module key -> ticks. Raises ValueError on a dump without the total."""
    out = {}
    for p, key in dumps.walk(root, '.dump-simpl-stats'):
        t = ticks(dumps.read_text(p))
        if t is None:
            raise ValueError(f'{p} has no "{GRAND}" block')
        out[key] = t
    return out


def rule_lines(a, b, keys):
    lines, fus, tot = [], [0, 0], [0, 0]
    for k in keys:
        ra = a.get(k, {}).get('RuleFired', collections.Counter())
        rb = b.get(k, {}).get('RuleFired', collections.Counter())
        rows = sorted(((rb[n] - ra[n], n) for n in set(ra) | set(rb)
                       if ra[n] != rb[n]), key=lambda r: (-abs(r[0]), r[1]))
        for n in set(ra) | set(rb):
            if fusion(n):
                fus = [fus[0] + ra[n], fus[1] + rb[n]]
        tot = [tot[0] + sum(ra.values()), tot[1] + sum(rb.values())]
        if rows:
            lines.append(f'== {k}')
            for _, n in rows:
                mark = 'fusion' if fusion(n) else '      '
                lines.append(f'  {mark} {ra[n]:7d} -> {rb[n]:7d}  {n}')
    lines.append(f'fusion rules fired {fus[0]} -> {fus[1]}, '
                 f'all rules fired {tot[0]} -> {tot[1]}')
    return lines


def unfolding_lines(a, b, keys, name):
    lines = [f'== UnfoldingDone of names containing {name}']
    for k in keys:
        ua = a.get(k, {}).get('UnfoldingDone', collections.Counter())
        ub = b.get(k, {}).get('UnfoldingDone', collections.Counter())
        for n in sorted(x for x in set(ua) | set(ub) if name in x):
            lines.append(f'  {ua[n]:7d} -> {ub[n]:7d}  {n}  in {k}')
    return lines


def self_test():
    """Two trees of synthetic stats dumps, each with a FloatOut block before
    its grand total: one module's fusion rule drops and a rule with spaces in
    its name moves, another module's counts agree."""
    import tempfile
    def stats(fb, op, mapfb, sumt):
        return ('\n==================== FloatOut stats: ====================\n'
                '2026-10-05 10:00:00.1 UTC\n\n'
                '9 Lets floated to top level; 1 Lets floated elsewhere\n\n'
                f'\n==================== {GRAND} ====================\n'
                '2026-10-05 10:00:01.2 UTC\n\nTotal ticks:     99\n\n'
                '40 PreInlineUnconditionally\n  20 g\n  20 a\n'
                f'{sumt + 2} UnfoldingDone\n  {sumt} Data.Array.Internal.sumT\n'
                '  1 $sallSameT\n  1 $sallSameT\n'
                f'{fb + op + mapfb} RuleFired\n  {fb} fold/build\n'
                f'  {op} Class op ==\n  {mapfb} mapFB\n'
                '7 BetaReduction\n  7 x\n')
    bad = []
    with tempfile.TemporaryDirectory() as td:
        tree = {
            'A/build/src/M/User.dump-simpl-stats': stats(4, 3, 2, 5),
            'A/build/src/M/Same.dump-simpl-stats': stats(1, 1, 1, 1),
            'B/build/src/M/User.dump-simpl-stats': stats(3, 5, 2, 0),
            'B/build/src/M/Same.dump-simpl-stats': stats(1, 1, 1, 1),
            'C/build/src/M/User.dump-simpl-stats': '1 RuleFired\n  1 map\n',
        }
        for rel, text in tree.items():
            p = os.path.join(td, rel)
            os.makedirs(os.path.dirname(p), exist_ok=True)
            with open(p, 'w') as fh:
                fh.write(text)
        a, b = scan(os.path.join(td, 'A')), scan(os.path.join(td, 'B'))
        if a['src/M/User']['UnfoldingDone']['$sallSameT'] != 2:
            bad.append('same-named UnfoldingDone entries not summed')
        if 'Lets floated to top level; 1 Lets floated elsewhere' in str(a):
            bad.append('the FloatOut block read as ticks')
        got = rule_lines(a, b, sorted(set(a) | set(b)))
        want = ['== src/M/User',
                f'         {3:7d} -> {5:7d}  Class op ==',
                f'  fusion {4:7d} -> {3:7d}  fold/build',
                'fusion rules fired 5 -> 4, all rules fired 12 -> 13']
        if got != want:
            bad.append('rules:\n  ' + '\n  '.join(got))
        got = unfolding_lines(a, b, ['src/M/User'], 'sumT')
        want = ['== UnfoldingDone of names containing sumT',
                f'  {5:7d} -> {0:7d}  Data.Array.Internal.sumT  in src/M/User']
        if got != want:
            bad.append('unfoldings:\n  ' + '\n  '.join(got))
        for rule, want in (('stream/unstream [Vector]', True),
                           ('transform/unstream [New]', True),
                           ('(!)/unstream [Vector]', True), ('mapList', False),
                           ('inplace [Vector]', False),
                           ('SPEC/Data.Vector slice @Vector @_', False)):
            if fusion(rule) != want:
                bad.append(f'{rule} classified as fusion: {not want}')
        A, B = os.path.join(td, 'A'), os.path.join(td, 'B')
        empty = os.path.join(td, 'empty')
        os.makedirs(empty)
        C = os.path.join(td, 'C')
        for argv, why in (
                ([A, empty], 'a tree without stats dumps'),
                ([A, C], 'a dump without the grand total'),
                ([A, B, '--module', 'NoSuch'], 'a --module matching nothing'),
                ([A, B, '--unfolding', 'noSuchName'],
                 'an --unfolding no entry contains')):
            if main(argv) != 2:
                bad.append(f'{why} did not exit 2')
    for b_ in bad:
        print('FAIL', b_)
    print('self-test', 'FAILED' if bad else 'passed')
    return 1 if bad else 0


def main(argv):
    if argv == ['--self-test']:
        return self_test()
    sub, names, rest = None, [], []
    i = 0
    while i < len(argv):
        if argv[i] in ('--module', '--unfolding') and i + 1 < len(argv):
            if argv[i] == '--module':
                sub = argv[i + 1]
            else:
                names.append(argv[i + 1])
            i += 2
        else:
            rest.append(argv[i])
            i += 1
    if len(rest) != 2 or any(r.startswith('--') for r in rest):
        print(__doc__.split('\n\n')[1], file=sys.stderr)
        return 2
    trees = []
    for d in rest:
        try:
            t = scan(d)
        except ValueError as e:
            print(e, file=sys.stderr)
            return 2
        if not t:
            print(f'no .dump-simpl-stats file under {d}; was it built with '
                  '-ddump-simpl-stats -ddump-to-file?', file=sys.stderr)
            return 2
        trees.append(t)
    keys = sorted(k for k in set(trees[0]) | set(trees[1])
                  if sub is None or sub in k)
    if not keys:
        print(f"no module's path contains {sub}", file=sys.stderr)
        return 2
    lines = rule_lines(*trees, keys)
    for n in names:
        if not any(n in x for t in trees for k in keys
                   for x in t.get(k, {}).get('UnfoldingDone', ())):
            print(f'no UnfoldingDone entry contains {n} in either build',
                  file=sys.stderr)
            return 2
        lines += unfolding_lines(*trees, keys, n)
    print('\n'.join(lines))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
