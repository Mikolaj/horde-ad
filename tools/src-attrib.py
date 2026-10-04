#!/usr/bin/env python3
"""Attribute a Core dump's code to the source definitions it came from.

Usage: python3 tools/src-attrib.py DUMP SRCDIR [--top N] [--with-notes]
       python3 tools/src-attrib.py DUMP_A SRCDIR_A DUMP_B SRCDIR_B [--top N]
                                   [--with-notes]
       python3 tools/src-attrib.py --self-test

DUMP is a `-ddump-simpl` dump of a module compiled with `-g1` or more and
without `-dsuppress-ticks` or `-dsuppress-all`, so that its source notes,
`src<file:span>`, are kept; SRCDIR is the package directory the notes'
paths are relative to. A line's characters outside the notes are credited
to the innermost note around the line, a line inside none to `(no note)`,
and summed by the top-level source definition holding the note's first line,
found in SRCDIR's file: the N largest (default 40), with their notes and the
lines carrying most of each.
Two dumps, each with its source directory, are compared definition by
definition, the largest change first. `--with-notes` counts the notes' own
text as well, as the script's first version did.

Where the Core of a module comes from is what this answers: which inlined
function brought how much, the dump otherwise naming the code GHC made
(`go39`, `$j56`, `lvl123`) and not the source. Code inlined from a package
built without `-g` counts to the note around its call, so build the library
under study with `-g1` too. A note's scope is the rest of its line and the
lines after it indented deeper; a note opens one only where it starts an
expression, at the start of a line or after `=`, `->` or `in`, and one on a
case scrutinee or an argument labels its own line alone.

It locates code; it does not predict what a pragma change saves. In one
orthotope test module `-g1` nearly doubled the terms, GHC floated otherwise
and copied notes onto the code it duplicated, and `subArraysT` held 3.0% of
that Core where making it NOINLINE saved 0.17% of the `-O1` Core. Measure
a change by building it (tools/core-diff.py).

A top-level definition is a line at column 0 that is not inside a block
comment: a name, an infix operator's definition (`xs +++ ys = ...`) or its
signature (`(+++) :: ...`), or a declaration --- `instance`, `data`,
`newtype`, `type`, `class`, `pattern` --- named by its head. A note into a
file SRCDIR does not hold is credited to `?` in that file, and the files are
listed.

Exit 0 when the attribution was printed, 2 when it could not be: a dump
with no source note, which a build without `-g` or with `-dsuppress-ticks`
gives, or no note whose file SRCDIR holds.
"""

import collections
import os
import re
import sys

NOTE = re.compile(r'src<([^:>]+):\(?(\d+)')
NOTE_TEXT = re.compile(r'src<[^>]*>')
# What may stand before a note that opens a scope: nothing, or a binding's
# or an alternative's arrow, or `in`.
SCOPE = re.compile(r'^\s*$|(?:=|->|\bin)\s*$')
OPCHARS = r"[!#$%&*+./<=>?@\\^|~:-]+"
NAME_DEF = re.compile(r"^([a-z_][\w']*)\b")
INFIX_DEF = re.compile(r"^[a-z_][\w']*\s+(" + OPCHARS + r")\s")
OP_SIG = re.compile(r"^\((" + OPCHARS + r")\)")
DECL = re.compile(r'^(instance|data|newtype|type|class|pattern)\s+(.*)')
KEYWORDS = {'import', 'module', 'where', 'deriving', 'infixl', 'infixr',
            'infix', 'foreign', 'default'}
# Reserved operators: `g = 1` and `f x | p = ...` define g and f, not = or |.
RESERVED = {'=', '|', '::', '->', '<-', '=>', '@', '~', '\\', '..'}


def definitions(path):
    """[(line, name)] of the top-level definitions in a Haskell file."""
    rows, depth = [], 0
    with open(path, errors='replace') as fh:
        for i, line in enumerate(fh, 1):
            if depth == 0 and not line.startswith(('{-', ' ', '\t', '--', '#')):
                m = DECL.match(line)
                infix = INFIX_DEF.match(line)
                if m:
                    head = ' '.join(m.group(2).split()[:3])
                    rows.append((i, f'{m.group(1)} {head}'))
                elif infix and infix.group(1) not in RESERVED:
                    rows.append((i, infix.group(1)))
                elif OP_SIG.match(line):
                    rows.append((i, OP_SIG.match(line).group(1)))
                else:
                    m = NAME_DEF.match(line)
                    if m and m.group(1) not in KEYWORDS:
                        rows.append((i, m.group(1)))
            depth = max(0, depth + line.count('{-') - line.count('-}'))
    return rows


class Sources:
    def __init__(self, srcdir):
        self.srcdir, self.defs, self.missing = srcdir, {}, set()

    def definition(self, path, line):
        if path not in self.defs:
            p = os.path.join(self.srcdir, path)
            self.defs[path] = definitions(p) if os.path.isfile(p) else None
            if self.defs[path] is None:
                self.missing.add(path)
        best = '?'
        for i, name in self.defs[path] or ():
            if i > line:
                break
            best = name
        return best


def attribute(dump, srcdir, with_notes=False):
    """(total characters, Counter {(file, definition): characters},
    {key: set of note lines}, Counter {(file, line): characters}, Sources)."""
    src = Sources(srcdir)
    chars, bynote = collections.Counter(), collections.Counter()
    notes = collections.defaultdict(set)
    stack, total, seen = [], 0, False
    with open(dump, errors='replace') as fh:
        for raw in fh:
            s = raw.rstrip('\n')
            if not s.strip():
                continue
            ind = len(s) - len(s.lstrip())
            while stack and ind <= stack[-1][0]:
                stack.pop()
            here = None
            for m in NOTE.finditer(s):
                seen = True
                before = s[:m.start()]
                if SCOPE.search(before):
                    stack.append((ind, m.group(1), int(m.group(2))))
                here = (m.group(1), int(m.group(2)))
            body = s.strip() if with_notes else NOTE_TEXT.sub('', s).strip()
            total += len(body)
            top = here or (stack[-1][1:] if stack else None)
            if top:
                f, ln = top
                key = (f, src.definition(f, ln))
                chars[key] += len(body)
                notes[key].add((f, ln))
                bynote[(f, ln)] += len(body)
            else:
                chars[('(no note)', '')] += len(body)
    return (total if seen else None), chars, notes, bynote, src


def single_lines(res, top):
    total, chars, notes, bynote, src = res
    lines = [f'{total} characters']
    for (f, d), c in chars.most_common(top):
        lines.append(f'{100 * c / total if total else 0:5.1f}% {c:10d} '
                     f'{len(notes[(f, d)]):5d} notes  {f} {d}'.rstrip())
        if f != '(no note)':
            best = sorted(((bynote[x], x[1]) for x in notes[(f, d)]),
                          reverse=True)[:3]
            lines.append('        ' + ', '.join(
                f'line {ln} {100 * cc / total if total else 0:.1f}%'
                for cc, ln in best))
    if src.missing:
        lines.append('not under the source directory: '
                     + ', '.join(sorted(src.missing)))
    return lines


def compare_lines(ra, rb, top):
    (ta, ca, _, _, sa), (tb, cb, _, _, sb) = ra, rb
    lines = [f'{ta} characters, then {tb}, {tb - ta:+d}']
    keys = sorted(set(ca) | set(cb), key=lambda k: (-abs(cb[k] - ca[k]), k))
    for k in keys[:top]:
        if ca[k] != cb[k]:
            lines.append(f'{ca[k]:10d} {cb[k]:10d} {cb[k] - ca[k]:+10d}  '
                         f'{k[0]} {k[1]}'.rstrip())
    missing = sorted(sa.missing | sb.missing)
    if missing:
        lines.append('not under a source directory: ' + ', '.join(missing))
    return lines


def usable(res, dump):
    total, chars, _, _, src = res
    if total is None:
        return (f'{dump} has no source note; was it compiled with -g1 and '
                'without -dsuppress-ticks?')
    if not any(f not in src.missing for f, _ in chars if f != '(no note)'):
        return f"no note of {dump} names a file the source directory holds"
    return None


def self_test():
    """A source file with a block comment, an infix operator and a data
    declaration, and two dumps whose notes point into it."""
    import tempfile
    bad = []
    with tempfile.TemporaryDirectory() as td:
        src = os.path.join(td, 'pkg')
        os.makedirs(os.path.join(src, 'M'))
        with open(os.path.join(src, 'M', 'A.hs'), 'w') as fh:
            fh.write('module M.A where\n'           # 1
                     '{- A block comment\n'          # 2
                     'whose lines start at column 0\n'  # 3
                     '-}\n'                          # 4
                     'f :: Int -> Int\n'             # 5
                     'f x = x\n'                     # 6
                     '(+++) :: [a] -> [a] -> [a]\n'  # 7
                     'xs +++ ys = xs\n'              # 8
                     'data T = T Int\n'              # 9
                     '  deriving Eq\n'               # 10
                     'g = 1\n')                      # 11
        def dump(name, body):
            p = os.path.join(td, name)
            with open(p, 'w') as fh:
                fh.write(body)
            return p
        da = dump('a.dump-simpl',
                  'f1 = src<M/A.hs:6:1-7> \\ x ->\n'
                  '  case x of { I# y -> y }\n'
                  'plus = src<M/A.hs:8:1-14>\n'
                  '  \\ xs ys -> xs\n'
                  'eqT = src<M/A.hs:(9,1)-(10,13)> \\ a b -> True\n'
                  'h = 1\n'
                  'k = src<M/A.hs:3:1-5> k\n'
                  'm = src<Elsewhere.hs:1:1-2> 2\n'
                  'r = foo src<M/A.hs:11:1-5> x\n'
                  '  tail\n')
        db = dump('b.dump-simpl',
                  'f1 = src<M/A.hs:6:1-7> \\ x ->\n'
                  '  case x of { I# y -> y }\n'
                  '  -- more code\n'
                  'plus = src<M/A.hs:8:1-14>\n'
                  '  \\ xs ys -> xs\n')
        res = attribute(da, src)
        total, chars = res[0], res[1]
        want = {('M/A.hs', 'f'):
                len('f1 =  \\ x ->') + len('case x of { I# y -> y }'),
                ('M/A.hs', '+++'): len('plus =') + len('\\ xs ys -> xs'),
                ('M/A.hs', 'data T = T'): len('eqT =  \\ a b -> True'),
                # a note on an argument labels its own line alone
                ('M/A.hs', 'g'): len('r = foo  x'),
                ('(no note)', ''): len('h = 1') + len('tail'),
                # the comment's line 3 is no definition, so k has none
                ('M/A.hs', '?'): len('k =  k'),
                ('Elsewhere.hs', '?'): len('m =  2')}
        if dict(chars) != want:
            bad.append(f'attribution: {dict(chars)}')
        if total != sum(want.values()):
            bad.append(f'total {total} is not the sum of the parts')
        if attribute(da, src, with_notes=True)[0] <= total:
            bad.append('--with-notes counted no more than the code alone')
        if res[4].missing != {'Elsewhere.hs'}:
            bad.append(f'missing files: {res[4].missing}')
        got = compare_lines(res, attribute(db, src), 10)
        if not got or not any(l.endswith('M/A.hs f') and '+' in l for l in got):
            bad.append('comparison:\n  ' + '\n  '.join(got))
        plain = dump('plain.dump-simpl', 'f = \\ x -> x\n')
        if 'no source note' not in (usable(attribute(plain, src), plain) or ''):
            bad.append('a dump without notes not refused for having none')
        if main([plain, src]) != 2:
            bad.append('a dump without notes did not exit 2')
        if main([da, os.path.join(td, 'nowhere')]) != 2:
            bad.append('a source directory holding no noted file did not '
                       'exit 2')
        if main([da, src, '--top', '3']) != 0:
            bad.append('a usable dump did not exit 0')
    for b_ in bad:
        print('FAIL', b_)
    print('self-test', 'FAILED' if bad else 'passed')
    return 1 if bad else 0


def main(argv):
    if argv == ['--self-test']:
        return self_test()
    top, with_notes, rest = 40, False, []
    i = 0
    while i < len(argv):
        if argv[i] == '--top' and i + 1 < len(argv) and argv[i + 1].isdigit():
            top, i = int(argv[i + 1]), i + 2
        elif argv[i] == '--with-notes':
            with_notes, i = True, i + 1
        else:
            rest.append(argv[i])
            i += 1
    if len(rest) not in (2, 4) or any(r.startswith('--') for r in rest):
        print(__doc__.split('\n\n')[1], file=sys.stderr)
        return 2
    results = []
    for dump, srcdir in zip(rest[::2], rest[1::2]):
        if not os.path.isfile(dump):
            print(f'no file {dump}', file=sys.stderr)
            return 2
        r = attribute(dump, srcdir, with_notes)
        why = usable(r, dump)
        if why:
            print(why, file=sys.stderr)
            return 2
        results.append(r)
    lines = (single_lines(results[0], top) if len(results) == 1
             else compare_lines(*results, top))
    print('\n'.join(lines))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
