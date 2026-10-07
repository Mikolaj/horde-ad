#!/usr/bin/env python3
"""Find the code in optimised Core that runs unspecialised.

Usage: python3 tools/spec-audit.py DUMPS [--module SUBSTRING]
                                   [--ignore REGEX]...
       python3 tools/spec-audit.py --self-test

DUMPS is a dump tree, a build directory or a `-dumpdir` tree, whose modules
were compiled with `--ghc-options="-ddump-simpl -ddump-to-file
-dsuppress-uniques"` (tools/core-diff.py says how to keep two builds apart).
Without `-dsuppress-all` a callee keeps its module, which is what tells a
library's function from the client's own. Two lists are printed:

- calls that hand a function an instance dictionary of a class whose methods
  do the work --- `Vector`, `Unbox`, `Storable`, `Prim`, `Num` and the other
  numeric classes, `Eq`, `Ord`, `Enum`, `Bits`, `NFData`, `IsList` --- such
  as `Data.Array.Internal.DynamicU.$wscalar $fUnboxDouble`: a function GHC
  did not specialise, given the instance at run time. Grouped by module,
  callee and dictionary, with the count and the line of the first;
- bindings that take a dictionary as a lambda argument, a `$d...` or an
  `irred`, which is how a type-family constraint such as orthotope's
  `VecElem v a` prints: code polymorphic at run time. A library's own
  originals take them by design, so read this list over the clients
  (`--module`).

The callee is a guess, and each finding is read in the dump before anything
is done about it. It is the token before the dictionary on its line, its
qualifiers, type applications and other dictionaries passed over; for a
dictionary that opens its line, the last token of the nearest line above
that is indented less, the head of the application the dictionary is an
argument of. Where that token is a keyword, `=`, `->` or an opening
parenthesis, the `$f` name heads its own application, `case $fNumSize2 r`,
called rather than handed over, and is no finding. `--ignore REGEX` drops the calls whose dictionary matches, `List` for
the `Eq [Int]` comparisons of shapes, say; dictionaries that feed error
messages and the test harness are the reader's to set aside. A lambda whose
binders run onto a second line is not seen.

This is the audit of docs/perf-checklist.md's S1. Prove it on a known
positive before trusting its silence anywhere: a module built
`-fno-specialise` must be flagged.

Exit 0 when nothing was found, 1 when something was, 2 when the audit did
not happen: no `.dump-simpl` file under DUMPS, or a SUBSTRING no module's
path contains.
"""

import collections
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dumps  # noqa: E402

CLASSES = ('Vector|MVector|Unbox|Storable|Prim|Num|Fractional|Floating|'
           'RealFrac|RealFloat|Real|Integral|Eq|Ord|Enum|Bits|NFData|IsList')
DICT = re.compile(r'\$f(?:' + CLASSES + r')[A-Z][A-Za-z0-9_]*')
NAME = re.compile(r"(?:[A-Z][\w']*\.)*(?:[$\w][\w$']*|[!#$%&*+./<=>?\\^|~:-]+)")
NOT_CALLEE = {'case', 'of', 'let', 'in', 'join', 'joinrec', 'letrec', 'jump',
              'forall', 'cast', '__DEFAULT', 'type', 'ww', 'wild',
              '->', '=', '\\', '::', '.', '|'}
# A name's package and module qualifiers, `vector-0.13.2.0-28fe:Data.Vector.`.
QUAL = r"(?:[\w.'-]+:)?(?:[A-Z][\w']*\.)*"
LAMBDA = re.compile(r'\\\s((?:[^-]|-(?!>))*?)->')
LAMBDA_DICT = re.compile(r"(?<![\w$'])(\$d(?!IP)[A-Za-z0-9_]+|irred[0-9]*)"
                         r"(?![\w$'])")


def bare(prefix):
    """A line's text before a dictionary, its type applications, other
    dictionaries and literals removed."""
    prefix = re.sub(r'@\([^()]*\)', ' ', prefix)
    prefix = re.sub(r'@\S+', ' ', prefix)
    prefix = re.sub(QUAL + r'\$[fd][A-Za-z0-9_$]*', ' ', prefix)
    return re.sub(r'"[^"]*"|\b\d[\w.#]*', ' ', prefix)


def indent(line):
    return len(line) - len(line.lstrip(' '))


def callee(lines, i, col):
    """The function the dictionary at line i, column col is handed to, or
    None where the dictionary heads its own application, `case $fNumSize2 r`,
    being called rather than handed over: the token before it decides."""
    prefix = bare(re.sub(QUAL + '$', '', lines[i][:col]))
    if not prefix.strip():
        k = indent(lines[i])
        for j in range(i - 1, -1, -1):
            if lines[j].strip() and indent(lines[j]) < k:
                prefix = bare(lines[j])
                break
        else:
            return '?'
    if prefix.rstrip().endswith('('):
        return None
    names = NAME.findall(prefix)
    if not names or names[-1] in NOT_CALLEE:
        return None
    return names[-1]


def audit(txt, ignore):
    """(Counter of (callee, dictionary), {key: first line}, Counter of
    (binding, argument), {key: first line}) of one dump."""
    calls, lams = collections.Counter(), collections.Counter()
    first_call, first_lam = {}, {}
    lines = txt.split('\n')
    cur = None
    for i, line in enumerate(lines):
        if (line and not line[0].isspace() and not line.startswith(
                ('Rec {', 'end Rec', '--', '====', 'Result size'))):
            cur = line.split()[0]
        for m in DICT.finditer(line):
            if m.start() == 0 or line[m.end():].startswith('$c'):
                continue
            if any(re.search(r, m.group(0)) for r in ignore):
                continue
            c = callee(lines, i, m.start())
            if c is None:
                continue
            key = (c, m.group(0))
            calls[key] += 1
            first_call.setdefault(key, i + 1)
        for mm in LAMBDA.finditer(line):
            for a in LAMBDA_DICT.findall(mm.group(1)):
                key = (cur or '?', re.sub(r'[0-9]+$', '', a))
                lams[key] += 1
                first_lam.setdefault(key, i + 1)
    return calls, first_call, lams, first_lam


def report(root, sub, ignore):
    """The lines of both lists, the number of findings, and the number of
    modules read."""
    call_lines, lam_lines, found, read = [], [], 0, 0
    for p, key in dumps.walk(root, '.dump-simpl'):
        if sub is not None and sub not in key:
            continue
        read += 1
        calls, fc, lams, fl = audit(dumps.read_text(p), ignore)
        for (c, d), n in sorted(calls.items()):
            call_lines.append(f'  {key}  {c}  {d}: {n}, line {fc[(c, d)]}')
        for (b, a), n in sorted(lams.items()):
            lam_lines.append(f'  {key}  {b}  {a}: {n}, line {fl[(b, a)]}')
        found += len(calls) + len(lams)
    lines = (['== calls handed an instance dictionary '
              '(module, callee, dictionary: count, first line)'] + call_lines
             + ['== bindings taking a dictionary '
                '(module, binding, argument: count, first line)'] + lam_lines)
    return lines, found, read


def self_test():
    """A client dump with a worker given an instance at run time, calls
    whose dictionary opens a line, under a case alternative, under a case
    scrutinee and package-qualified, a shape comparison to ignore, an
    instance method and a `$f` binding in head position that are no calls,
    and two bindings polymorphic at run time; a library dump with its own original;
    and a client dump with nothing to find."""
    import tempfile
    head = ('\n==================== Tidy Core ====================\n'
            'Result size of Tidy Core\n  = {terms: 9, types: 1}\n\n')
    client = head + (
        'foo = \\ (x :: Double) -> Lib.$wscalar @Double $fUnboxDouble x\n\n'
        'qux\n'
        '  = \\ (x :: Double) ->\n'
        '      case x of {\n'
        '        __DEFAULT ->\n'
        '          Lib.k\n'
        '            @Double\n'
        '            $fOrdDouble\n'
        '            x\n'
        '      }\n\n'
        'baz = GHC.Classes.== @[Int] $fEqList_ a b\n\n'
        'meth = GHC.Base.foldr GHC.Float.$fNumDouble_$c+ 0.0## xs\n\n'
        'poly = \\ (@a) ($dNum :: Num a) (y :: a) -> + @a $dNum y y\n\n'
        'fam = \\ (@v) (irred :: VecElem v Double) -> Lib.h @v irred\n'
        '\nquux\n  = \\ eta ->\n'
        '      case Data.Array.Internal.DynamicU.$wscalar\n'
        '             vector-0.13.2.0-28fe:Data.Vector.Unboxed.Base.'
        '$fUnboxDouble eta\n'
        '      of\n      { __DEFAULT -> eta }\n\n'
        'size = case vector-0.13.2.0-28fe:Data.Vector.Fusion.Bundle.Size.'
        '$fNumSize2 r of\n\n'
        'pkg\n  = Lib.$windex\n'
        '      ghc-internal:GHC.Internal.Foreign.Storable.$fStorableDouble\n'
        '      ww\n')
    lib = head + 'Lib.h = \\ (@v) ($dUnbox :: Unbox v) -> Lib.g @v $dUnbox\n'
    clean = head + 'ok = \\ (x :: Double) -> GHC.Prim.+## x x\n'
    bad = []
    with tempfile.TemporaryDirectory() as td:
        for rel, text in (('A/build/src/Client.dump-simpl', client),
                          ('A/build/src/Lib.dump-simpl', lib),
                          ('B/build/src/Clean.dump-simpl', clean)):
            p = os.path.join(td, rel)
            os.makedirs(os.path.dirname(p), exist_ok=True)
            with open(p, 'w') as fh:
                fh.write(text)
        A, B = os.path.join(td, 'A'), os.path.join(td, 'B')
        got, found, read = report(A, 'Client', ['List'])
        want = ['== calls handed an instance dictionary '
                '(module, callee, dictionary: count, first line)',
                '  src/Client  Data.Array.Internal.DynamicU.$wscalar  '
                '$fUnboxDouble: 1, line 29',
                '  src/Client  Lib.$windex  $fStorableDouble: 1, line 37',
                '  src/Client  Lib.$wscalar  $fUnboxDouble: 1, line 6',
                '  src/Client  Lib.k  $fOrdDouble: 1, line 14',
                '== bindings taking a dictionary '
                '(module, binding, argument: count, first line)',
                '  src/Client  fam  irred: 1, line 24',
                '  src/Client  poly  $dNum: 1, line 22']
        if got != want or found != 6 or read != 1:
            bad.append(f'client report ({found} found, {read} read):\n  '
                       + '\n  '.join(got))
        got, _, _ = report(A, 'Client', [])
        if not any('GHC.Classes.==  $fEqList_' in x for x in got):
            bad.append('the shape comparison not reported without --ignore')
        got, _, _ = report(A, None, ['List'])
        if not any('src/Lib  Lib.h  $dUnbox' in x for x in got):
            bad.append("the library's own original not reported without "
                       "--module")
        for argv, want, why in (
                ([A, '--module', 'Client'], 1, 'findings'),
                ([B], 0, 'a clean tree'),
                ([os.path.join(td, 'empty')], 2, 'a tree without dumps'),
                ([A, '--module', 'NoSuch'], 2, 'a --module matching nothing')):
            os.makedirs(os.path.join(td, 'empty'), exist_ok=True)
            if main(argv) != want:
                bad.append(f'{why} did not exit {want}')
    for b in bad:
        print('FAIL', b)
    print('self-test', 'FAILED' if bad else 'passed')
    return 1 if bad else 0


def main(argv):
    if argv == ['--self-test']:
        return self_test()
    sub, ignore, rest = None, [], []
    i = 0
    while i < len(argv):
        if argv[i] in ('--module', '--ignore') and i + 1 < len(argv):
            if argv[i] == '--module':
                sub = argv[i + 1]
            else:
                ignore.append(argv[i + 1])
            i += 2
        else:
            rest.append(argv[i])
            i += 1
    if len(rest) != 1 or rest[0].startswith('--'):
        print(__doc__.split('\n\n')[1], file=sys.stderr)
        return 2
    lines, found, read = report(rest[0], sub, ignore)
    if not dumps.walk(rest[0], '.dump-simpl'):
        print(f'no .dump-simpl file under {rest[0]}; was it built with '
              '-ddump-simpl -ddump-to-file?', file=sys.stderr)
        return 2
    if not read:
        print(f"no module's path contains {sub}", file=sys.stderr)
        return 2
    print('\n'.join(lines))
    return 1 if found else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
