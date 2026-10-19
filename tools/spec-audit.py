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
  `VecElem v a` prints: code polymorphic at run time. Each argument
  is printed with the type the dump gives it, so that a constraint whose
  class has no methods, orthotope's `VecElem [] a` say, reads as costing
  nothing. A library's own originals take them by design, so read this
  list over the clients (`--module`).

A `$f` name is a dictionary unless the tree's dump of the module
qualifying it gives it a type not headed by its class: GHC names a binding
it floats out of a dictionary after it, `$fStorableE5 :: Int`. A class
whose name begins with a listed one's, as horde-ad's `EqH` or ox-arrays'
`NumElt`, counts as one of them, and a specialised dictionary,
`$fEqList_$s$fEqList1`, as one dictionary. A name
of a module outside the tree, base's say, or qualified by an import's
alias, is taken for a dictionary. A `$d` argument of an unboxed type,
a worker's field of a dictionary, is not one.

The callee is a guess, and each finding is read in the dump before anything
is done about it. It is the token before the dictionary on its line, its
qualifiers, type applications and other dictionaries passed over; for a
dictionary that opens its line, the last token of the nearest line above
that is indented less, the head of the application the dictionary is an
argument of. Where that token is a keyword, `=`, `->` or an opening
parenthesis, the `$f` name heads its own application, `case $fNumSize2 r`,
called rather than handed over, and is no finding; where it is
a constructor, `C:Elem` building a dictionary or `:%`, the dictionary
is stored and runs nothing, and is no finding either. `--ignore REGEX`
drops the calls whose dictionary matches, `List` for the `Eq [Int]`
comparisons of shapes, say; dictionaries that feed error messages and
the test harness are the reader's to set aside.

This is the audit of docs/perf-checklist.md's S1. Prove it on a known
positive before trusting its silence anywhere: a module built
`-fno-specialise` must be flagged.

Exit 0 when nothing was found, 1 when something was, 2 when the audit did
not happen: no `.dump-simpl` file under DUMPS, a SUBSTRING no module's
path contains, or an `--ignore` that is no regex.
"""

import bisect
import collections
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dumps  # noqa: E402

CLASSES = ('Vector|MVector|Unbox|Storable|Prim|Num|Fractional|Floating|'
           'RealFrac|RealFloat|Real|Integral|Eq|Ord|Enum|Bits|NFData|IsList')
# A whole name, behind its qualifiers, to an instance method's $c: without
# the boundary and the $, $fEqList_$s$fEqList1 read as two (spec-audit-09).
DICT = re.compile(r"(?<![\w$'])\$f(" + CLASSES + r")[A-Z](?:(?!\$c)[\w$'])*")
OPS = r"[!#$%&*+./<=>?\\^|~:-]+"
# A class's data constructor, an operator's instance method, an identifier
# with its trailing #s, or an operator, each behind its qualifiers.
NAME = re.compile(r"(?:[A-Z][\w']*\.)*(?:C:[\w']+|[$\w][\w$']*\$c" + OPS
                  + r"|[$\w][\w$']*#*|" + OPS + ")")
NOT_CALLEE = {'case', 'of', 'let', 'in', 'join', 'joinrec', 'letrec', 'jump',
              'forall', 'cast', '__DEFAULT', 'type', 'ww', 'wild',
              '->', '=', '\\', '::', '.', '|'}
# A name's package and module qualifiers, `vector-0.13.2.0-28fe:Data.Vector.`.
QUAL = r"(?:[\w.'-]+:)?(?:[A-Z][\w']*\.)*"
# A dictionary or a dictionary variable, but not an instance method.
OTHER_DICT = re.compile(QUAL + r"\$[fd](?:(?!\$c)[\w$])*"
                        r"(?![\w$'!#%&*+./<=>?\\^|~:-])")
LAMBDA_DICT = re.compile(r"\$d(?!IP)[A-Za-z0-9_]+|irred[0-9]*")
# A top-level `$f` binding's name at column 0, and its type where the
# signature shares the line.
SIG = re.compile(r"(" + QUAL + r"\$f[\w$']*)(?:\s+::\s+(.*))?$")
FORALL = dumps.FORALL
HEAD = re.compile(r"[(\s]*" + QUAL + r"([\w']+#*)")
# A lambda's binder: its parentheses, or a bare name.
PAREN = re.compile(r'[()]')
BARE = re.compile(r"@?[\w$'][\w$'#]*")


def bare(prefix):
    """A line's text before a dictionary, its type applications, other
    dictionaries and literals removed."""
    prefix = re.sub(r'@\([^()]*\)', ' ', prefix)
    prefix = re.sub(r'@\S+', ' ', prefix)
    prefix = OTHER_DICT.sub(' ', prefix)
    return re.sub(r'"[^"]*"|\b\d[\w.#]*', ' ', prefix)


def signatures(lines):
    """{name: type} of the `$f` bindings a dump defines at top level, by the
    name its module prints them with, the type's lines joined."""
    sigs = {}
    for i, line in enumerate(lines):
        if '$f' not in line or line[:1].isspace():
            continue
        m = SIG.match(line)
        if not m:
            continue
        if m.group(2) is not None:
            parts, j = [m.group(2)], i + 1
        elif i + 1 < len(lines) and lines[i + 1].lstrip().startswith(':: '):
            parts, j = [lines[i + 1].lstrip()[3:]], i + 2
        else:
            continue
        while j < len(lines) and lines[j][:1].isspace() and lines[j].strip():
            parts.append(lines[j].strip())
            j += 1
        sigs[m.group(1)] = ' '.join(parts)
    return sigs


def type_head(ty):
    """The head of a type, behind its foralls and its context, or None."""
    m = FORALL.match(ty)
    while m:
        ty = ty[m.end():]
        m = FORALL.match(ty)
    m = HEAD.match(ty.rsplit('=>', 1)[-1])
    return m.group(1) if m else None


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
    # A constructor stores the dictionary and runs nothing with it.
    if re.sub(r"^(?:[A-Z][\w']*\.)*", '', names[-1]).startswith((':', 'C:')):
        return None
    return names[-1]


def binders(txt, k):
    """[(name, type or None)] of the lambda whose binders start at offset k,
    read to the `->` outside them, whatever lines they run onto."""
    out = []
    while True:
        while k < len(txt) and txt[k] in ' \n':
            k += 1
        if k >= len(txt) or txt.startswith('->', k):
            return out
        if txt[k] == '(':
            depth = 0
            for p in PAREN.finditer(txt, k):
                depth += 1 if p.group() == '(' else -1
                if depth == 0:
                    break
            else:
                return out
            name, sep, ty = txt[k + 1:p.start()].partition(' :: ')
            out.append((name.split()[0] if name.split() else '',
                        ' '.join(ty.split()) if sep else None))
            k = p.end()
        else:
            m = BARE.match(txt, k)
            if not m:
                return out
            out.append((m.group(), None))
            k = m.end()


def audit(txt, ignore, resolve=lambda module: None):
    """(Counter of (callee, dictionary), {key: first line}, Counter of
    (binding, argument, its type), {key: first line}) of one dump. resolve
    gives the signatures of another module of the tree, by its name, or
    None."""
    calls, lams = collections.Counter(), collections.Counter()
    first_call, first_lam = {}, {}
    lines = txt.split('\n')
    sigs = signatures(lines)
    owner, cur = [], None
    for i, line in enumerate(lines):
        if (line and not line[0].isspace() and not line.startswith(
                ('Rec {', 'end Rec', '--', '====', 'Result size'))):
            cur = line.split()[0]
        owner.append(cur)
        for m in DICT.finditer(line):
            qual = re.search(QUAL + '$', line[:m.start()]).group()
            # The binding's own name, in its signature or its definition.
            if (re.fullmatch(QUAL, line[:m.start()])
                    or line[m.end():].startswith('$c')):
                continue
            if any(re.search(r, m.group(0)) for r in ignore):
                continue
            # A binding GHC floated out of a dictionary takes its name.
            ty = sigs.get(qual + m.group(0))
            module = qual.split(':')[-1]
            if ty is None and qual:
                ty = (resolve(module[:-1]) or {}).get(module + m.group(0))
            # Its class is its type's head, which may extend the listed one,
            # NumScalar Num's (spec-audit-08), and which its name begins
            # with; a floated binding's type is headed otherwise.
            head = type_head(ty) or '' if ty is not None else None
            if head is not None and not (head.startswith(m.group(1))
                                         and m.group(0)[2:].startswith(head)):
                continue
            c = callee(lines, i, m.start())
            if c is None:
                continue
            key = (c, m.group(0))
            calls[key] += 1
            first_call.setdefault(key, i + 1)
    starts = [0]
    for line in lines:
        starts.append(starts[-1] + len(line) + 1)
    for m in re.finditer(r'\\ ', txt):
        i = bisect.bisect_right(starts, m.start()) - 1
        for a, ty in binders(txt, m.end()):
            if not LAMBDA_DICT.fullmatch(a):
                continue
            # An unboxed field a worker took out of a dictionary.
            if ty is not None and (type_head(ty) or '').endswith('#'):
                continue
            key = (owner[i] or '?', re.sub(r'[0-9]+$', '', a), ty)
            lams[key] += 1
            first_lam.setdefault(key, i + 1)
    return calls, first_call, lams, first_lam


def report(root, sub, ignore):
    """The lines of both lists, the number of findings, and the number of
    modules read."""
    call_lines, lam_lines, found, read = [], [], 0, 0
    tree, cache = dumps.walk(root, '.dump-simpl'), {}

    def resolve(module):
        """The signatures of a module of the tree other than key's, or None;
        where two components hold it, key's own, since flags that differ
        between them can number the floated bindings differently."""
        rel = module.replace('.', '/')
        hits = [(len(os.path.commonprefix([q, key])), p) for p, q in tree
                if (q == rel or q.endswith('/' + rel)) and q != key]
        if not hits:
            return None
        p = max(hits)[1]
        if p not in cache:
            cache[p] = signatures(dumps.core(dumps.read_text(p)).split('\n'))
        return cache[p]

    for p, key in tree:
        if sub is not None and sub not in key:
            continue
        read += 1
        # The rules section cut: a rule's left-hand side was counted as a
        # call handed a dictionary (spec-audit-11).
        calls, fc, lams, fl = audit(dumps.core(dumps.read_text(p)), ignore,
                                    resolve)
        for (c, d), n in sorted(calls.items()):
            call_lines.append(f'  {key}  {c}  {d}: {n}, line {fc[(c, d)]}')
        for (b, a, t), n in sorted(lams.items(), key=lambda kv: (
                kv[0][0], kv[0][1], kv[0][2] or '')):
            ty = '' if t is None else ' :: ' + t
            lam_lines.append(f'  {key}  {b}  {a}{ty}: {n}, '
                             f'line {fl[(b, a, t)]}')
        found += len(calls) + len(lams)
    lines = (['== calls handed an instance dictionary '
              '(module, callee, dictionary: count, first line)'] + call_lines
             + ['== bindings taking a dictionary '
                '(module, binding, argument: count, first line)'] + lam_lines)
    return lines, found, read


def self_test():
    """A client dump with a worker given an instance at run time, calls whose
    dictionary opens a line, under a case alternative, under a case scrutinee
    and package-qualified, a shape comparison to ignore, an instance method and
    a `$f` binding in head position that are no calls, and two bindings
    polymorphic at run time; then a dictionary of its own and one of the
    library's, bindings floated out of dictionaries, here and in the library,
    two instance methods and a name ending in # as callees, two constructors,
    an unboxed `$d` binder and binders running onto further lines, a
    dictionary of a class extending a listed one's and a specialised
    dictionary; a library dump with its own original; a component whose
    floated binding shares its name with another component's dictionary; and
    a client dump with nothing to find."""
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
        '      ww\n\n'
        'Client.$fStorableE\n  :: forall a.\n     Num a =>\n'
        '     Storable (E a)\n'
        'Client.$fStorableE = Client.mkE\n\n'
        'Client.$fStorableE5 :: Int\n'
        'Client.$fStorableE5 = GHC.Types.I# 1#\n\n'
        'real = \\ (x :: E) -> Lib.peek Client.$fStorableE x\n\n'
        'aux = \\ (x :: Int) -> Lib.g Client.$fStorableE5 '
        '(Lib.h Lib.$fNumT3 x)\n\n'
        'eqw = GHC.Classes.$fEqList_$c== @Word8 GHC.Word.$fEqWord8 a b\n\n'
        'cmp = GHC.Classes.$fOrdList_$ccompare @Int '
        'GHC.Classes.$fOrdInt a b\n\n'
        'ix = Data.Primitive.Types.indexByteArray# @Double '
        'Data.Primitive.Types.$fPrimDouble ba i\n\n'
        'r = GHC.Real.:% @Integer GHC.Real.$fEnumRatio1 x\n\n'
        'Client.$fElemInt :: Elem Int\n'
        'Client.$fElemInt\n  = Client.C:Elem\n      @Int\n'
        '      GHC.Real.$fIntegralInt\n\n'
        't = \\ ($dKnownNat :: GHC.Prim.ByteArray#) -> '
        'Lib.rotate $dKnownNat\n\n'
        'multi\n  = \\ (@a)\n      (f :: (a -> a) -> a)\n'
        '      ($dEq :: Eq a)\n      (y :: a) ->\n      f y\n\n'
        'srt = Lib.sort Lib.$fOrdT xs\n\n'
        'Client.$fNumScalarDouble :: NumScalar Double\n'
        'Client.$fNumScalarDouble = Client.mk\n\n'
        'num = \\ (x :: Double) -> Lib.go @Double Client.$fNumScalarDouble x\n\n'
        'spc = Lib.sort GHC.Classes.$fEqList_$s$fEqList1 xs\n')
    lib = head + ('Lib.h = \\ (@v) ($dUnbox :: Unbox v) -> '
                  'Lib.g @v $dUnbox\n\n'
                  'Lib.$fNumT3\n  :: Int\nLib.$fNumT3 = GHC.Types.I# 3#\n\n'
                  'Lib.$fOrdT :: forall a. Ord (T a)\nLib.$fOrdT = Lib.mk\n')
    # The component's own Shared floated a binding where the other's has
    # a dictionary of the same name.
    comp = head + 'c = Shared.k Shared.$fNumT1\n'
    shared_b = head + 'Shared.$fNumT1 :: Num T\nShared.$fNumT1 = Shared.mk\n'
    shared_z = head + ('Shared.$fNumT1 :: Int\n'
                       'Shared.$fNumT1 = GHC.Types.I# 1#\n')
    clean = head + 'ok = \\ (x :: Double) -> GHC.Prim.+## x x\n'
    bad = []
    with tempfile.TemporaryDirectory() as td:
        for rel, text in (('A/build/src/Client.dump-simpl', client),
                          ('A/build/src/Lib.dump-simpl', lib),
                          ('C/build/b/b-tmp/Shared.dump-simpl', shared_b),
                          ('C/build/z/z-tmp/Shared.dump-simpl', shared_z),
                          ('C/build/z/z-tmp/Comp.dump-simpl', comp),
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
                '  src/Client  Data.Primitive.Types.indexByteArray#  '
                '$fPrimDouble: 1, line 57',
                '  src/Client  GHC.Classes.$fEqList_$c==  $fEqWord8: 1, '
                'line 53',
                '  src/Client  GHC.Classes.$fOrdList_$ccompare  $fOrdInt: 1, '
                'line 55',
                '  src/Client  Lib.$windex  $fStorableDouble: 1, line 37',
                '  src/Client  Lib.$wscalar  $fUnboxDouble: 1, line 6',
                '  src/Client  Lib.go  $fNumScalarDouble: 1, line 81',
                '  src/Client  Lib.k  $fOrdDouble: 1, line 14',
                '  src/Client  Lib.peek  $fStorableE: 1, line 49',
                '  src/Client  Lib.sort  $fOrdT: 1, line 76',
                '== bindings taking a dictionary '
                '(module, binding, argument: count, first line)',
                '  src/Client  fam  irred :: VecElem v Double: 1, line 24',
                '  src/Client  multi  $dEq :: Eq a: 1, line 70',
                '  src/Client  poly  $dNum :: Num a: 1, line 22']
        if got != want or found != 13 or read != 1:
            bad.append(f'client report ({found} found, {read} read):\n  '
                       + '\n  '.join(got))
        got, found, _ = report(os.path.join(td, 'C'), 'Comp', [])
        if found:
            bad.append("a floated binding resolved in another component:\n  "
                       + '\n  '.join(got))
        got, _, _ = report(A, 'Client', [])
        if not any('GHC.Classes.==  $fEqList_' in x for x in got):
            bad.append('the shape comparison not reported without --ignore')
        if [x for x in got if 'Lib.sort  $fEqList' in x] != [
                '  src/Client  Lib.sort  $fEqList_$s$fEqList1: 1, line 83']:
            bad.append('the specialised dictionary not reported as one:\n  '
                       + '\n  '.join(got))
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
    # An --ignore that is no regex was a traceback and exit 1 (spec-audit-10).
    for r in ignore:
        try:
            re.compile(r)
        except re.error as e:
            print(f'--ignore {r!r} is no regex: {e}', file=sys.stderr)
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
