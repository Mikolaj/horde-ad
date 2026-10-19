#!/usr/bin/env python3
"""List the arguments optimised Core takes apart though they are passed boxed.

Usage: python3 tools/box-audit.py DUMPS [--module SUBSTRING] [--sum TYPE]...
                                  [--ignore REGEX]...
       python3 tools/box-audit.py --self-test

DUMPS is a dump tree, a build directory or a `-dumpdir` tree, whose modules
were compiled with `-ddump-simpl -ddump-to-file -dsuppress-idinfo`, with or
without `-dsuppress-uniques` but not with `-dsuppress-all`, which drops
the binders' types this reads; `--module` keeps the modules
whose dump path contains SUBSTRING, and `--ignore` passes over the bindings
whose name REGEX matches, a client's own as the specialisation benchmark's
`lvl` rows. For each top-level binding of Tidy Core,
each lambda-bound argument of a lifted type that is not a function, a type
variable or a dictionary, and that the body scrutinises (`case x of`, a
newtype's `cast` included), is printed: the module, the binding, the
argument's position and name, `used` where the box itself is used besides,
the argument or its case binder occurring elsewhere in the body, and
`unused` where only its fields are, and the type. The final Core is the
evidence, not the demand signature: a function taking six products apart,
small enough to inline, got no worker, all six passed boxed, where its
signature called four of them unboxed; NOINLINE, its worker took the last
two boxed at `-fmax-worker-args`'s default of 10. A wrapper, whose body
calls its own worker (`$w` and its name), is passed over: taking boxes apart
is its job. An argument of a sum type --- lists, `Maybe`, `Either`, `Bool`,
`Ordering`, `Integer`, `Natural`, and each `--sum` type, a synonym of one
say --- is printed as `sum`, GHC HEAD passing no sum unboxed
(docs/perf-checklist.md, A3). Where the module was also dumped with
`-ddump-cpr-signatures`, each binding returning such a lifted type without
CPR is printed as `res`, its result returned boxed, or as `sum` where the type
is a sum.

`unused` is the lost unboxing: `-fmax-worker-args`, a function small enough
to inline and so given no worker, boxed where a call does not inline it, or
a lazy argument taken apart under a branch (L1); `used` is most often the
deliberate box, stored or returned, or the one an out-of-line callee takes
boxed; each is read in the Core before anything is done about it
(docs/perf-checklist.md, B1).

Exit 0 when nothing was found, 1 when something was, 2 when DUMPS holds no
`.dump-simpl`, no module's path contains SUBSTRING, a dump carries IdInfo,
no binding carries the types this reads, or an `--ignore` is no regex.
"""

import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dumps  # noqa: E402

SUMS = {'[]', 'Maybe', 'Either', 'Bool', 'Ordering', 'Integer', 'Natural'}
NAME = r"[\w$'.]+"


def split_top(s, sep):
    """s split at sep where no bracket is open."""
    parts, depth, cur, i = [], 0, [], 0
    while i < len(s):
        c = s[i]
        if c in '([':
            depth += 1
        elif c in ')]':
            depth -= 1
        if depth == 0 and s.startswith(sep, i):
            parts.append(''.join(cur).strip())
            cur, i = [], i + len(sep)
            continue
        cur.append(c)
        i += 1
    parts.append(''.join(cur).strip())
    return parts


def strip_parens(ty):
    ty = ty.strip()
    while ty.startswith('(') and ty.endswith(')') and \
            split_top(ty[1:-1], ',') == [ty[1:-1].strip()] and \
            len(split_top(ty[1:-1], '->')) == 1:
        ty = ty[1:-1].strip()
    return ty


def head(ty):
    ty = strip_parens(ty)
    if ty.startswith('['):
        return '[]'
    return ty.split()[0].rsplit('.', 1)[-1] if ty else ''


def kind(ty, sums):
    """'box', 'sum', or None for what is not a box to judge."""
    ty = strip_parens(ty)
    if not ty or len(split_top(ty, '->')) > 1 or len(split_top(ty, '=>')) > 1 \
            or ty.startswith('forall') or ty.startswith('(#'):
        return None
    h = head(ty)
    if h.endswith('#') or re.match(r"^[a-z_]", h):
        return None
    short = {t.rsplit('.', 1)[-1] for t in sums}
    if h in sums or h in short or ty in sums:
        return 'sum'
    return 'box'


def result_type(ty):
    """The result of a Core type, past its foralls, constraints and arrows."""
    ty = re.sub(r'^(forall\b[^.]*\.\s*)+', '', ty.strip())
    parts = split_top(ty, '=>')
    ty = re.sub(r'^(forall\b[^.]*\.\s*)+', '', parts[-1])
    return split_top(ty, '->')[-1]


def bindings(core):
    """[(name, type, binders, body)] of Tidy Core's top-level bindings,
    binders [(name, type)] of the outer lambda's value arguments."""
    out = []
    for block in re.split(r'\n(?=-- RHS size)', core):
        lines = block.split('\n')
        i = 0
        while i < len(lines) and not re.match(r'^' + NAME + r'(\s|$)', lines[i]):
            i += 1
        if i == len(lines):
            continue
        m = re.match(r'^(' + NAME + r')(?:\s*::\s*(.*))?$', lines[i])
        if not m:
            continue
        name, ty, j = m.group(1), m.group(2), i + 1
        if ty is None:
            if j < len(lines) and re.match(r'^\s+::', lines[j]):
                ty, j = re.sub(r'^\s+::\s*', '', lines[j]), j + 1
            else:
                continue
        while j < len(lines) and lines[j].startswith(' ') and \
                not re.match(r'^\s+=', lines[j]):
            ty += ' ' + lines[j].strip()
            j += 1
        while j < len(lines) and not re.match(r'^' + re.escape(name) + r'(\s|$)', lines[j]):
            j += 1
        rhs = '\n'.join(lines[j:])
        m = re.match(re.escape(name) + r'\s*=\s*\\\s*', rhs)
        binders, body = [], rhs
        if m:
            k = m.end()
            while True:
                while k < len(rhs) and rhs[k] in ' \n':
                    k += 1
                if rhs.startswith('->', k):
                    body = rhs[k + 2:]
                    break
                if rhs.startswith('(', k):
                    depth, e = 0, k
                    while e < len(rhs):
                        depth += rhs[e] == '('
                        depth -= rhs[e] == ')'
                        if depth == 0:
                            break
                        e += 1
                    g = re.match(r"\(\s*([\w$']+)\s*::\s*(.*)\)$", ' '.join(rhs[k:e + 1].split()))
                    if g:
                        binders.append((g.group(1), g.group(2)))
                    k = e + 1
                    continue
                g = re.match(r"@?[\w$']+", rhs[k:])
                if not g:
                    break
                k += g.end()
        out.append((name, ty, binders, body))
    return out


def token(name):
    return r"(?<![\w$'])" + re.escape(name) + r"(?![\w$'])"


def scrutinies(body, x):
    """The spans of body's `case x ... of` heads, a newtype's cast between
    them, and the case binders they name."""
    spans, cbs = [], []
    for m in re.finditer(r"\bcase\s+" + re.escape(x) + r"(?=\s)", body):
        k = m.end()
        while k < len(body) and body[k] in ' \n':
            k += 1
        if body.startswith('`cast`', k):
            k += len('`cast`')
            while k < len(body) and body[k] in ' \n':
                k += 1
            if not body.startswith('(', k):
                continue
            depth = 0
            while k < len(body):
                depth += body[k] == '('
                depth -= body[k] == ')'
                k += 1
                if depth == 0:
                    break
            while k < len(body) and body[k] in ' \n':
                k += 1
        g = re.match(r"of\s+(?:([\w$']+)\s+)?\{", body[k:])
        if not g:
            continue
        spans.append((m.start(), k + g.end()))
        if g.group(1):
            cbs.append(g.group(1))
    return spans, cbs


def cpr_signatures(text):
    """name -> CPR signature, from the last section of a CPR dump."""
    out = {}
    section = re.split(r'\n=+ [^\n]* =+\n', text)[-1]
    for line in section.split('\n'):
        m = re.match(r'^(' + NAME + r'):\s?(.*)$', line)
        if m and not re.match(r'^\d{4}-', line):
            out[m.group(1).rsplit('.', 1)[-1]] = m.group(2).strip()
    return out


def findings(core, sums, cpr=None, ignore=()):
    out, typed = [], False
    for name, ty, binders, body in bindings(core):
        typed = typed or bool(binders)
        if any(re.search(r, name) for r in ignore):
            continue
        base = name.rsplit('.', 1)[-1] if re.match(r'^[A-Z]', name) else name
        if re.search(r"(?<![\w$'])(?:[\w.]*\.)?\$w" + re.escape(base) + r"(?![\w$'])", body):
            continue
        for pos, (b, bty) in enumerate(binders, 1):
            if b.startswith('$d') or b.startswith('irred'):
                continue
            kd = kind(bty, sums)
            if not kd:
                continue
            spans, binders_of = scrutinies(body, b)
            if not spans:
                continue
            rest = body
            for a, z in reversed(spans):
                rest = rest[:a] + ' ' + rest[z:]
            used = bool(re.search(token(b), rest)) or any(
                len(re.findall(token(cb), body)) > 1 for cb in binders_of)
            out.append((name, kd if kd == 'sum' else 'arg', pos, b,
                        'used' if used else 'unused', bty))
        if cpr is not None and binders:
            c = cpr.get(base)
            rt = result_type(ty)
            kd = kind(rt, sums)
            if c is not None and kd and not c.startswith('1'):
                out.append((name, 'res' if kd == 'box' else 'sum', 0, '-',
                            c or '-', rt))
    return out, typed


def report(root, sub, sums, ignore=()):
    lines, found, read, typed, info = [], 0, 0, False, None
    for path, key in dumps.walk(root, '.dump-simpl'):
        if sub is not None and sub not in path:
            continue
        read += 1
        core = dumps.core(dumps.read_text(path))
        if re.search(r'^\[GblId', core, re.M):
            info = info or path
            continue
        cpr = None
        cp = path[:-len('.dump-simpl')] + '.dump-cpr-signatures'
        if os.path.exists(cp):
            cpr = cpr_signatures(dumps.read_text(cp))
        fs, t = findings(core, sums, cpr, ignore)
        typed = typed or t
        for name, what, pos, b, used, ty in fs:
            lines.append(f'{key}\t{what}\t{name}\t{pos}\t{b}\t{used}\t{ty}')
            found += 1
    return lines, found, read, typed, info


def self_test():
    """Tidy Core of the probe that settled the design: wide, six products
    and no worker, small enough to inline; h2 and mx taking apart a box
    they also use; lz, a sum and a lazy argument taken apart under a
    branch; a wrapper. Besides, written for the test: a worker
    taking a vector apart through its case binder; a dictionary, an
    unboxed argument and a function argument; a newtype taken apart through
    a cast; a CAF defining a lambda of its own, whose binders are not the
    CAF's (box-audit-01); and a CPR dump without CPR for a product
    result."""
    import tempfile
    core = '''
-- RHS size: {terms: 48, types: 24, coercions: 0, joins: 0/0}
wide :: Pt -> Pt -> Pt -> Pt -> Pt -> Pt -> Int
wide
  = \\ (ds :: Pt)
      (ds1 :: Pt)
      (ds2 :: Pt)
      (ds3 :: Pt)
      (ds4 :: Pt)
      (ds5 :: Pt) ->
      case ds of { Pt bx bx1 ->
      case ds1 of { Pt bx2 bx3 ->
      case ds2 of { Pt bx4 bx5 ->
      case ds3 of { Pt bx6 bx7 ->
      case ds4 of { Pt bx8 bx9 ->
      case ds5 of { Pt bx10 bx11 ->
      GHC.Internal.Types.I# (GHC.Internal.Prim.+# bx bx11)
      }
      }
      }
      }
      }
      }

-- RHS size: {terms: 11, types: 7, coercions: 0, joins: 0/0}
h2 :: Pt -> (Int, [Pt])
h2
  = \\ (p :: Pt) ->
      case p of wild { Pt bx bx1 ->
      (GHC.Internal.Types.I# (GHC.Internal.Prim.+# bx bx1), store wild)
      }

-- RHS size: {terms: 13, types: 6, coercions: 0, joins: 0/0}
mx :: Int -> Maybe Int
mx
  = \\ (n :: Int) ->
      case n of wild { GHC.Internal.Types.I# x ->
      case GHC.Internal.Prim.># x 0# of {
        __DEFAULT -> GHC.Internal.Maybe.Nothing @Int;
        1# -> GHC.Internal.Maybe.Just @Int wild
      }
      }

-- RHS size: {terms: 14, types: 5, coercions: 0, joins: 0/0}
lz :: Bool -> Int -> Int
lz
  = \\ (c :: Bool) (x :: Int) ->
      case c of {
        False -> Q.lz1;
        True ->
          case x of { GHC.Internal.Types.I# x1 ->
          GHC.Internal.Types.I# (GHC.Internal.Prim.+# x1 1#)
          }
      }

-- RHS size: {terms: 9, types: 4, coercions: 0, joins: 0/0}
capt :: Int -> Double -> [Double]
capt
  = \\ (n :: Int) (d :: Double) ->
      case n of { GHC.Internal.Types.I# ww -> Q.$wcapt ww d }

-- RHS size: {terms: 20, types: 9, coercions: 0, joins: 0/0}
Client.$wrow
  :: Data.Vector.Vector Double
     -> GHC.Internal.Prim.Int#
     -> GHC.Internal.Prim.Double#
Client.$wrow
  = \\ (ww :: Data.Vector.Vector Double)
      (ww1 :: GHC.Internal.Prim.Int#) ->
      case ww of ww2 { Data.Vector.Vector ipv ipv1 ipv2 ->
      Client.$wsum ipv ipv1 ww2 ww1
      }

-- RHS size: {terms: 12, types: 8, coercions: 2, joins: 0/0}
poly
  :: forall a. Ord a => (a -> a) -> a -> GHC.Internal.Prim.Int# -> IS.Array a -> a
poly
  = \\ (@a)
      ($dOrd :: Ord a)
      (f :: a -> a)
      (y :: a)
      (k :: GHC.Internal.Prim.Int#)
      (arr :: IS.Array a) ->
      case arr
           `cast` (Data.Array.Internal.DynamicS.N:Array <a>_N
                   :: IS.Array a ~R# DG.Array V.Vector a)
      of
      { DG.A s bx ->
      case y of y1 { __DEFAULT -> f y1 }
      }

-- RHS size: {terms: 12, types: 6, coercions: 0, joins: 0/0}
caf :: Int
caf
  = let {
      go :: Pt -> Int
      go
        = \\ (p :: Pt) ->
            case p of { Pt bx bx1 -> GHC.Internal.Types.I# bx1 } } in
    go Q.pt0
'''
    cpr = '''==================== Cpr signatures ====================
2026-10-19 13:09:13.140235453 UTC

Q.h2: 1(1,)
Q.mx:
Q.lz: 1
Q.wide:
'''
    want = ['wide\targ\t1\tds\tunused\tPt',
            'wide\targ\t2\tds1\tunused\tPt',
            'wide\targ\t3\tds2\tunused\tPt',
            'wide\targ\t4\tds3\tunused\tPt',
            'wide\targ\t5\tds4\tunused\tPt',
            'wide\targ\t6\tds5\tunused\tPt',
            'h2\targ\t1\tp\tused\tPt',
            'mx\targ\t1\tn\tused\tInt',
            'lz\tsum\t1\tc\tunused\tBool',
            'lz\targ\t2\tx\tunused\tInt',
            'Client.$wrow\targ\t1\tww\tused\tData.Vector.Vector Double',
            'poly\targ\t5\tarr\tunused\tIS.Array a']
    want_cpr = want[:6] + ['wide\tres\t0\t-\t-\tInt'] + want[6:8] + \
        ['mx\tsum\t0\t-\t-\tMaybe Int'] + want[8:]
    bad = []
    got = ['\t'.join(map(str, f)) for f in findings(core, SUMS)[0]]
    if got != want:
        bad.append('findings:\n  ' + '\n  '.join(got))
    got = ['\t'.join(map(str, f)) for f in findings(core, SUMS, cpr_signatures(cpr))[0]]
    if got != want_cpr:
        bad.append('findings with CPR:\n  ' + '\n  '.join(got))
    if findings(core, SUMS | {'IS.Array'})[0][-1][1] != 'sum':
        bad.append('a --sum type not printed as a sum')
    if [f[0] for f in findings(core, SUMS, None, [r'^wide$', r'\$w'])[0]] != \
            ['h2', 'mx', 'lz', 'lz', 'poly']:
        bad.append('--ignore did not pass over the bindings it matches')
    with tempfile.TemporaryDirectory() as td, tempfile.TemporaryDirectory() as ti:
        with open(os.path.join(ti, 'M.dump-simpl'), 'w') as fh:
            fh.write('-- RHS size: {terms: 6}\nf :: Pt -> Int\n'
                     '[GblId, Arity=1, Unf=OtherCon []]\n'
                     'f = \\ (x :: Pt) -> case x of { Pt y z -> I# y }\n')
        d = os.path.join(td, 'b', 'build', 'Client')
        os.makedirs(d)
        with open(os.path.join(d, 'Ops.dump-simpl'), 'w') as fh:
            fh.write('==================== Tidy Core ====================\n' + core)
        e = os.path.join(td, 'empty')
        os.makedirs(e)
        s = os.path.join(td, 'suppressed', 'build')
        os.makedirs(s)
        with open(os.path.join(s, 'M.dump-simpl'), 'w') as fh:
            fh.write('-- RHS size: {terms: 1}\nf = \\ x -> case x of { I# y -> y }\n')
        for argv, code, why in (([td], 1, 'findings'),
                                ([td, '--module', 'Client'], 1, 'a --module'),
                                ([td, '--module', 'NoSuch'], 2, 'a --module matching nothing'),
                                ([e], 2, 'a tree without dumps'),
                                ([s], 2, 'a dump without binders\' types'),
                                ([ti], 2, 'a dump carrying IdInfo'),
                                ([td, '--sum'], 2, 'a --sum without a type'),
                                ([td, '--ignore', '('], 2, 'an --ignore that is no regex')):
            if main(argv) != code:
                bad.append(f'{why} did not exit {code}')
    for b in bad:
        print('FAIL', b)
    print('self-test', 'FAILED' if bad else 'passed')
    return 1 if bad else 0


def main(argv):
    if argv == ['--self-test']:
        return self_test()
    sub, sums, ignore, rest, i = None, set(SUMS), [], [], 0
    while i < len(argv):
        if argv[i] in ('--module', '--sum', '--ignore'):
            if i + 1 >= len(argv):
                print(__doc__.split('\n\n')[1], file=sys.stderr)
                return 2
            if argv[i] == '--module':
                sub = argv[i + 1]
            elif argv[i] == '--sum':
                sums.add(argv[i + 1])
            else:
                ignore.append(argv[i + 1])
            i += 2
        else:
            rest.append(argv[i])
            i += 1
    if len(rest) != 1 or rest[0].startswith('--'):
        print(__doc__.split('\n\n')[1], file=sys.stderr)
        return 2
    for r in ignore:
        try:
            re.compile(r)
        except re.error as e:
            print(f'--ignore {r!r} is no regex: {e}', file=sys.stderr)
            return 2
    if not dumps.walk(rest[0], '.dump-simpl'):
        print(f'no .dump-simpl file under {rest[0]}; was it built with '
              '-ddump-simpl -ddump-to-file?', file=sys.stderr)
        return 2
    lines, found, read, typed, info = report(rest[0], sub, sums, ignore)
    if not read:
        print(f"no module's path contains {sub}", file=sys.stderr)
        return 2
    if info:
        print(f'{info} carries IdInfo, whose binder annotations this does not '
              'parse; build it with -dsuppress-idinfo', file=sys.stderr)
        return 2
    if not typed:
        print('no binding carries its arguments\' types; was the tree built '
              'with -dsuppress-all?', file=sys.stderr)
        return 2
    if lines:
        print('\n'.join(lines))
    return 1 if found else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
