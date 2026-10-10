#!/usr/bin/env python3
"""List the overloaded bindings of a source tree that carry no pragma.

Usage: python3 tools/pragma-census.py SRC
       python3 tools/pragma-census.py --self-test

For every `.hs` file under SRC, the top-level functions whose signature has
a context and the methods of the instances that have one, which carry
no `INLINE`, `INLINABLE`, `NOINLINE` or `SPECIALISE` pragma of their name:
what docs/perf-checklist.md's P asks a pragma, or a reason beside the code,
of where their callers' speed is protected. A context counts only where it
holds a class constraint. `HasCallStack`, an equality
`a ~ b`, a `TypeError` and a type-level `<=` give a caller nothing
to specialise, so a signature or an instance with only those is passed over,
as are a `TypeError` instance, whose methods cannot be called, and a method
defined as `undefined`.

A signature may span lines, its context running to the first `=>` outside
parentheses, a rank-2 argument's context being its own; a method may be
defined prefix, as an operator section, `(<*>) = ...`, or infix, `x == y` or
`` a@(T x) `compare` b ``, and on the instance's own line after its `where`;
an instance head may span lines too, and only the lines at the body's own
indentation define a method, the deeper ones continuing it. A method's pragma
is looked for in its instance, a top-level function's anywhere in its module,
and a line `m :: ...` in an instance is its signature while a definition
holding `(Proxy :: Proxy n)` is not. A class's own signatures and default
methods, indented under it, are no instance's. It is a reader of lines and
not a parser: a top-level binding without a signature, a local function and a
pragma naming a binding of another module are not seen, and its verdict is a
list of candidates for P's rule, which only the callers decide.

Exit 0 when every overloaded binding carries a pragma, 1 when one does not,
2 when SRC holds no `.hs` file.
"""

import os
import re
import sys

PRAGMA = re.compile(r'\{-#\s*(?:INLINE|INLINABLE|INLINEABLE|NOINLINE'
                    r'|SPECIALI[SZ]E)\s*(?:\[~?\d+\]\s*)?\(?([^\s)#,]+)')
TOP_SIG = re.compile(r"^([a-z_][\w']*(?:\s*,\s*[a-z_][\w']*)*"
                     r"|\([!#$%&*+./<=>?@\\^|~:-]+\))\s*::(.*)")
OP = r"[!#$%&*+./<=>?@\\^|~:-]+"
SECTION = re.compile(r'^\((' + OP + r')\)')
INFIX_OP = re.compile(r"\s+(`[\w']+`|" + OP + r")(?=\s)")
SIGNATURE = re.compile(r"^(?:[\w']+|\(" + OP + r"\))(?:\s*,\s*[\w']+)*\s+::")


def constraints(ctx):
    """The class constraints of a context, the rest dropped."""
    ctx = re.sub(r'^\s*forall\b[^.]*\.', '', ctx).strip()
    if ctx.startswith('(') and ctx.endswith(')'):
        depth = 0
        for i, ch in enumerate(ctx):
            depth += ch == '('
            depth -= ch == ')'
            if depth == 0 and i < len(ctx) - 1:
                break
        else:
            ctx = ctx[1:-1]
    parts, depth, cur = [], 0, ''
    for ch in ctx:
        depth += ch in '(['
        depth -= ch in ')]'
        if ch == ',' and depth == 0:
            parts.append(cur)
            cur = ''
        else:
            cur += ch
    parts.append(cur)
    return [' '.join(p.split()) for p in parts
            if p.strip() and p.strip() != 'HasCallStack' and '~' not in p
            and not p.strip().startswith('TypeError') and '<=' not in p]


def context(sig):
    """The context of a signature, before its first `=>` outside parentheses
    and brackets, or None where it has none."""
    depth = 0
    for i, ch in enumerate(sig):
        depth += ch in '(['
        depth -= ch in ')]'
        if depth == 0 and sig.startswith('=>', i):
            return sig[:i]
    return None


def pattern_end(s):
    """Where the first pattern of a definition ends: a variable or constructor,
    or a parenthesised pattern, either behind an as-pattern's `x@`."""
    m = re.match(r"[\w']+@", s)
    i = m.end() if m else 0
    if s[i:i + 1] == '(':
        depth = 0
        for j in range(i, len(s)):
            depth += s[j] == '('
            depth -= s[j] == ')'
            if depth == 0:
                return j + 1
        return None
    m = re.match(r"[\w'.]+", s[i:])
    return i + m.end() if m else None


def method_name(line):
    """The method a line of an instance body defines, or None."""
    s = line.strip()
    if not s or s.startswith(('--', '{-', '|')) or SIGNATURE.match(s):
        return None
    m = SECTION.match(s)
    if m:
        return m.group(1)
    end = pattern_end(s)
    m = INFIX_OP.match(s, end) if end else None
    if m and m.group(1) not in ('=', '|'):
        return m.group(1).strip('`')
    m = re.match(r"^([a-z_][\w']*)", s)
    return m.group(1) if m else None


def indent(line):
    return len(line) - len(line.lstrip())


def census(text):
    """([(line, name, constraints)] of the top-level functions and
    [(line, class, method)] of the instance methods carrying no pragma."""
    lines = text.split('\n')
    module_pragmas = {m.group(1) for line in lines
                      for m in PRAGMA.finditer(line)}
    funs, meths = [], []
    i = 0
    while i < len(lines):
        line = lines[i]
        m = TOP_SIG.match(line)
        if m:
            sig, j = m.group(2), i + 1
            while (j < len(lines) and lines[j][:1] in (' ', '\t')
                   and not lines[j].strip().startswith('--')):
                sig += ' ' + lines[j]
                j += 1
            ctx = context(sig)
            if ctx is not None:
                cs = constraints(ctx)
                for name in re.split(r'\s*,\s*', m.group(1).strip()):
                    name = name.strip('()')
                    if cs and name not in module_pragmas:
                        funs.append((i + 1, name, cs))
            i = j
            continue
        if line.startswith('instance'):
            head, j = line, i
            while not re.search(r'\bwhere\b', head) and j + 1 < len(lines) \
                    and lines[j + 1][:1] in (' ', '\t'):
                j += 1
                head += ' ' + lines[j].strip()
            hm = re.match(r'^instance\b(.*?)(?:\bwhere\b(.*))?$', head)
            k = j + 1
            while k < len(lines) and (lines[k][:1] in (' ', '\t')
                                      or not lines[k].strip()):
                if not lines[k].strip() and k + 1 < len(lines) \
                        and lines[k + 1][:1] not in (' ', '\t'):
                    break
                k += 1
            if hm and '=>' in hm.group(1):
                ctx, cls_head = hm.group(1).split('=>', 1)
                cs = constraints(ctx)
                if cs:
                    cls = cls_head.split()[0]
                    rest = [(n, lines[n]) for n in range(j + 1, k)
                            if lines[n].strip()]
                    base = min((indent(b) for _, b in rest), default=0)
                    body = [(j, hm.group(2) or '')] + [
                        (n, b) for n, b in rest if indent(b) == base]
                    pragmas = {p.group(1) for b in [head] + lines[j + 1:k]
                               for p in PRAGMA.finditer(b)}
                    seen = set()
                    for n, b in body:
                        name = method_name(b)
                        if name and name not in seen and name not in pragmas \
                                and not b.rstrip().endswith('= undefined'):
                            meths.append((n + 1, cls, name))
                        seen.add(name)
            i = k
            continue
        i += 1
    return funs, meths


def report(src):
    """(lines, number of bindings listed, number of .hs files read)."""
    files = []
    for d, dirs, names in os.walk(src):
        dirs[:] = sorted(x for x in dirs if not x.startswith(('.', 'dist')))
        files += [os.path.join(d, x) for x in sorted(names)
                  if x.endswith('.hs')]
    funs, meths = [], []
    for path in files:
        with open(path) as fh:
            f, m = census(fh.read())
        rel = os.path.relpath(path, src)
        funs += [(rel, n, name, cs) for n, name, cs in f]
        meths += [(cls, rel, n, name) for n, cls, name in m]
    out = ['== overloaded functions without a pragma'
           ' (file:line name [context])']
    out += [f'  {rel}:{n} {name} [{", ".join(cs)}]'
            for rel, n, name, cs in funs]
    out.append('== overloaded instance methods without a pragma'
               ' (class: file:line method)')
    out += [f'  {cls}: {rel}:{n} {name}'
            for cls, rel, n, name in sorted(meths)]
    return out, len(funs) + len(meths), len(files)


def self_test():
    import tempfile
    src = ('module M where\n'
           'f :: HasCallStack => Int -> Int\n'
           'f = id\n'
           'g :: (HasCallStack, Num a) => a -> a\n'
           'g = id\n'
           'h :: (a ~ b) => a -> b\n'
           'h = id\n'
           'k :: forall a .\n'
           '     (Show a)\n'
           '  => a -> String\n'
           'k = show\n'
           '{-# INLINABLE m #-}\n'
           'm :: Eq a => a -> Bool\n'
           'm x = x == x\n'
           'p :: ((o + n) <= s) => Int\n'
           'p = 0\n'
           'class C a where\n'
           '  c :: Eq a => a -> Int\n'
           '  c _ = 0\n'
           'instance Show a => Show (T a) where show = showT\n'
           'instance Eq a => Eq (T a) where\n'
           '  (T x) == (T y) = x == y\n'
           '  {-# INLINE (==) #-}\n'
           '  x /= y = not (x == y)\n'
           'instance Num a => Num (T a) where\n'
           '  (+) = liftT2 (+)\n'
           '  negate (T x) = T (negate x)\n'
           '  negate _ = undefined\n'
           '  {-# INLINE negate #-}\n'
           "instance (TypeError ('Text \"no\")) => C (T Bool) where\n"
           '  c = error "no"\n'
           'instance KnownNat n => D (P n) where\n'
           '  {-# INLINE d #-}\n'
           '  d = natVal (Proxy :: Proxy n)\n'
           'instance KnownNat n => E (P n) where\n'
           '  e = natVal (Proxy :: Proxy n)\n'
           'instance (Num a,\n'
           '          Show a) => F (T a) where\n'
           '  f1 = 1\n'
           '\n'
           '  a `f2` b = a\n'
           'instance Show U where show _ = "U"\n'
           'instance (a ~ b) => G a b where g = id\n'
           'instance Ord a => H (T a) where\n'
           '  hh :: T a -> Int\n'
           '  hh _ = 0\n'
           '  {-# INLINE hh #-}\n'
           'instance Ord a => J (T a) where\n'
           '  jj = undefined\n'
           'instance Ord a => K (T a) where\n'
           '  kk 0 = 1\n'
           '  kk _ = 2\n'
           'q1, q2 :: Num a => a\n'
           'q1 = 0\n'
           'q2 = 1\n'
           '{-# INLINE [1] r #-}\n'
           'r :: Num a => a\n'
           'r = 0\n'
           '{-# SPECIALISE s :: Int -> Int #-}\n'
           's :: Num a => a -> a\n'
           's = id\n'
           'instance Show a => Show (V a) where\n'
           '  showsPrec p v = showString "V " .\n'
           '    showsPrec p (unV v)\n'
           '  show v = s\n'
           '    where s = "V"\n'
           'instance (Ord a, Show a)\n'
           '         => Ord (V a) where\n'
           '  a@(V (W x)) `compare` (V y) = compare x y\n'
           '  {-# INLINE compare #-}\n'
           'instance Arbitrary a => Arbitrary (V a) where\n'
           '  arbitrary = do\n'
           '    x <- arbitrary\n'
           '    return (V x)\n'
           'withRank :: Int -> (forall n . KnownNat n => Proxy n -> r) -> r\n'
           'withRank = undefined\n'
           'hr :: Num a => (forall n . KnownNat n => Proxy n -> a) -> a\n'
           'hr = undefined\n')
    want = ['== overloaded functions without a pragma'
            ' (file:line name [context])',
            '  M.hs:4 g [Num a]',
            '  M.hs:8 k [Show a]',
            '  M.hs:53 q1 [Num a]',
            '  M.hs:53 q2 [Num a]',
            '  M.hs:77 hr [Num a]',
            '== overloaded instance methods without a pragma'
            ' (class: file:line method)',
            '  Arbitrary: M.hs:72 arbitrary',
            '  E: M.hs:36 e',
            '  Eq: M.hs:24 /=',
            '  F: M.hs:39 f1',
            '  F: M.hs:41 f2',
            '  K: M.hs:51 kk',
            '  Num: M.hs:26 +',
            '  Show: M.hs:20 show',
            '  Show: M.hs:63 showsPrec',
            '  Show: M.hs:65 show']
    bad = []
    with tempfile.TemporaryDirectory() as td:
        os.makedirs(os.path.join(td, 'S'))
        os.makedirs(os.path.join(td, 'E'))
        os.makedirs(os.path.join(td, 'C'))
        with open(os.path.join(td, 'S', 'M.hs'), 'w') as fh:
            fh.write(src)
        with open(os.path.join(td, 'C', 'N.hs'), 'w') as fh:
            fh.write('module N where\n{-# INLINE n #-}\n'
                     'n :: Num a => a\nn = 0\n')
        got, nbad, nfiles = report(os.path.join(td, 'S'))
        if got != want or (nbad, nfiles) != (15, 1):
            bad.append(f'report ({nbad}, {nfiles}):\n  ' + '\n  '.join(got))
        for d, code, why in (('S', 1, 'bindings without a pragma'),
                             ('E', 2, 'a tree without .hs files'),
                             ('C', 0, 'a tree whose bindings all carry one')):
            if main([os.path.join(td, d)]) != code:
                bad.append(f'{why} did not exit {code}')
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
    lines, nbad, nfiles = report(argv[0])
    if not nfiles:
        print(f'no .hs file under {argv[0]}', file=sys.stderr)
        return 2
    print('\n'.join(lines))
    return 1 if nbad else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
