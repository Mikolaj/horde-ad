#!/usr/bin/env python3
"""Check orthotope's HasCallStack constraints against the rule they keep to.

Usage: python3 tools/hascallstack.py ROOT [--fix] [--list]
       python3 tools/hascallstack.py --self-test

ROOT is an orthotope checkout, of which Data.Array.Internal and the array
modules under it are read. The rule, ruled 2026-10-08, rests on the contract
policy that orthotope's README states: an operation's error on an argument
that has no result names the operation, while a check of a contract that
the operations establish says "violated contract". A function takes
HasCallStack exactly when it calls `error` with a message that is not
a violated contract's, or calls a function of the same name in another
module that takes it, as a wrapper of a generic module does, so that
the error shows the line the operation was called from. A contract check
guards against a bug in orthotope and adds no stack, nor does an assert,
and class methods take none, a stack on one binding every instance.

The rule reads the wording, so the wording is checked too: an error
in Data.Array.Internal that does not say "violated contract", and one
anywhere that says "impossible" or "shouldn't happen", are findings. So is
a stack-taking function that calls itself, each level of which would push
a frame of its own where a stack-free local worker pushes none.

Reports each signature the rule would change and each module whose
GHC.Stack import does not match its uses; `--fix` rewrites both and reports
what remains, and `--list` prints the verdict. Exit 0 when the tree keeps
the rule, 1 with the findings listed, 2 when the run did not happen:
a module missing under ROOT.
"""

import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hssource import strip_comments  # noqa: E402

MODS = ['Internal', 'DynamicG', 'RankedG', 'ShapedG', 'Dynamic', 'DynamicS',
        'DynamicU', 'Ranked', 'RankedS', 'RankedU', 'Shaped', 'ShapedS',
        'ShapedU']
ORTHOTOPE = dict(
    own='Data.Array',
    mods=MODS,
    path={m: 'Data/Array/Internal.hs' if m == 'Internal'
          else 'Data/Array/Internal/%s.hs' % m for m in MODS},
    # Whose every error checks a contract.
    internal='Internal')

SIG = re.compile(r"^([a-z][\w']*) ::(.*)$")
END = re.compile(r"^([a-z][\w']* ::|[a-z][\w']*\s*$|-- \||\{-#|"
                 r"(instance|class|data|newtype|type|deriving)\b)")
MESSAGE = re.compile(r'\berror\b\s*\$?\s*\(?\s*("[^"]*"|[a-zA-Z_][\w.]*)')
CONTRACT = 'violated contract'
UNWORDED = re.compile(r'"[^"]*(impossible|shouldn.t happen)')


def unquote(line):
    """The line with its string literals emptied."""
    out, q = [], False
    for i, c in enumerate(line):
        if c == '"' and (i == 0 or line[i - 1] != '\\'):
            q = not q
        elif not q:
            out.append(c)
    return ''.join(out)


def parse(cfg, texts):
    """{(module, name): sig, body, hcs, errors, occ}, and each module's
    imports of the others: {qualifier: module} and 'unqual': [modules].
    errors lists the message of each `error` call in the body, the literal
    or the name it is built from."""
    own = re.escape(cfg['own'])
    funs, imports = {}, {}
    for m in cfg['mods']:
        lines = texts[m].split('\n')
        code = [unquote(l) for l in strip_comments(texts[m]).split('\n')]
        imp = {'unqual': []}
        for l in lines:
            a = re.match(r'import\s+qualified\s+(%s(?:\.\w+)*)\s+as\s+(\w+)'
                         % own, l)
            if a and a.group(1).split('.')[-1] in cfg['mods']:
                imp[a.group(2)] = a.group(1).split('.')[-1]
            b = re.match(r'import\s+(%s(?:\.\w+)*)\s*(\(|$)' % own, l)
            if b and b.group(1).split('.')[-1] in cfg['mods']:
                imp['unqual'].append(b.group(1).split('.')[-1])
        imports[m] = imp
        k = 0
        while k < len(lines):
            mm = SIG.match(lines[k])
            if (not mm and k + 1 < len(lines)
                    and re.match(r"^[a-z][\w']*\s*$", lines[k])
                    and re.match(r'^\s+::', lines[k + 1])):
                mm = re.match(r"^([a-z][\w']*)", lines[k])
            if not mm:
                k += 1
                continue
            name, j = mm.group(1), k + 1
            while j < len(lines) and lines[j].startswith(' '):
                j += 1
            sig_end = j
            while j < len(lines) and not END.match(lines[j]):
                j += 1
            occ, errors = {}, []
            for i in range(sig_end, j):
                # The name heading its own equation is no call.
                l = re.sub(r"^%s\b" % re.escape(name), ' ' * len(name),
                           code[i])
                for q, f in re.findall(r"\b(?:([A-Z]\w*)\.)?([a-z_][\w']*)\b",
                                       l):
                    occ.setdefault((q, f), []).append(i)
                if re.search(r'\berror\b', l):
                    e = MESSAGE.search(lines[i])
                    errors.append((i, e.group(1) if e else ''))
            funs[(m, name)] = dict(
                sig=(k, sig_end), body=(sig_end, j),
                hcs='HasCallStack' in ' '.join(lines[k:sig_end]),
                errors=errors, occ=occ)
            k = j
    return funs, imports


def graph(funs, imports):
    """{(caller, callee): [lines of the calls]}."""
    defs = {}
    for m, n in funs:
        defs.setdefault(m, set()).add(n)
    edges = {}
    for (m, name), d in funs.items():
        for (q, f), lns in d['occ'].items():
            if q:
                tm = imports[m].get(q)
                tgts = [(tm, f)] if tm and f in defs.get(tm, ()) else []
            elif f in defs[m]:
                tgts = [(m, f)]
            else:
                tgts = [(u, f) for u in imports[m]['unqual']
                        if f in defs.get(u, ())]
            for t in tgts:
                edges.setdefault(((m, name), t), []).extend(lns)
    return edges


def verdict(cfg, texts):
    """The functions the rule gives HasCallStack, with the parse and the
    call graph."""
    funs, imports = parse(cfg, texts)
    edges = graph(funs, imports)
    v = {k for k, d in funs.items()
         if any(CONTRACT not in msg for _, msg in d['errors'])}
    while True:
        new = {g for g, f in edges
               if g not in v and f in v and f[1] == g[1] and f[0] != g[0]}
        if not new:
            return v, funs, edges
        v |= new


def split_ctx(sig):
    """The signature up to `::` and an optional forall, the context before
    the first top-level `=>` or None, and the rest."""
    i = j = sig.index('::') + 2
    fa = re.match(r'\s*forall\s[^.]*\.', sig[i:])
    if fa:
        j = i + fa.end()
    depth = 0
    for p in range(j, len(sig) - 1):
        c = sig[p]
        if c in '([':
            depth += 1
        elif c in ')]':
            depth -= 1
        elif depth == 0 and sig.startswith('=>', p):
            return sig[:j], sig[j:p], sig[p:]
        elif depth == 0 and sig.startswith('->', p):
            break
    return sig[:j], None, sig[j:]


def add_hcs(sig):
    head, ctx, rest = split_ctx(sig)
    if ctx is None:
        lead = re.match(r'\s*', rest).group(0)
        return head + lead + '(HasCallStack) => ' + rest[len(lead):]
    c = ctx.strip()
    if c.startswith('(') and c.endswith(')'):
        i = ctx.index('(')
        return head + ctx[:i + 1] + 'HasCallStack, ' + ctx[i + 1:] + rest
    lead = re.match(r'\s*', ctx).group(0)
    return head + lead + '(HasCallStack, ' + c + ') ' + rest


def drop_hcs(sig):
    head, ctx, rest = split_ctx(sig)
    c = ctx.strip()
    if c in ('HasCallStack', '(HasCallStack)'):
        return (head + re.match(r'\s*', ctx).group(0)
                + re.sub(r'^=>\s*', '', rest, count=1))
    new = re.sub(r'HasCallStack\s*,\s*', '', ctx, count=1)
    if new == ctx:
        new = re.sub(r',\s*HasCallStack', '', ctx, count=1)
    return head + new + rest


def stack_import(cfg, s):
    """(the GHC.Stack import line or None, whether the code names
    HasCallStack)."""
    has = re.search(r'^import\s+GHC\.Stack\b.*$', s, re.M)
    code = '\n'.join(l for l in strip_comments(s).split('\n')
                     if not l.startswith('import'))
    return has, re.search(r'\bHasCallStack\b', code) is not None


def fix_import(cfg, s):
    has, uses = stack_import(cfg, s)
    if uses and not has:
        lines = s.split('\n')
        imps = [i for i, l in enumerate(lines) if l.startswith('import ')]
        own = re.compile(r'import\s+(qualified\s+)?%s\b' % re.escape(cfg['own']))
        # In order among the unqualified imports of other packages, which
        # come first, else before the module's own.
        pos = next((i for i in imps
                    if not lines[i].startswith('import qualified')
                    and not own.match(lines[i])
                    and lines[i][len('import '):].lstrip() > 'GHC.Stack'),
                   None)
        if pos is None:
            pos = next((i for i in imps if own.match(lines[i])),
                       imps[-1] + 1 if imps else 1)
        lines.insert(pos, 'import GHC.Stack(HasCallStack)')
        s = '\n'.join(lines)
    elif has and not uses:
        s = s.replace(has.group(0) + '\n', '', 1)
    return s


def rewrite(cfg, texts, v):
    """The texts with HasCallStack on exactly the functions of v, and
    GHC.Stack imported where it is used."""
    funs, _ = parse(cfg, texts)
    out = {}
    for m in cfg['mods']:
        lines = texts[m].split('\n')
        for k, d in sorted(funs.items(), key=lambda x: -x[1]['sig'][0]):
            if k[0] != m or (k in v) == d['hcs']:
                continue
            b, e = d['sig']
            sig = '\n'.join(lines[b:e])
            new = add_hcs(sig) if k in v else drop_hcs(sig)
            lines[b:e] = new.split('\n')
        out[m] = fix_import(cfg, '\n'.join(lines))
    return out


def name(k):
    return '%s.%s' % k


def check(cfg, texts):
    """The findings, one line each, and the verdict."""
    v, funs, edges = verdict(cfg, texts)
    out = []
    for k, d in sorted(funs.items()):
        where = '%s:%d' % (cfg['path'][k[0]], d['sig'][0] + 1)
        if (k in v) != d['hcs']:
            out.append('%s HasCallStack: %s (%s)'
                       % ('add' if k in v else 'drop', name(k), where))
        if k in v and (k, k) in edges:
            out.append('calls itself with a stack: %s (%s)' % (name(k), where))
        for i, msg in d['errors']:
            line = texts[k[0]].split('\n')[i]
            if UNWORDED.search(line) or (k[0] == cfg['internal']
                                         and CONTRACT not in msg):
                out.append('error worded as neither: %s (%s:%d): %s'
                           % (name(k), cfg['path'][k[0]], i + 1,
                              line.strip()[:60]))
    for m in cfg['mods']:
        has, uses = stack_import(cfg, texts[m])
        if bool(has) != uses:
            out.append('GHC.Stack import %s: %s'
                       % ('missing' if uses else 'unused', cfg['path'][m]))
    return out, v


def main(argv, cfg=ORTHOTOPE):
    if argv == ['--self-test']:
        return self_test()
    flags = [a for a in argv if a.startswith('--')]
    args = [a for a in argv if not a.startswith('--')]
    if len(args) != 1 or set(flags) - {'--fix', '--list'}:
        print(__doc__.split('\n\n')[1])
        return 2
    root, texts = args[0], {}
    for m in cfg['mods']:
        p = os.path.join(root, cfg['path'][m])
        if not os.path.isfile(p):
            print('no %s under %s: nothing checked' % (cfg['path'][m], root))
            return 2
        with open(p) as fh:
            texts[m] = fh.read()
    if '--fix' in flags:
        v = verdict(cfg, texts)[0]
        new = rewrite(cfg, texts, v)
        for m in cfg['mods']:
            if new[m] != texts[m]:
                with open(os.path.join(root, cfg['path'][m]), 'w') as fh:
                    fh.write(new[m])
                print('rewrote', cfg['path'][m])
        texts = new
    out, v = check(cfg, texts)
    if '--list' in flags:
        for m in cfg['mods']:
            print('%s: %s' % (m, ' '.join(sorted(n for mm, n in v
                                                 if mm == m))))
    for o in out:
        print(o)
    print('%d functions take HasCallStack by the rule; %d findings'
          % (len(v), len(out)))
    return 1 if out else 0


FIXTURE = {
    'A': '''module Lib.A where

import GHC.Stack(HasCallStack)
import qualified Lib.C as C

build :: Int -> [Int]
build n | n < 0 = error "build: negative size"
        | otherwise = [0 .. n]

total :: (HasCallStack) => [Int] -> Int
total = sum

twice :: Int -> [Int]
twice n = build n ++ build n

view :: Int -> Int
view i = C.at i

grow :: Int -> [Int]
grow k | k < 0 = error "grow: negative size"
       | k == 0 = []
       | otherwise = k : grow (k - 1)

long
  :: Int -> Int
long n = if n < 0 then error "long: negative" else n
''',
    'B': '''module Lib.B where

import qualified Lib.A as A

build :: Int -> [Int]
build = A.build

twice :: Int -> [Int]
twice = A.twice

size :: Int -> Int
size n = length (A.build n)
''',
    'C': '''module Lib.C where

import GHC.Stack(HasCallStack)

-- | Indexes, with no use for HasCallStack.
at :: (HasCallStack) => Int -> Int
at i | i < 0 = error "at: violated contract: negative index"
     | otherwise = i

bad :: Int -> Int
bad i = if i < 0 then error "impossible" else i

half :: Int -> Int
half i = if odd i then error "half: odd" else i `div` 2
'''}


def self_test():
    """The fixture above: the verdict, the wording and recursion findings,
    the rewrite and its fixed point, and the exit codes."""
    import tempfile
    cfg = dict(own='Lib', mods=['A', 'B', 'C'],
               path={m: 'Lib/%s.hs' % m for m in 'ABC'}, internal='C')
    bad = []

    def kinds(out, kind):
        return sorted(o.split(': ')[1].split(' ')[0] for o in out
                      if o.startswith(kind))
    out, v = check(cfg, FIXTURE)
    if kinds(out, 'add') != ['A.build', 'A.grow', 'A.long', 'B.build',
                             'C.bad', 'C.half']:
        bad.append('adds %s' % kinds(out, 'add'))
    if kinds(out, 'drop') != ['A.total', 'C.at']:
        bad.append('drops %s' % kinds(out, 'drop'))
    if kinds(out, 'calls itself') != ['A.grow']:
        bad.append('recursion %s' % kinds(out, 'calls itself'))
    if kinds(out, 'error worded') != ['C.bad', 'C.half']:
        bad.append('wording %s' % kinds(out, 'error worded'))
    new = rewrite(cfg, FIXTURE, v)
    want = ['build :: (HasCallStack) => Int -> [Int]',
            'total :: [Int] -> Int', 'twice :: Int -> [Int]',
            'view :: Int -> Int', 'long\n  :: (HasCallStack) => Int -> Int',
            'size :: Int -> Int',
            'import GHC.Stack(HasCallStack)\nimport qualified Lib.A as A\n',
            'at :: Int -> Int']
    text = '\n'.join(new[m] for m in 'ABC')
    bad += ['rewrite lacks %r' % w for w in want if w not in text]
    if new['C'].count('import GHC.Stack') != 1:
        bad.append('C keeps one import, bad taking the stack')
    out, _ = check(cfg, new)
    rest = sorted(o.split(':')[0] for o in out)
    if rest != ['calls itself with a stack', 'error worded as neither',
                'error worded as neither']:
        bad.append('after the rewrite: %s' % out)
    clean = dict(FIXTURE)
    clean['A'] = re.sub(r'grow ::.*?\n\n', '', clean['A'], flags=re.S)
    clean['C'] = clean['C'][:clean['C'].index('bad ::')]
    with tempfile.TemporaryDirectory() as td:
        os.makedirs(os.path.join(td, 'Lib'))
        for m in 'ABC':
            with open(os.path.join(td, 'Lib', m + '.hs'), 'w') as fh:
                fh.write(clean[m])
        if main([td], cfg) != 1:
            bad.append('findings did not exit 1')
        if main([td, '--fix'], cfg) != 0:
            bad.append('--fix did not exit 0')
        with open(os.path.join(td, 'Lib', 'C.hs')) as fh:
            if 'GHC.Stack' in fh.read():
                bad.append("--fix kept C's unused import")
        if main([td], cfg) != 0:
            bad.append('a fixed tree did not exit 0')
        os.remove(os.path.join(td, 'Lib', 'C.hs'))
        if main([td], cfg) != 2:
            bad.append('a missing module did not exit 2')
    for b in bad:
        print('FAIL', b)
    print('self-test', 'FAILED' if bad else 'passed')
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
