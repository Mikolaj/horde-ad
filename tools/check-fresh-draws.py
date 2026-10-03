#!/usr/bin/env python3
"""Fresh identifiers are drawn only where no evaluation can be duplicated.

Usage: python3 tools/check-fresh-draws.py [FILE ...]
       python3 tools/check-fresh-draws.py --self-test

The library draws AST variable ids and delta node ids from two global
counters, impurely, and the header of src/HordeAd/Core/AstFreshId.hs says
why every draw runs under unsafePerformIO and none under
unsafeDupablePerformIO: a thunk two threads force at once runs twice under
the latter, and a result read in two parts can then mix the copies, a binder
from one with a body from the other. This makes that rule mechanical, over
the Haskell files given or, given none, over every tracked .hs file under
src/, test/, bench/ and example/:

1. unsafeDupablePerformIO appears only in the top-level definitions ALLOW
   names, each with the reason every evaluation of it computes the same
   result; the other duplicable primitives (FORBIDDEN) appear in no code,
   imports aside.
2. No definition ALLOW names mentions an unprotected drawer: a counter, or
   a top-level definition that mentions one, transitively, without running
   under unsafePerformIO itself. A protected drawer, funToAst and its kin,
   may be called from one: its noDuplicate# claims every thunk under
   evaluation at the draw, the allowed definition's included.
3. Every ALLOW entry and every counter whose module is among the files read
   is still there, and an ALLOW entry still uses unsafeDupablePerformIO, so
   neither list outlives what it names.

Comments, pragmas and string and character literals are blanked before
anything is matched, so prose about the primitives, of which the AstFreshId
header has plenty, never reads as a use of them. A top-level definition
is the run of lines from one starting in the first column to the next
such line, CPP lines aside, and every run with one name in a file is one
definition, a signature being free to stand apart from its equations. A
module is named by its `module` header, not its path, so a file checked
under another name keeps its entries.

Exit 0 when the rule holds, 1 with a line per finding, 2 when nothing was
read: no file given and none tracked, or a file that cannot be opened.
"""

import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import chdir_root  # noqa: E402

DIRS = ('src', 'test', 'bench', 'example')
DUPABLE = 'unsafeDupablePerformIO'
PLAIN = 'unsafePerformIO'
# (module, definition): why every evaluation computes the same result. A new
# entry is a claim a reviewer reads here: it draws nothing, and any effect
# runs behind noDuplicate.
ALLOW = {
    ('HordeAd.Core.AstTools', 'astIsSmall'):
        'reads a flag that only tests set and draws nothing',
    ('HordeAd.Core.AstVectorize', 'mkTraceRule'):
        'reads the tracing flag and draws nothing; the tracing branch calls '
        'noDuplicate before its effects',
}
# Duplicable without even unsafeDupablePerformIO's discipline, or the raw
# primitive under both: nothing here needs one.
FORBIDDEN = ('unsafeDupableInterleaveIO', 'unsafeInterleaveIO',
             'accursedUnutterablePerformIO', 'unsafeInlineIO',
             'inlinePerformIO', 'runRW#')
# The seeds of rule 2: every draw reaches one of these.
COUNTERS = {
    ('HordeAd.Core.AstFreshId', 'unsafeAstVarCounter'),
    ('HordeAd.Core.DeltaFreshId', 'unsafeGlobalCounter'),
}

SYMBOL = set('!#$%&*+./<=>?@\\^|-~:')
CHAR_LIT = re.compile(r"'(?:\\.[^'\n]*|[^'\\\n])'")
TOKEN = re.compile(r"[A-Za-z_][\w']*#?")
MODULE = re.compile(r'^module\s+([A-Z][\w.]*)', re.M)
NAME = re.compile(r"^([a-z_][\w']*)")
KEYWORDS = {'import', 'instance', 'data', 'type', 'newtype', 'class',
            'module', 'infix', 'infixl', 'infixr', 'deriving', 'foreign',
            'pattern', 'default'}


def blank(text):
    """TEXT with comments, pragmas and string and character literals turned
    to spaces, newlines kept, so names and line numbers survive."""
    out = []
    i, n, depth = 0, len(text), 0
    while i < n:
        c = text[i]
        if depth:
            if text.startswith('{-', i):
                depth += 1
                out.append('  ')
                i += 2
            elif text.startswith('-}', i):
                depth -= 1
                out.append('  ')
                i += 2
            else:
                out.append('\n' if c == '\n' else ' ')
                i += 1
        elif text.startswith('{-', i):
            depth = 1
            out.append('  ')
            i += 2
        elif text.startswith('--', i) and (i == 0 or text[i - 1] not in SYMBOL):
            j = i
            while j < n and text[j] == '-':
                j += 1
            if j < n and text[j] in SYMBOL:  # an operator such as -->
                out.append(text[i:j])
                i = j
                continue
            while j < n and text[j] != '\n':
                j += 1
            out.append(' ' * (j - i))
            i = j
        elif c == '"':
            j = i + 1
            while j < n and text[j] not in '"\n':
                j += 2 if text[j] == '\\' else 1
            j = min(j + 1, n)
            out.append(''.join('\n' if ch == '\n' else ' '
                               for ch in text[i:j]))
            i = j
        elif c == "'" and (i == 0 or not (text[i - 1].isalnum()
                                          or text[i - 1] in "_'")):
            m = CHAR_LIT.match(text, i)
            if m:
                out.append(' ' * len(m.group()))
                i = m.end()
            else:  # a promotion tick, as in '[] or 'True
                out.append(c)
                i += 1
        else:
            out.append(c)
            i += 1
    return ''.join(out)


class Definition:
    def __init__(self, path, module, name, kind, line):
        self.path, self.module, self.name = path, module, name
        self.kind, self.line = kind, line
        self.lines = []  # (line number, blanked text)
        self._tokens = None

    def tokens(self):
        if self._tokens is None:
            self._tokens = {t for _, text in self.lines
                            for t in TOKEN.findall(text)}
        return self._tokens

    def first(self, token):
        """The number of the first line mentioning TOKEN."""
        for no, text in self.lines:
            if token in TOKEN.findall(text):
                return no
        return self.line

    def label(self):
        return self.name or 'the %s at line %d' % (self.kind, self.line)


def definitions(path, text):
    """The module name and the top-level definitions of one file."""
    bl = blank(text)
    m = MODULE.search(bl)
    module = m.group(1) if m else 'Main'
    defs, named, cur = [], {}, None
    for no, line in enumerate(bl.split('\n'), 1):
        if line[:1] and not line[0].isspace() and line[0] != '#':
            m = NAME.match(line)
            word = m.group(1) if m else None
            if word in KEYWORDS:
                cur = Definition(path, module, None, word, no)
                defs.append(cur)
            elif word:
                # A signature may stand apart from its equations, so every
                # run with one name is one definition.
                cur = named.get(word)
                if cur is None:
                    cur = named[word] = Definition(path, module, word,
                                                   'definition', no)
                    defs.append(cur)
            else:
                cur = Definition(path, module, None, 'declaration', no)
                defs.append(cur)
        if cur:
            cur.lines.append((no, line))
    return module, defs


def findings(files):
    """The findings, as `path:line: message`, of FILES, a list of
    (path, text) pairs."""
    out = []
    defs, modules = [], set()
    for path, text in files:
        module, ds = definitions(path, text)
        modules.add(module)
        defs.extend(ds)
    code = [d for d in defs if d.kind != 'import']
    for d in code:
        toks = d.tokens()
        for bad in FORBIDDEN:
            if bad in toks:
                out.append('%s:%d: %s in %s; no duplicable primitive but %s '
                           'is permitted' % (d.path, d.first(bad), bad,
                                             d.label(), DUPABLE))
        if DUPABLE in toks and (d.module, d.name) not in ALLOW:
            out.append('%s:%d: %s uses %s, which ALLOW does not list'
                       % (d.path, d.first(DUPABLE), d.label(), DUPABLE))
    # Rule 2: grow the unprotected drawers from the counters, stopping at a
    # definition that runs under unsafePerformIO itself.
    draw = {name for module, name in COUNTERS}
    grew = True
    while grew:
        grew = False
        for d in code:
            if d.name and d.name not in draw:
                toks = d.tokens()
                if PLAIN not in toks and toks & draw:
                    draw.add(d.name)
                    grew = True
    present = {(d.module, d.name): d for d in code if d.name}
    for key in sorted(ALLOW):
        d = present.get(key)
        if d is None:
            if key[0] in modules:
                out.append('%s: ALLOW lists %s.%s, which is gone; drop it '
                           'from ALLOW' % (key[0], key[0], key[1]))
            continue
        toks = d.tokens()
        if DUPABLE not in toks:
            out.append('%s:%d: ALLOW lists %s, which no longer uses %s; drop '
                       'it from ALLOW' % (d.path, d.line, d.name, DUPABLE))
        for name in sorted((toks & draw) - {d.name}):
            out.append('%s:%d: %s, allowed %s, mentions %s, which draws a '
                       'fresh identifier without %s of its own'
                       % (d.path, d.first(name), d.name, DUPABLE, name,
                          PLAIN))
    for key in sorted(COUNTERS):
        if key[0] in modules and key not in present:
            out.append('%s: no counter %s is defined there, so rule 2 has '
                       'nothing to grow from; update COUNTERS'
                       % (key[0], key[1]))
    return out


def tracked():
    """The tracked Haskell under DIRS, from the repository root, or None
    when git cannot list them."""
    chdir_root()
    r = subprocess.run(['git', 'ls-files', '--'] +
                       ['%s/*.hs' % d for d in DIRS],
                       capture_output=True, text=True)
    if r.returncode != 0:
        return None
    return r.stdout.split()


def self_test():
    """Fixtures for each rule, and for the blanking each rule relies on."""
    import tempfile
    fresh = ('module HordeAd.Core.AstFreshId where\n'
             'unsafeAstVarCounter :: Counter\n'
             '{-# NOINLINE unsafeAstVarCounter #-}\n'
             'unsafeAstVarCounter = unsafePerformIO (new 100000001)\n'
             'unsafeGetFreshAstVarId :: IO AstVarId\n'
             'unsafeGetFreshAstVarId = add unsafeAstVarCounter 1\n'
             'funToAstIO ftk f = do\n'
             '  !freshId <- unsafeGetFreshAstVarId\n'
             '  return (freshId, f freshId)\n'
             'funToAst :: Int -> (Int -> Int) -> (Int, Int)\n'
             'funToAst ftk = unsafePerformIO . funToAstIO ftk\n')
    delta = ('module HordeAd.Core.DeltaFreshId where\n'
             'unsafeGlobalCounter = unsafePerformIO (new 100000001)\n'
             'shareDelta d = unsafePerformIO $ do\n'
             '  n <- add unsafeGlobalCounter 1\n'
             '  return $! (n, d)\n')
    tools = ('module HordeAd.Core.AstTools where\n'
             'import System.IO.Unsafe (unsafeDupablePerformIO)\n'
             '-- | Mentions unsafeDupablePerformIO and runRW# in a haddock.\n'
             'astIsSmall :: Bool -> Int -> Bool\n'
             'astIsSmall _ 0 = True\n'
             'astIsSmall lax t = unsafeDupablePerformIO $ do\n'
             '  flag <- readIORef ref  -- not unsafeInterleaveIO\n'
             '  return $! flag || funToAst 1 id == (t, t)\n'
             'helper = "unsafeDupablePerformIO {- -- " ++ show \'"\' '
             '++ [\'\\\'\']\n'
             '{- unsafeDupablePerformIO {- nested -} runRW# -}\n')
    vect = ('module HordeAd.Core.AstVectorize where\n'
            'mkTraceRule prefix from to =\n'
            '  unsafeDupablePerformIO $ do\n'
            '    enabled <- readIORef traceRuleEnabledRef\n'
            '    when enabled $ do\n'
            '      noDuplicate\n'
            '      hPutStrLn stderr prefix\n'
            '    return $! to\n')
    clean = [('Fresh.hs', fresh), ('Delta.hs', delta), ('Tools.hs', tools),
             ('Vect.hs', vect)]
    cases = [
        ('the clean tree', clean, []),
        ('a draw under unsafeDupablePerformIO',
         [('Fresh.hs', fresh.replace('funToAst ftk = unsafePerformIO',
                                     'funToAst ftk = unsafeDupablePerformIO'))]
         + clean[1:],
         ['Fresh.hs:11: funToAst uses unsafeDupablePerformIO, which ALLOW '
          'does not list',
          'Tools.hs:8: astIsSmall, allowed unsafeDupablePerformIO, mentions '
          'funToAst, which draws a fresh identifier without '
          'unsafePerformIO of its own']),
        ('an allowed definition calling an unprotected drawer',
         [clean[0], clean[1],
          ('Tools.hs', tools.replace('funToAst 1 id', 'funToAstIO 1 id'))]
         + clean[3:],
         ['Tools.hs:8: astIsSmall, allowed unsafeDupablePerformIO, mentions '
          'funToAstIO, which draws a fresh identifier without '
          'unsafePerformIO of its own']),
        ('an allowed definition reaching a counter directly',
         clean[:2] + [('Tools.hs', tools.replace(
             'readIORef ref', 'add unsafeAstVarCounter 1'))] + clean[3:],
         ['Tools.hs:7: astIsSmall, allowed unsafeDupablePerformIO, mentions '
          'unsafeAstVarCounter, which draws a fresh identifier without '
          'unsafePerformIO of its own']),
        ('operators made of dashes hiding nothing',
         clean + [('Op.hs', 'module Op where\n'
                   'f x = x |-- unsafeDupablePerformIO (pure 1)\n'
                   'k x = x --> unsafeDupablePerformIO (pure 1)\n')],
         ['Op.hs:2: f uses unsafeDupablePerformIO, which ALLOW does not '
          'list',
          'Op.hs:3: k uses unsafeDupablePerformIO, which ALLOW does not '
          'list']),
        ('a character literal of a double quote opening no string',
         clean + [('Ch.hs', 'module Ch where\n'
                   'g = (\'"\', unsafeDupablePerformIO (pure 1))\n')],
         ['Ch.hs:2: g uses unsafeDupablePerformIO, which ALLOW does not '
          'list']),
        ('an instance method',
         clean + [('In.hs', 'module In where\ninstance C T where\n'
                   '  m = unsafeDupablePerformIO (pure 1)\n')],
         ['In.hs:3: the instance at line 2 uses unsafeDupablePerformIO, '
          'which ALLOW does not list']),
        ('a forbidden primitive',
         clean + [('Fo.hs', 'module Fo where\n'
                   'h = runRW# (\\s -> s)\n')],
         ['Fo.hs:2: runRW# in h; no duplicable primitive but '
          'unsafeDupablePerformIO is permitted']),
        ('a stale and a vanished entry',
         clean[:2] + [('Tools.hs', tools.replace(
             'astIsSmall lax t = unsafeDupablePerformIO',
             'astIsSmall lax t = unsafePerformIO')),
                      ('Vect.hs', vect.replace('mkTraceRule', 'mkRule'))],
         ['Tools.hs:4: ALLOW lists astIsSmall, which no longer uses '
          'unsafeDupablePerformIO; drop it from ALLOW',
          'HordeAd.Core.AstVectorize: ALLOW lists '
          'HordeAd.Core.AstVectorize.mkTraceRule, which is gone; drop it '
          'from ALLOW',
          'Vect.hs:3: mkRule uses unsafeDupablePerformIO, which ALLOW does '
          'not list']),
        ('a renamed counter',
         [('Fresh.hs', fresh.replace('unsafeAstVarCounter', 'varCounter'))]
         + clean[1:],
         ['HordeAd.Core.AstFreshId: no counter unsafeAstVarCounter is '
          'defined there, so rule 2 has nothing to grow from; update '
          'COUNTERS']),
    ]
    bad = []
    for title, files, want in cases:
        got = findings(files)
        if sorted(got) != sorted(want):
            bad.append('%s:\n  got  %s\n  want %s' % (title, got, want))
    with tempfile.TemporaryDirectory() as td:
        # A file under another name: the module header decides.
        path = os.path.join(td, 'zz-against-AstFreshId.hs')
        with open(path, 'w') as fh:
            fh.write(fresh.replace('funToAst ftk = unsafePerformIO',
                                   'funToAst ftk = unsafeDupablePerformIO'))
        if main([path]) != 1:
            bad.append('a materialised file with a dupable draw did not '
                       'exit 1')
        with open(path, 'w') as fh:
            fh.write(fresh)
        if main([path]) != 0:
            bad.append('a materialised clean file did not exit 0')
        if main([os.path.join(td, 'missing.hs')]) != 2:
            bad.append('a file that cannot be opened did not exit 2')
    for b in bad:
        print('FAIL', b)
    print('self-test', 'FAILED' if bad else 'passed')
    return 1 if bad else 0


def main(argv):
    if argv == ['--self-test']:
        return self_test()
    if any(a.startswith('-') for a in argv):
        print(__doc__.split('\n\n')[1], file=sys.stderr)
        return 2
    paths = argv or tracked()
    if paths is None:
        print('git cannot list the tracked Haskell; nothing checked',
              file=sys.stderr)
        return 2
    if not paths:
        print('no Haskell file given or tracked under %s; nothing checked'
              % ', '.join(DIRS), file=sys.stderr)
        return 2
    files = []
    for p in paths:
        try:
            with open(p, encoding='utf-8') as fh:
                files.append((p, fh.read()))
        except OSError as e:
            print('cannot read %s: %s; nothing checked' % (p, e),
                  file=sys.stderr)
            return 2
    out = findings(files)
    for line in out:
        print(line)
    return 1 if out else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
