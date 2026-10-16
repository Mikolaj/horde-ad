#!/usr/bin/env python3
"""Which removed inlining pragmas change the optimised Core, and where;
and which INLINE pragmas one build did not honour.

Usage: python3 tools/pragma-calls.py DUMPS_A DUMPS_B WORKTREE_B
       python3 tools/pragma-calls.py --inline DUMPS SRCDIR
       python3 tools/pragma-calls.py --self-test

DUMPS_A and DUMPS_B are the dump trees of two builds made with
`--ghc-options="-ddump-simpl -ddump-to-file -dsuppress-uniques
-dsuppress-idinfo"` (tools/core-diff.py says how to keep two builds apart);
WORKTREE_B is the git checkout B was built from, whose uncommitted diff
removes the pragmas. For each `INLINE`, `INLINABLE` or `NOINLINE` pragma
the diff deletes, the script counts the occurrences of its target's name in
every module's Core in both builds --- bare or module-qualified, and behind
the `$s`, `$w` and similar prefixes of specialisations and workers, numbered
or not, an operator without the parentheses its pragma writes it in --- and
prints
one line per pragma: DEAD when every module's count agrees, MOVED
with the modules whose counts differ otherwise.

This is the step between removing a whole group of pragmas and bisecting
it: one build of the group sorts its pragmas into those whose removal does
nothing to the Core and those that change it, and names the modules each of
the latter reaches. DEAD means only that the counts agree, which is weaker
than identical Core: a pragma that changes what a class method's default
receives, or a function's unfolding without its call sites, can read DEAD
and still move a benchmark, as the `rsize` family behind `tsize` did
(docs/pragmas-and-flags.md). And a DEAD verdict does not make a pragma
removable: it may be dead only at today's inliner thresholds
(docs/perf-checklist.md, P). A name the diff removes a pragma from in
several modules is counted per module, `(per module)`, in the code alone,
the specialisation rules GHC prints after it left out: a token counts towards
module M's binding where M qualifies it, as Core writes a worker or a copy,
or stands unqualified in M's own dump, a copy that M's rules name as one of
an imported function excepted; where its qualifier is an alias the importing
module's source binds to M or to a module re-exporting it, one that imports M
and binds no such name; and where it stands unqualified in a module importing
M, or such a re-exporter, unqualified and binding no such name itself. A name
removed twice in one module is marked, its counts covering both.

The token counts of each dump tree are cached beside it, in
DUMPS.tokens.pickle, since tokenising 1.5 GB of Core takes a minute. The
cache records every dump file's size and modification time, the tokeniser,
the module keying and the normalisation it was counted with, and is
recounted when any of them differs, as after a rebuild into the same
builddir. Where
the directory refuses the write, the counts are made afresh on every run,
which says so.

`--inline` reads one build. For every INLINE pragma at column 0 of the
`.hs` files under SRCDIR it counts, in every module's Core but the defining
module's own, which its definition hides, two things. CALLED: the target,
its worker or its specialisation, qualified by the defining module,
or by an alias under which the calling module, its source under SRCDIR,
imports that module or one re-exporting it, called there, a copy that
module's rules name as one of an imported function excepted. COPIED: a `$s` copy the module made itself, unqualified or
qualified by that module, counted only where the module defines no function
of that name. A copy a third module made is counted for no target, so both
are a floor. A line says `inlined` where neither is left, and RECURSIVE where
the target is a binder of a `Rec {` group of its own module's Core.
A survivor is a call too unsaturated to inline, the eta-expansion question
of docs/perf-checklist.md's I1, a recursive target, one a phase holds back,
or one in a boring context, its arguments variables GHC knows nothing of and
its result returned or stored as it is, where GHC inlines only a tiny INLINE
body; RECURSIVE is I2, an INLINE that on GHC HEAD blocks worker/wrapper and
is never honoured. A name with INLINE in several modules is marked, and its
copies, which may be any of theirs, are listed once, after the lines. A
pragma inside an instance, a class or a `where` is passed over, its name
being a method's or a local's. Its own token counts, unnormalised and
of the Core alone, the specialisation rules GHC prints after it left out,
are cached beside the tree as DUMPS.rawtokens.pickle.

Exit 0 when the verdicts were printed, 2 when they could not be: a dump
tree without `.dump-simpl` files, a WORKTREE that git cannot diff, or a
diff that removes no pragma. `--inline` exits 1 when a target is called,
copied or recursive, 0 when every one is inlined, and 2 when no INLINE pragma
is found under SRCDIR or none of their modules has a dump.
"""

import collections
import contextlib
import functools
import io
import os
import pickle
import re
import shutil
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common  # noqa: E402
import dumps  # noqa: E402

# The module keying and the normalisation the cache was written with, part
# of its signature so a cache keyed or normalised the old way is recounted
# (pragma-calls-03, pragma-calls-13).
KEYS = 'dumps.module_key'
NORMALISED = 'qualifier, $ prefixes and the numbering behind them'

TOK = re.compile(r"(?:[A-Z][\w']*\.)*"
                 r"(?:\$*[\w'][\w$']*|[!#$%&*+./<=>?@\\^|~:-]+)")
PRAGMA = re.compile(r'-\s*\{-#\s*(?:INLINE|INLINABLE|INLINEABLE|NOINLINE)'
                    r'\s*(?:\[~?\d\])?\s*(\S+)\s*#-\}')
INLINE_SRC = re.compile(r'^\{-#\s*INLINE\s*(?:\[~?\d\])?\s*(\S+)\s*#-\}', re.M)
MODULE = re.compile(r'^module\s+([A-Z][\w.]*)', re.M)
# The header GHC prints above a module's specialisation rules, after its Core.
RULES = '------ Local rules for imported ids --------'
# The head of a rule's right-hand side, the copy the rule sends calls to.
RULE_RHS = re.compile(r'(?:^|\s)=\s+(\S+)')


def target(n):
    """A pragma's target as Core names it: an operator without the
    parentheses its pragma writes it in."""
    return n[1:-1] if n.startswith('(') and n.endswith(')') else n


def pragmas(wt):
    """(file, name) of every pragma the worktree's diff removes, or None
    when git cannot diff it. The diff is against HEAD, staged changes
    included, where the unstaged diff missed a staged removal
    (pragma-calls-11); a file deleted is named by its old path, its new one
    being /dev/null (pragma-calls-12)."""
    r = subprocess.run(['git', '-C', wt, 'diff', '-U0', '--no-color',
                        '--no-ext-diff', '--src-prefix=a/', '--dst-prefix=b/',
                        'HEAD'], capture_output=True, text=True)
    if r.returncode != 0:
        return None
    names, cur, old = [], None, None
    for line in r.stdout.split('\n'):
        if line.startswith('--- '):
            old = line[6:] if line.startswith('--- a/') else None
        elif line.startswith('+++ '):
            cur = line[6:] if line.startswith('+++ b/') else old
        m = PRAGMA.match(line)
        if m:
            names.append((cur, target(m.group(1))))
    return names


def normalise(tok):
    """A Core token as the name it refers to: module qualifier, the
    one-letter `$` prefixes of specialisations and workers and, behind
    those, the numbering of a worker or a copy dropped, as index() drops
    it: kept, $sf1 counted for f1 and not f (pragma-calls-13)."""
    tok = re.sub(r"^(?:[A-Z][\w']*\.)+", '', tok)
    m = re.match(r'(?:\$[a-z])+', tok)
    return re.sub(r'[0-9]+$', '', tok[m.end():]) if m else tok


def signature(root):
    """What a cached count must match: the tokeniser, the module keying, the
    normalisation, and every dump file's path, size and modification time.
    A dump is a file
    ending in .dump-simpl, gzipped or not, and not the .dump-simpl-stats
    beside it (pragma-calls-04)."""
    files = []
    for p, _ in dumps.walk(root, '.dump-simpl'):
        st = os.stat(p)
        files.append((p, st.st_size, st.st_mtime_ns))
    return TOK.pattern, KEYS, NORMALISED, files


def code(txt):
    """A dump's Core without the specialisation rules GHC prints after it,
    whose left-hand sides name the functions the rules replace and are no
    calls of them (pragma-calls-06)."""
    return txt.split('\n' + RULES, 1)[0]


def load(root, raw=False):
    """Module key -> Counter of normalised tokens, or with raw of the tokens
    of the code alone as they print, cached beside root where it can be."""
    cache = root.rstrip('/') + ('.rawtokens.pickle' if raw else
                                '.tokens.pickle')
    sig = signature(root)
    key = sig + ('code',) if raw else sig
    try:
        with open(cache, 'rb') as fh:
            got = pickle.load(fh)
        if isinstance(got, tuple) and len(got) == 2 and got[0] == key:
            return got[1]
    except (OSError, pickle.UnpicklingError, EOFError):
        pass
    out = {}
    for p, _, _ in sig[-1]:
        txt = dumps.read_text(p)
        counts = collections.Counter(TOK.findall(code(txt) if raw else txt))
        c = collections.Counter()
        for t, n in counts.items():
            c[t if raw else normalise(t)] += n
        out[dumps.module_key(p, root, '.dump-simpl')] = c
    if out:
        # A tree whose directory refuses the write is counted afresh each
        # run rather than not at all (pragma-calls-05).
        try:
            with open(cache, 'wb') as fh:
                pickle.dump((key, out), fh)
        except OSError as e:
            print(f'pragma-calls: could not cache the counts at {cache} '
                  f'({e.strerror}); counted afresh', file=sys.stderr)
    return out


IMPORT = re.compile(r'^import\s+(qualified\s+)?([A-Z][\w.]*)(\s+qualified)?'
                    r'(?:\s+as\s+([A-Z][\w.]*))?(\s+hiding)?\s*(\(\s*\))?',
                    re.M)
# A raw Core token: its qualifier, its `$` prefixes and the rest.
RAW = re.compile(r"((?:[A-Z][\w']*\.)*)((?:\$[a-z])*)(.*)")


def hs_files(src):
    """[(path, module, text)] of every .hs file under src, build directories
    and hidden ones passed over."""
    out = []
    for dp, ds, fs in os.walk(src):
        ds[:] = [d for d in ds if not d.startswith(('.', 'dist'))]
        for f in fs:
            if f.endswith('.hs'):
                p = os.path.join(dp, f)
                with open(p, errors='replace') as fh:
                    txt = fh.read()
                m = MODULE.search(txt)
                out.append((p, m.group(1) if m else 'Main', txt))
    return out


def sources(wt):
    """Module name -> text of every .hs file under the worktree."""
    return {mod: txt for _, mod, txt in hs_files(wt)}


def scope(txt):
    """(alias -> {module}, [module imported unqualified]) of a module's text;
    an import of () brings no names."""
    al, unq = collections.defaultdict(set), []
    for m in IMPORT.finditer(txt):
        al[m.group(4) or m.group(2)].add(m.group(2))
        if not (m.group(1) or m.group(3)) and not m.group(6):
            unq.append(m.group(2))
    return al, unq


def defines(txt, n):
    """Whether a module's text binds n at column 0, by a signature or an
    equation, an operator's infix one included."""
    e = re.escape(n)
    return re.search(rf"^(?:\(?{e}\)?\s|[\w']+\s+{e}\s.*=)", txt, re.M) \
        is not None


def index(raw):
    """Module key -> {base: [(qualifier, count, unqualified token)]} of raw
    token counts, a base being a token without its qualifier, its `$`
    prefixes and, behind those, the numbering of a worker or a copy."""
    out = {}
    for k, c in raw.items():
        d = collections.defaultdict(list)
        for t, v in c.items():
            q, pre, rest = RAW.fullmatch(t).groups()
            d[re.sub(r'[0-9]+$', '', rest) if pre else rest].append(
                (q.rstrip('.'), v, pre + rest))
        out[k] = d
    return out


@functools.lru_cache(maxsize=None)
def own_copies(root, mod):
    """The copies mod's dumps under root name as ones of imported functions,
    unqualified: no specialisation of mod's own binding (pragma-calls-08)."""
    path = mod.replace('.', '/')
    return frozenset(''.join(RAW.fullmatch(t).groups()[1:])
                     for p, k in dumps.walk(root, '.dump-simpl')
                     if k == path or k.endswith('/' + path)
                     for t in imported_copies(dumps.read_text(p)))


def referrer(srcs, scopes, mod, n):
    """refers(module, qualifier): whether a token so qualified in that
    module's Core refers to mod's binding of n, by the rules the docstring
    gives; scopes are scope() of srcs."""
    def reaches(x):
        if x == mod:
            return True
        t = srcs.get(x)
        return (t is not None and not defines(t, n)
                and mod in set().union(*scopes[x][0].values()))

    def refers(k, q):
        if q == mod:
            return True
        if k not in srcs:
            return False
        if not q:
            if k == mod:
                return True
            return not defines(srcs[k], n) and any(map(reaches, scopes[k][1]))
        return any(map(reaches, scopes[k][0].get(q, ())))

    return refers


def module_name(k, srcs):
    """The module of srcs a dump's key names, or its last component."""
    parts = k.split('/')
    return next(('.'.join(parts[i:]) for i in range(len(parts))
                 if '.'.join(parts[i:]) in srcs), parts[-1])


def per_module(ia, ib, srcs, mod, n, copies=(set(), set())):
    """{module key: (count in A, count in B)} of the tokens referring to
    mod's binding of n, by the rules the docstring gives; copies are those
    of own_copies in A and in B."""
    refers = referrer(srcs, {m: scope(t) for m, t in srcs.items()}, mod, n)

    def copy(km, q, u, cs):
        return u in cs and (q == mod or not q and km == mod)

    out = {}
    for k in set(ia) | set(ib):
        km = module_name(k, srcs)
        out[k] = tuple(sum(v for q, v, u in t.get(k, {}).get(n, ())
                           if refers(km, q) and not copy(km, q, u, cs))
                       for t, cs in zip((ia, ib), copies))
    return out


def verdicts(a, b, names, per=None):
    """One line per removed pragma; per, (raw counts of A, raw counts of B,
    the worktree's sources, file -> module, the root of A, the root of B),
    counts a name removed in several modules module by module."""
    dup = collections.Counter(n for _, n in names)
    dupf = collections.Counter(names)
    ia, ib = (index(per[0]), index(per[1])) if per else (None, None)
    lines = []
    for f, n in names:
        moved = []
        if per and dup[n] > dupf[(f, n)]:
            mod = per[3].get(f)
            counts = per_module(ia, ib, per[2], mod, n,
                                (own_copies(per[4], mod),
                                 own_copies(per[5], mod)))
            for k in sorted(counts):
                ca, cb = counts[k]
                if ca != cb:
                    moved.append(f'{k.split("/")[-1]} {ca}->{cb}')
            amb = ' (per module)'
            if dupf[(f, n)] > 1:
                amb = ' (per module, name not unique in it)'
        else:
            for k in sorted(set(a) | set(b)):
                ca, cb = a.get(k, {}).get(n, 0), b.get(k, {}).get(n, 0)
                if ca != cb:
                    moved.append(f'{k.split("/")[-1]} {ca}->{cb}')
            amb = ' (name not unique)' if dup[n] > 1 else ''
        more = f' +{len(moved) - 6}' if len(moved) > 6 else ''
        lines.append(f'{f}\t{n}{amb}\t'
                     + ('DEAD' if not moved else
                        'MOVED ' + ', '.join(moved[:6]) + more))
    return lines


def inline_pragmas(src):
    """[(file, module, name)] of every INLINE pragma at column 0 of the .hs
    files under src, build directories and hidden ones passed over."""
    out = []
    for p, mod, txt in hs_files(src):
        for m in INLINE_SRC.finditer(txt):
            out.append((os.path.relpath(p, src), mod, target(m.group(1))))
    return sorted(out)


def rec_binders(txt):
    """The names bound at column 0 inside the `Rec {` groups of a dump,
    module qualifiers dropped."""
    out, inrec = set(), False
    for line in txt.split('\n'):
        if line.startswith('Rec {'):
            inrec = True
        elif line.startswith('end Rec'):
            inrec = False
        elif inrec and line and not line[0].isspace():
            out.add(re.sub(r"^(?:[A-Z][\w']*\.)+", '', line.split()[0]))
    return out


def imported_copies(txt):
    """The copies a dump's module made of imported functions, the right-hand
    sides of the rules GHC prints after its Core: a `$s` name there is no
    specialisation of the module's own function of that name
    (pragma-calls-07)."""
    rules = txt.split('\n' + RULES, 1)
    return set(RULE_RHS.findall(rules[1])) if len(rules) == 2 else set()


def inline_census(root, tokens, prags, srcs=None):
    """(lines, number of targets left behind or recursive, number whose
    module has a dump); srcs, module name -> text, resolve the aliases
    a calling module imports under (pragma-calls-09)."""
    srcs = srcs or {}
    scopes = {m: scope(t) for m, t in srcs.items()}
    paths = dict((k, p) for p, k in dumps.walk(root, '.dump-simpl'))
    dup = collections.Counter(n for _, _, n in prags)
    lines, shared, flagged, seen = [], {}, 0, 0
    for f, mod, n in prags:
        path = mod.replace('.', '/')
        own = [k for k in tokens if k == path or k.endswith('/' + path)]
        if not own:
            lines.append(f'{f}\t{n}\tNO DUMP of {mod}')
            continue
        seen += 1
        e = re.escape(n)
        refers = referrer(srcs, scopes, mod, n)
        # Digits only behind a prefix, as index() reads them: a bare
        # M.rgather1 is a sibling, no call of rgather (pragma-calls-10).
        called_re = re.compile(rf"((?:[A-Z][\w']*\.)+)"
                               rf"(?:(?:\$[sw])+{e}[0-9]*|{e})")
        copy_re = re.compile(rf"((?:[A-Z][\w']*\.)*)\$s(?:\$[sw])*{e}[0-9]*")
        texts = [dumps.read_text(paths[k]) for k in own]
        foreign = set().union(*map(imported_copies, texts))
        called, copied = [], []
        for k in sorted(tokens):
            if k in own:
                continue
            here, c = k.rsplit('/', 1)[-1], tokens[k]
            km = module_name(k, srcs)
            ncall = 0
            for t, v in c.items():
                m = called_re.fullmatch(t)
                if m and t not in foreign and refers(km, m.group(1)[:-1]):
                    ncall += v
            if ncall:
                called.append(f'{here} {ncall}')
            # A module defining a function of that name copies its own.
            if any(t.endswith('.' + n) and t[:-len(n) - 1].rsplit('.', 1)[-1]
                   == here for t in c):
                continue
            ncopy = 0
            for t, v in c.items():
                m = copy_re.fullmatch(t)
                if m and m.group(1).rstrip('.').rsplit('.', 1)[-1] in ('', here):
                    ncopy += v
            if ncopy:
                copied.append(f'{here} {ncopy}')
        rec = any(n in rec_binders(t) for t in texts)
        parts = []
        if called:
            parts.append('CALLED ' + listed(called))
        if copied and dup[n] > 1:
            shared[n] = 'COPIED ' + listed(copied)
        elif copied:
            parts.append('COPIED ' + listed(copied))
        if rec:
            parts.append('RECURSIVE')
        amb = ' (name not unique)' if dup[n] > 1 else ''
        lines.append(f'{f}\t{n}{amb}\t' + (', '.join(parts) or 'inlined'))
        flagged += bool(parts) or n in shared
    if shared:
        lines.append('== copies of names with INLINE in several modules')
        lines += [f'{n}\t{v}' for n, v in sorted(shared.items())]
    return lines, flagged, seen


def listed(xs):
    return ', '.join(xs[:6]) + (f' +{len(xs) - 6}' if len(xs) > 6 else '')


def inline_self_test(td):
    """A source tree with INLINE targets called, copied, inlined and
    recursive, one name in two modules, one module without a dump, and
    pragmas that are INLINABLE, indented or in a build directory; and one
    dump tree of it, with a copy qualified by a third module, a module
    copying a function of its own of the same name, a target's module
    copying an imported function of the same name, called elsewhere,
    and calls under two aliases, one of the target's module and one
    of a module binding the name itself."""
    bad = []
    src = os.path.join(td, 'isrc')
    os.makedirs(os.path.join(src, 'dist-newstyle'))
    for name, text in (
            ('M.hs', 'module M where\n{-# INLINE f #-}\nf x = x\n'
                     '{-# INLINE g #-}\ng x = x\n{-# INLINE k #-}\nk = 1\n'
                     '{-# INLINE [1] r #-}\n'
                     'r x = r x\n{-# INLINABLE h #-}\nh x = x\n'
                     'instance C T where\n  {-# INLINE m #-}\n  m = id\n'),
            ('N.hs', '-- a module\nmodule N (f) where\n{-# INLINE f #-}\nf = 1\n'),
            ('P.hs', 'module P where\n{-# INLINE p #-}\np = 1\n'),
            ('User2.hs', 'module User2 where\nimport M\ng x = x\n'),
            ('User3.hs', 'module User3 where\nimport qualified M as Q\n'
                         'import qualified User2 as Q2\n'),
            ('dist-newstyle/Q.hs', 'module Q where\n{-# INLINE q #-}\nq = 1\n')):
        with open(os.path.join(src, name), 'w') as fh:
            fh.write(text)
    tree = os.path.join(td, 'I')
    for rel, text in (
            ('build/src/M.dump-simpl',
             'Rec {\nM.r = \\ x -> M.r x\nend Rec }\n\nM.f = \\ x -> x\n'
             'M.g = \\ x -> x\nM.$sg1 = \\ x -> x\n\n'
             # M's copy of an imported g, called by User (pragma-calls-07).
             + RULES + '\n"SPEC/M g @T"\n    forall ($dC :: C T).\n'
             '      G.g @T $dC\n      = M.$sg1\n'),
            ('build/src/N.dump-simpl', 'N.f = 1\n'),
            ('build/src/User.dump-simpl',
             'User.u = \\ y -> M.f y\nUser.$sf1 = \\ y -> y\n'
             'User.v = N.$wf 2\nUser.w = Other.$sg 3\nUser.x = User.$sk2\n'
             'User.z = M.$sg1 4\n\n'
             # A rule naming f and its copy, no call of either
             # (pragma-calls-06).
             + RULES + '\n"SPEC/User f"\n    forall. M.f = User.$sf1\n'),
            ('build/src/User2.dump-simpl',
             'User2.g = \\ x -> x\nUser2.$sg1 = User2.g 1\n'),
            # M's g called under an alias, and User2's own g under another
            # (pragma-calls-09).
            ('build/src/User3.dump-simpl',
             'User3.y = \\ z -> Q.g z\nUser3.w = \\ z -> Q2.g z\n')):
        p = os.path.join(tree, rel)
        os.makedirs(os.path.dirname(p), exist_ok=True)
        with open(p, 'w') as fh:
            fh.write(text)
    prags = inline_pragmas(src)
    want = [('M.hs', 'M', 'f'), ('M.hs', 'M', 'g'), ('M.hs', 'M', 'k'),
            ('M.hs', 'M', 'r'), ('N.hs', 'N', 'f'), ('P.hs', 'P', 'p')]
    if prags != want:
        bad.append(f'INLINE pragmas found: {prags}')
    # A cache of the whole dumps, as written before the rules were left
    # out, must be recounted.
    with open(tree + '.rawtokens.pickle', 'wb') as fh:
        pickle.dump((signature(tree), {'src/User': collections.Counter(
            {'M.f': 9})}), fh)
    got, flagged, seen = inline_census(tree, load(tree, raw=True), prags,
                                       sources(src))
    want = ['M.hs\tf (name not unique)\tCALLED User 1',
            'M.hs\tg\tCALLED User3 1', 'M.hs\tk\tCOPIED User 1',
            'M.hs\tr\tRECURSIVE',
            'N.hs\tf (name not unique)\tCALLED User 1',
            'P.hs\tp\tNO DUMP of P',
            '== copies of names with INLINE in several modules',
            'f\tCOPIED User 1']
    if got != want or flagged != 5 or seen != 5:
        bad.append(f'census ({flagged} flagged, {seen} seen):\n  '
                   + '\n  '.join(got))
    if main(['--inline', tree, src]) != 1:
        bad.append('a census with survivors did not exit 1')
    empty = os.path.join(td, 'iempty')
    os.makedirs(empty)
    if main(['--inline', empty, src]) != 2:
        bad.append('--inline over a tree without dumps did not exit 2')
    if main(['--inline', tree, empty]) != 2:
        bad.append('--inline over sources without INLINE did not exit 2')
    return bad


def per_module_self_test(td, git):
    """A name whose pragma the diff removes in two modules, M and N: a user
    reaching M's through an alias of a module re-exporting it and N's
    unqualified and through N's worker, each counted towards its own; two
    modules whose own f counts towards neither: one importing N
    unqualified, one importing M and reached through an alias; and M's
    copy of N's f, called by the user, counted towards neither."""
    bad = []
    repo = os.path.join(td, 'repo2')
    os.makedirs(repo)
    srcs = {'M.hs': 'module M where\n{-# INLINE f #-}\nf x = x\n',
            'N.hs': 'module N where\n{-# INLINE f #-}\nf x = x\n',
            'R.hs': 'module R (f) where\nimport M (f)\n',
            # A module importing M and binding f of its own, no re-exporter.
            'S.hs': 'module S where\nimport qualified M\nf = 4\n',
            'U.hs': 'module U where\nimport qualified R as X\nimport N\n'
                    'import qualified S as Y\nu = X.f 1\nv = f 2\ny = Y.f\n',
            # A module importing N unqualified and binding f of its own.
            'W.hs': 'module W where\nimport N hiding (f)\nf = 3\nw = f\n'}
    for name, text in srcs.items():
        with open(os.path.join(repo, name), 'w') as fh:
            fh.write(text)
    g = git[:2] + [repo] + git[3:]
    for cmd in (['init', '-q'], ['add', '.'],
                ['commit', '-q', '-m', 'x', '--no-gpg-sign']):
        subprocess.run(g + cmd, check=True, capture_output=True)
    for name in ('M.hs', 'N.hs'):
        with open(os.path.join(repo, name), 'w') as fh:
            fh.write(srcs[name].replace('{-# INLINE f #-}\n', ''))
    for rel, text in (('A2/build/M.dump-simpl', 'f = \\ x -> x\n'),
                      ('A2/build/N.dump-simpl', 'f = \\ x -> x\n'),
                      ('A2/build/U.dump-simpl', 'u = 1\nv = 2\n'),
                      # M's copy of N's f, called by U, which is no
                      # reference to M's own (pragma-calls-08).
                      ('B2/build/M.dump-simpl',
                       'f = \\ x -> x\nM.$sf3 = \\ x -> x\n\n' + RULES
                       + '\n"SPEC/M f @T"\n    forall ($dC :: C T).\n'
                       '      N.f @T $dC\n      = M.$sf3\n'),
                      ('B2/build/N.dump-simpl', 'f = \\ x -> x\n$wf = 1\n'),
                      ('B2/build/U.dump-simpl',
                       'u = X.f 1\nv = f 2\nw = N.$wf 3\ny = Y.f\n'
                       'z = M.$sf3 5\n'),
                      ('A2/build/W.dump-simpl', 'f = 3\nw = f\n'),
                      ('B2/build/W.dump-simpl', 'f = 3\nw = f\nx = f\n')):
        p = os.path.join(td, rel)
        os.makedirs(os.path.dirname(p), exist_ok=True)
        with open(p, 'w') as fh:
            fh.write(text)
    out = io.StringIO()
    with contextlib.redirect_stdout(out):
        code = main([os.path.join(td, 'A2'), os.path.join(td, 'B2'), repo])
    want = ['M.hs\tf (per module)\tMOVED U 0->1',
            'N.hs\tf (per module)\tMOVED N 1->2, U 0->2']
    if code != 0 or out.getvalue().split('\n')[:-1] != want:
        bad.append('per-module verdicts:\n  '
                   + '\n  '.join(out.getvalue().split('\n')))
    return bad


def self_test():
    """A git repository whose diff removes two pragmas, and two dump trees
    in which one target's call sites change and the other's do not."""
    import tempfile
    # git -C does not override an inherited GIT_DIR, which took the scratch
    # repository's commits to the caller's (pragma-calls-14).
    for k in common.GIT_LOCATION:
        os.environ.pop(k, None)
    bad = []
    with tempfile.TemporaryDirectory() as td:
        repo = os.path.join(td, 'repo')
        os.makedirs(repo)
        src = ('module M where\n{-# INLINE f #-}\nf x = x\n'
               '{-# INLINE [1] g #-}\ng x = x\n{-# NOINLINE h #-}\nh x = x\n'
               '{-# INLINE (+++) #-}\nxs +++ ys = xs\n')
        with open(os.path.join(repo, 'M.hs'), 'w') as fh:
            fh.write(src)
        git = ['git', '-C', repo, '-c', 'user.name=t', '-c', 'user.email=t@t']
        for cmd in (['init', '-q'], ['add', 'M.hs'],
                    ['commit', '-q', '-m', 'x', '--no-gpg-sign']):
            subprocess.run(git + cmd, check=True, capture_output=True)
        with open(os.path.join(repo, 'M.hs'), 'w') as fh:
            fh.write(src.replace('{-# INLINE f #-}\n', '')
                        .replace('{-# INLINE [1] g #-}\n', '')
                        .replace('{-# INLINE (+++) #-}\n', ''))
        files = {
            'A/build/src/M.dump-simpl': 'f = \\ x -> x\ng = \\ x -> x\n',
            'A/build/src/User.dump-simpl': 'u = \\ y -> y\nv = M.g 1\n',
            'B/build/src/M.dump-simpl': 'f = \\ x -> x\ng = \\ x -> x\n',
            'B/build/src/User.dump-simpl':
                'u = \\ y -> M.f y\nw = $sf 2\nv = M.g 1\nx = M.+++ y y\n',
            # Trees written with -dumpdir, no build/ directory in their paths
            # (pragma-calls-03), one module with the .dump-simpl-stats file
            # -ddump-simpl-stats writes beside its dump (pragma-calls-04).
            'C/src/M.dump-simpl': 'f = \\ x -> x\ng = \\ x -> x\n',
            'C/src/User.dump-simpl': 'u = \\ y -> y\nv = M.g 1\n',
            'D/src/M.dump-simpl': 'f = \\ x -> x\ng = \\ x -> x\n',
            'D/src/User.dump-simpl': 'u = \\ y -> y\nv = M.g 1\n',
            'D/src/User.dump-simpl-stats': '1 UnfoldingDone\n  2 M.g M.g\n',
        }
        for rel, text in files.items():
            os.makedirs(os.path.dirname(os.path.join(td, rel)), exist_ok=True)
            with open(os.path.join(td, rel), 'w') as fh:
                fh.write(text)
        names = pragmas(repo)
        if names != [('M.hs', 'f'), ('M.hs', 'g'), ('M.hs', '+++')]:
            bad.append(f'pragmas the diff removes: {names}')
        got = verdicts(load(os.path.join(td, 'A')),
                       load(os.path.join(td, 'B')), names or [])
        want = ['M.hs\tf\tMOVED User 0->2', 'M.hs\tg\tDEAD',
                'M.hs\t+++\tMOVED User 0->1']
        if got != want:
            bad.append('verdicts:\n  ' + '\n  '.join(got))
        if not os.path.exists(os.path.join(td, 'A.tokens.pickle')):
            bad.append('token counts not cached')
        # A dump rebuilt in place, its cache left from the run above.
        with open(os.path.join(td, 'B/build/src/User.dump-simpl'), 'a') as fh:
            fh.write('z = M.g 2\n')
        if load(os.path.join(td, 'B')).get('src/User', {}).get('g') != 2:
            bad.append('a dump rebuilt under its cache was read at the '
                       'cached counts')
        # A cache from before the keying entered the signature, which a run
        # over C then keyed by each dump's whole path, matching in all else,
        # must be recounted.
        croot = os.path.join(td, 'C')
        nroot = os.path.join(td, 'N')
        shutil.copytree(croot, nroot)
        with open(croot + '.tokens.pickle', 'wb') as fh:
            pickle.dump(((TOK.pattern, NORMALISED, signature(croot)[-1]),
                         {os.path.join(croot, 'src/User'):
                          collections.Counter({'g': 9})}), fh)
        got = verdicts(load(croot), load(os.path.join(td, 'D')), names or [])
        want = ['M.hs\tf\tDEAD', 'M.hs\tg\tDEAD', 'M.hs\t+++\tDEAD']
        if got != want:
            bad.append('verdicts over -dumpdir trees, one module with a '
                       'stats file:\n  ' + '\n  '.join(got))
        # So must one counted before the numbering was normalised
        # (pragma-calls-13).
        with open(nroot + '.tokens.pickle', 'wb') as fh:
            pickle.dump(((TOK.pattern, KEYS, signature(nroot)[-1]),
                         {'src/User': collections.Counter({'g': 9})}), fh)
        if load(nroot).get('src/User', {}).get('g') != 1:
            bad.append('a cache normalised the old way was read')
        # A corrupt cache is counted afresh, and a tree whose directory
        # refuses the write is counted without one (pragma-calls-05).
        cc = os.path.join(td, 'cc')
        shutil.copytree(os.path.join(td, 'A'), cc)
        with open(cc + '.tokens.pickle', 'wb') as fh:
            fh.write(b'not a pickle')
        try:
            got = load(cc)
        except Exception as e:
            got = {}
            bad.append(f'a corrupt cache stopped the run: {e!r}')
        if got.get('src/User', {}).get('g') != 1:
            bad.append('a corrupt cache was not counted afresh')
        ro = os.path.join(td, 'ro')
        shutil.copytree(os.path.join(td, 'A'), os.path.join(ro, 'A'))
        os.chmod(ro, 0o555)
        err = io.StringIO()
        try:
            with contextlib.redirect_stderr(err):
                got = load(os.path.join(ro, 'A'))
        except Exception as e:
            got = {}
            bad.append(f'a refused cache write stopped the run: {e!r}')
        finally:
            os.chmod(ro, 0o755)
        if (got.get('src/User', {}).get('g') != 1
                or 'could not cache' not in err.getvalue()):
            bad.append('a tree whose directory refuses the write was not '
                       f'counted, or not said to be: {err.getvalue()!r}')
        bad += per_module_self_test(td, git)
        empty = os.path.join(td, 'empty')
        os.makedirs(empty)
        if main([os.path.join(td, 'A'), empty, repo]) != 2:
            bad.append('a tree without dumps did not exit 2')
        if main([os.path.join(td, 'A'), os.path.join(td, 'B'), td]) != 2:
            bad.append('a directory git cannot diff did not exit 2')
        bad += inline_self_test(td)
    for b in bad:
        print('FAIL', b)
    print('self-test', 'FAILED' if bad else 'passed')
    return 1 if bad else 0


def main(argv):
    if argv == ['--self-test']:
        return self_test()
    if len(argv) == 3 and argv[0] == '--inline':
        tokens = load(argv[1], raw=True)
        if not tokens:
            print(f'no .dump-simpl file under {argv[1]}; was it built with '
                  '-ddump-simpl -ddump-to-file?', file=sys.stderr)
            return 2
        prags = inline_pragmas(argv[2])
        if not prags:
            print(f'no INLINE pragma at column 0 of a .hs file under '
                  f'{argv[2]}', file=sys.stderr)
            return 2
        lines, flagged, seen = inline_census(argv[1], tokens, prags,
                                             sources(argv[2]))
        if not seen:
            print(f'no module of an INLINE pragma under {argv[2]} has a '
                  f'dump under {argv[1]}', file=sys.stderr)
            return 2
        print('\n'.join(lines))
        return 1 if flagged else 0
    if len(argv) != 3:
        print(__doc__.split('\n\n')[1], file=sys.stderr)
        return 2
    names = pragmas(argv[2])
    if names is None:
        print(f'git cannot diff {argv[2]}', file=sys.stderr)
        return 2
    if not names:
        print(f'the diff of {argv[2]} removes no pragma', file=sys.stderr)
        return 2
    trees = []
    for d in argv[:2]:
        t = load(d)
        if not t:
            print(f'no .dump-simpl file under {d}; was it built with '
                  '-ddump-simpl -ddump-to-file?', file=sys.stderr)
            return 2
        trees.append(t)
    print('\n'.join(verdicts(*trees, names, per_args(argv, names))))
    return 0


def per_args(argv, names):
    """verdicts' per for a run over two dump trees and a worktree, or None
    where no name is removed in more than one module."""
    if len({n for _, n in names}) == len(set(names)):
        return None
    srcs, mods = sources(argv[2]), {}
    for f, _ in names:
        with open(os.path.join(argv[2], f), errors='replace') as fh:
            m = MODULE.search(fh.read())
        mods[f] = m.group(1) if m else 'Main'
    return (load(argv[0], raw=True), load(argv[1], raw=True), srcs, mods,
            argv[0], argv[1])


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
