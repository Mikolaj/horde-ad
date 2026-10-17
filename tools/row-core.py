#!/usr/bin/env python3
"""Which rows of orthotope's specialisation benchmark have optimised Core
that differs between two builds, and where.

Usage: python3 tools/row-core.py rows DUMPS_A DUMPS_B SRC [--sample K]
       python3 tools/row-core.py diff [--summed] [--ops K] DUMPS_A DUMPS_B SRC
                                      MODULE SIZE KIND NAME
       python3 tools/row-core.py dump DUMPS SRC MODULE SIZE KIND NAME OUT
       python3 tools/row-core.py nodes [--width W] CLOSURE_A CLOSURE_B SECTION
       python3 tools/row-core.py tokens [--width W] CLOSURE_A CLOSURE_B MODULE
                                        NODE_A NODE_B SECTION
       python3 tools/row-core.py --self-test

Each DUMPS is the dump tree of a build of the benchmark made as
tools/pragma-calls.py describes (`-ddump-simpl -ddump-to-file
-dsuppress-uniques -dsuppress-idinfo`), a cabal build directory or a
`-dumpdir` tree, `.gz` dumps read as well; a module's name is the
capitalised end of its dump's path, below the last `build/` (tools/dumps.py).
SRC is a source tree whose `.hs` files' imports resolve the qualifiers the
Core writes, the benchmark's and the library's (tools/pragma-calls.py's
`scope`). The benchmark's own code is the modules whose dumps lie in a
directory holding a dump with a `Call.Call`; the others are the library.

A row is a `Call.Call @a @b d1 .. d5 name f x g` of the benchmark: its
forced function, the harness's `rnf` of f's result, is f with the NFData
dictionary d2, and its summing function is g. Its name is the first string
literal reached from name, and its size and kind are those of the
`ops{B,S,U}{Large,Small,Empty}` lists that reach it, `?` where none does.
A top-level binding's hash covers its text --- comments dropped, among
them GHC's `-- RHS size` comments, whose wrapped continuation lines would
otherwise end the binding above with the size of the one after it
(row-core-01); `Rec {` markers and layout dropped; a local binder renamed
by its base and its order of first appearance --- refined over its
references to other dumped bindings for 40 rounds; references outside the
dumps stay literal. Which binders a binding reaches is read per module, a
binder of one module never standing for another's of the same name
(row-core-02). The renaming follows a binder's first appearance, not its
binding site, so two builds whose dumps name local binders apart in one
and alike in the other can mark a row `differs` though its Core is the same
up to renaming: orthotope's Dynamic small boxed `maximumA`, its text
differing only in a join point renamed `$w$j_2` in one build and
`$w$j_1` in the other. Within a text the renaming is one to one,
so this error makes a row `differs` and never `same`.

rows prints a TSV line per row: module, size, kind, name, and for the
forced and the summing function `same`, `literals` (equal with numeric
literals blanked, a call stack's line moving, say) or `differs`, first
following the benchmark's own code alone and naming the library bindings
it reaches, then following every reference; then the counts of rows under
that key where they are not one each, and the library bindings whose
change alone moved the forced function's full hash. `--sample K` prints the
first K rows of DUMPS_A instead. A key in one build alone is UNMATCHED.

diff prints, for one row, the first node of the forced function's closure
(the summing function's with `--summed`), in breadth-first order over the
benchmark's own code, that differs in more than literals, with its first K
token differences (6). dump writes one row's closures to OUT, each node a
paragraph, `##### FORCED` and `##### SUMMED` heading the two. nodes
matches the nodes of a SECTION (FORCED or SUMMED) of two such files by
their text, local names, node numbers and binder numbers normalised, and
prints those of each side the other lacks; tokens diffs one node of each,
casts, type arguments and unit qualifiers dropped as well. W bounds the
text printed of a node (600) or a difference (400).

Exit 0 when the comparison was printed or the file written, 2 when it could
not be: a tree with no `.dump-simpl` dump, dumps with no `Call.Call`, a
row or a node not found, or an unreadable input.
"""

import collections
import contextlib
import difflib
import hashlib
import importlib.util
import io
import os
import re
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import dumps  # noqa: E402

sys.dont_write_bytecode = True
_spec = importlib.util.spec_from_file_location(
    'pragma_calls', os.path.join(HERE, 'pragma-calls.py'))
pc = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(pc)

ROUNDS = 40
# A resolved reference's place in a text; Core carries no NUL.
REF = '\x00'
LISTS = re.compile(r'ops([BSU])(Large|Small|Empty)')
TOP = re.compile(r'^([^\s()\[\]{},;=]+)\s+(?:::|=)', re.M)
NAME = re.compile(r"(?:[A-Z][\w']*\.)+[^\s()\[\]{},;@\\]+|[a-z_$][\w$'#]*")
QUAL = re.compile(r"((?:[A-Z][\w']*\.)+)(.+)")
LIT = re.compile(r'(?<![\w$#.])\d+(?:\.\d+)?(?:e-?\d+)?(?:##?)?(?![\w$])')
# A unit qualifier, `pkg-version-hash:` before a module, as Core writes it
# and as a closure's renaming leaves it, `ghc_0-internal_0:`.
UNITQ = re.compile(r"(?<![\w.'])[a-z][\w]*(?:-[\w.]+)*:(?=[A-Z])")


class Unreadable(Exception):
    """The run cannot happen; the message says why."""


# The Core reading, from tools/ under the specialisation benchmark's study.

def bindings(text):
    """Top-level binder -> its text, the type signature included."""
    starts = [(m.start(), m.group(1)) for m in TOP.finditer(text)]
    out = {}
    for i, (s, nm) in enumerate(starts):
        e = starts[i + 1][0] if i + 1 < len(starts) else len(text)
        out[nm] = out.get(nm, '') + text[s:e]
    return out


def atom(t, i):
    """The atom of Core text t at i, whitespace skipped: (text, next)."""
    while t[i].isspace():
        i += 1
    if t[i] in '([' or t[i] == "'" and t[i + 1] in '([':
        d, j = 0, i + (t[i] == "'")
        while True:
            if t[j] in '([':
                d += 1
            elif t[j] in ')]':
                d -= 1
                if d == 0:
                    return t[i:j + 1], j + 1
            j += 1
    if t[i] == '"':
        j = t.index('"', i + 1)
        while t[j + 1] == '#':
            j += 1
        return t[i:j + 1], j + 1
    j = i
    while j < len(t) and not t[j].isspace() and t[j] not in '()[]':
        j += 1
    return t[i:j], j


def call_args(t, i):
    """The type and term arguments after the constructor ending at i."""
    tys, terms = [], []
    while len(terms) < 9:
        k = i
        while t[k].isspace():
            k += 1
        if t[k] == '@':
            a, i = atom(t, k + 1)
            tys.append(a)
        else:
            a, i = atom(t, k)
            terms.append(a)
    return tys, terms


def body(binds, nm):
    b = binds.get(nm, '')
    k = max(b.find('\n' + nm + ' ='), b.find('\n' + nm + '\n  ='))
    return b[k:] if k >= 0 else b


def reach(binds, text, cache):
    """Top-level binders of binds reached from text; cache holds each
    binder's names, and is the module's own."""
    names = set(NAME.findall(text))
    seen, todo = set(), [n for n in names if n in binds]
    while todo:
        n = todo.pop()
        if n in seen:
            continue
        seen.add(n)
        if n not in cache:
            cache[n] = set(NAME.findall(body(binds, n)))
        todo.extend(m for m in cache[n] if m in binds and m not in seen)
    return seen


def module_name(key):
    """The capitalised end of a dump's key, as a module name."""
    parts = key.split('/')
    i = len(parts)
    while i > 0 and re.fullmatch(r"[A-Z][\w']*", parts[i - 1]):
        i -= 1
    return '.'.join(parts[i:]) or key


def load(tree, root):
    """({module: (binds, text)}, {module: scope}, the benchmark's
    modules)."""
    if not os.path.isdir(tree):
        raise Unreadable(f'{tree}: no such directory')
    if not os.path.isdir(root):
        raise Unreadable(f'{root}: no such source directory')
    mods, dirs = {}, {}
    for p, key in dumps.walk(tree, '.dump-simpl'):
        m = module_name(key)
        t = dumps.read_text(p)
        t = re.sub(r'(?<![\w.:])' + re.escape(m) + r'\.(?=[a-z_$])', '', t)
        # A size comment GHC wraps continues on indented lines, which
        # would end the binding above it (row-core-01).
        t = re.sub(r'^-- RHS size: \{[^}]*\}$', '', t, flags=re.M)
        t = re.sub(r'^(?:--.*|Rec \{|end Rec \})$', '', t, flags=re.M)
        # Layout is not compared: GHC aligns continuation lines by the
        # length of names, which renumbering changes.
        mods[m] = ({n: re.sub(r'\s+', ' ', x).strip()
                    for n, x in bindings(t).items()}, t)
        dirs[m] = os.path.dirname(p)
    if not mods:
        raise Unreadable(f'{tree} holds no .dump-simpl dump')
    calls = {dirs[m] for m, (_, t) in mods.items() if 'Call.Call' in t}
    if not calls:
        raise Unreadable(f'no dump under {tree} holds a Call.Call: not the'
                         ' specialisation benchmark\'s')
    srcs = pc.sources(root)
    scopes = {m: pc.scope(srcs.get(m, '')) for m in mods}
    return mods, scopes, {m for m in mods if dirs[m] in calls}


def resolver(mods, scopes):
    def lookup(c, n, depth=0, seen=None):
        seen = seen or set()
        if c in seen or depth > 3:
            return None
        seen.add(c)
        if c in mods and n in mods[c][0]:
            return (c, n)
        al, unq = scopes.get(c, ({}, []))
        for d in sorted(set().union(*al.values()) if al else set()):
            r = lookup(d, n, depth + 1, seen)
            if r:
                return r
        return None

    cache = {}

    def resolve(m, tok):
        k = (m, tok)
        if k in cache:
            return cache[k]
        r = None
        q = QUAL.fullmatch(tok)
        al, unq = scopes.get(m, ({}, []))
        if q:
            mq, n = q.group(1)[:-1], q.group(2)
            cands = [mq] if mq in mods else sorted(al.get(mq, ()))
            for c in cands:
                r = lookup(c, n)
                if r:
                    break
        elif tok in mods[m][0]:
            # An unqualified name is the module's own or a local binder's,
            # which shadows any import; an imported name left unqualified
            # is an exported one, which GHC does not renumber.
            r = (m, tok)
        cache[k] = r
        return r
    return resolve


def sha(s):
    return hashlib.sha1(s.encode()).hexdigest()[:16]


def shape(m, text, resolve, follow=None):
    """The text with resolved references replaced, and the references; a
    reference follow refuses is written `@Module.base` instead; an
    unqualified name left, a local binder, keyword or type variable, is
    renamed to its base, its trailing digits dropped, and its order of first
    appearance among the names of that base, GHC numbering local binders
    across the whole module."""
    refs, parts, i = [], [], 0
    local, per_base = {}, collections.Counter()
    for mt in NAME.finditer(text):
        tok = mt.group(0)
        r = resolve(m, tok)
        if r and follow is not None and not follow(r):
            parts.append(text[i:mt.start()] + '@' + r[0] + '.'
                         + re.sub(r'\d+$', '', r[1]))
            i = mt.end()
        elif r:
            parts.append(text[i:mt.start()] + REF)
            i = mt.end()
            refs.append(r)
        elif not QUAL.fullmatch(tok):
            if tok not in local:
                base = re.sub(r'\d+$', '', tok)
                local[tok] = f'{base}_{per_base[base]}'
                per_base[base] += 1
            parts.append(text[i:mt.start()] + local[tok])
            i = mt.end()
    parts.append(text[i:])
    return ''.join(parts), refs


def hashes(mods, resolve, follow=None):
    """(exact, literal-blind) hashes of every binding, those of the library
    left out where follow is given."""
    h0, h0l, refs = {}, {}, {}
    for m, (binds, _) in mods.items():
        if follow is not None and not follow((m, '')):
            continue
        for n, t in binds.items():
            s, rs = shape(m, t, resolve, follow)
            h0[(m, n)], h0l[(m, n)] = sha(s), sha(LIT.sub('N', s))
            refs[(m, n)] = rs
    # A fixed number of rounds, the same in both builds, so that equal
    # structures get equal hashes across them; it bounds the depth
    # of reference a difference is seen through.
    out = []
    for base in (h0, h0l):
        h = dict(base)
        for _ in range(ROUNDS):
            h = {n: sha(base[n] + ''.join(h[r] for r in refs[n] if r in h))
                 for n in base}
        out.append(h)
    return out


def first_string(binds, t, seen=None):
    """The first string literal of t, references followed in text order."""
    seen = set() if seen is None else seen
    m = re.search(r'"((?:[^"\\]|\\.)*)"#', t)
    if m:
        return m.group(1)
    for tok in NAME.findall(t):
        if tok in binds and tok not in seen:
            seen.add(tok)
            r = first_string(binds, body(binds, tok), seen)
            if r:
                return r
    return None


def rows(mods, resolve, own, hs, hsl):
    """(module, size, kind, name, forced term, summing term, signatures,
    library callees) of every Call, its size and kind those of the ops list
    reaching it; a signature per function: exact and literals blanked,
    following every reference (hs) and the benchmark's own code alone
    (hsl); the callees, the library bindings the row's own code refers to,
    per function."""
    memo = {}

    def mine(r):
        return r[0] in own

    def refs_of(r):
        if r not in memo:
            memo[r] = shape(r[0], mods[r[0]][0][r[1]], resolve)[1]
        return memo[r]

    def lib_callees(m, term):
        seen, libs = set(), set()
        todo = list(shape(m, term, resolve)[1])
        while todo:
            r = todo.pop()
            if r in seen:
                continue
            seen.add(r)
            if mine(r):
                todo.extend(refs_of(r))
            else:
                libs.add(r)
        return frozenset(libs)

    out = []
    for m, (binds, _) in mods.items():
        owner, cache = collections.defaultdict(list), {}
        for lst in binds:
            mm = LISTS.fullmatch(lst)
            if mm:
                for x in reach(binds, body(binds, lst), cache) | {lst}:
                    owner[x].append((mm.group(2).lower(), mm.group(1)))
        for x, text in binds.items():
            for mt in re.finditer(r'\bCall\.Call\b', text):
                try:
                    _, terms = call_args(text, mt.end())
                except (IndexError, ValueError):
                    continue
                name = first_string(binds, terms[5]) or terms[5]
                # The forced function is the harness's rnf of f's result:
                # f together with the NFData dictionary of the result.
                forced = terms[6] + ' ' + terms[1]
                sig, libs = [], []
                for term in (forced, terms[8]):
                    s, rs = shape(m, term, resolve)
                    sl, rsl = shape(m, term, resolve, mine)
                    sig.append((sha(s + ''.join(hs[0][r] for r in rs)),
                                sha(LIT.sub('N', s)
                                    + ''.join(hs[1][r] for r in rs)),
                                sha(sl + ''.join(hsl[0][r] for r in rsl)),
                                sha(LIT.sub('N', sl)
                                    + ''.join(hsl[1][r] for r in rsl))))
                    libs.append(lib_callees(m, term))
                for size, kind in owner.get(x) or [('?', '?')]:
                    out.append((m, size, kind, name, forced, terms[8], sig,
                                libs))
    return out


def closure(mods, resolve, root_mod, term, follow=None):
    """The closure of term in BFS order: [(node, text with references
    replaced by their BFS index)]."""
    index, out = {}, []
    s, rs = shape(root_mod, term, resolve, follow)
    todo = [(None, s, rs)]
    while todo:
        node, s, rs = todo.pop(0)
        parts = s.split(REF)
        txt = parts[0]
        for i, r in enumerate(rs):
            if r not in index:
                index[r] = len(index)
                t = mods[r[0]][0][r[1]]
                todo.append((r,) + shape(r[0], t, resolve, follow))
            txt += f'#{index[r]}' + parts[i + 1]
        out.append((node, txt))
    return out


def build(tree, root):
    """Everything a tree's rows need: (mods, resolve, own, rows)."""
    mods, scopes, own = load(tree, root)
    resolve = resolver(mods, scopes)
    hs = hashes(mods, resolve)
    hsl = hashes(mods, resolve, lambda r: r[0] in own)
    return mods, resolve, own, rows(mods, resolve, own, hs, hsl), hs


def compare(ta, tb, root, sample=None):
    out, res, full = [], [], []
    for tree in (ta, tb):
        mods, _, _, rs, hs = build(tree, root)
        res.append(rs)
        full.append(hs[1])
        print(f'{tree}: {len(mods)} modules, '
              f'{sum(len(b) for b, _ in mods.values())} bindings, '
              f'{len(rs)} calls', file=sys.stderr)
        if sample is not None:
            return [' | '.join(map(str, r[:6])) for r in rs[:sample]]
    a, b = collections.defaultdict(list), collections.defaultdict(list)
    for r in res[0]:
        a[r[:4]].append(r)
    for r in res[1]:
        b[r[:4]].append(r)
    out.append('\t'.join(['module', 'size', 'kind', 'name', 'forced local',
                          'summed local', 'forced full', 'summed full',
                          'calls', 'changed library callees']))
    for k in sorted(set(a) | set(b)):
        if not a[k] or not b[k]:
            out.append('\t'.join(k + (f'UNMATCHED {len(a[k])} {len(b[k])}',)))
            continue

        def v(j, i):
            ex, lit = ([sorted(r[6][j][x] for r in rr) for rr in (a[k], b[k])]
                       for x in (i, i + 1))
            return 'same' if ex[0] == ex[1] else \
                'literals' if lit[0] == lit[1] else 'differs'
        verdict = [v(0, 2), v(1, 2), v(0, 0), v(1, 0)]
        n = f'{len(a[k])}:{len(b[k])}' if len(a[k]) + len(b[k]) > 2 else ''
        changed = set()
        if verdict[0] != 'differs' and verdict[2] == 'differs':
            for la in (r[7][0] for r in a[k]):
                for c in la:
                    if c in full[0] and full[0].get(c) != full[1].get(c):
                        changed.add(c[0].rsplit('.', 1)[-1] + '.' + c[1])
        out.append('\t'.join(k + tuple(verdict)
                             + (n, ' '.join(sorted(changed)))))
    return out


def row_closures(tree, root, key):
    """(forced closure, summed closure) of the first row under key."""
    mods, resolve, own, rs, _ = build(tree, root)
    got = [r for r in rs if r[:4] == key]
    if not got:
        raise Unreadable(f'no row {" ".join(key)} in {tree}')
    return tuple(closure(mods, resolve, key[0], got[0][i],
                         lambda r: r[0] in own) for i in (4, 5))


def diff(ta, tb, root, key, summed=False, ops=6):
    out = []
    ca, cb = (row_closures(t, root, key)[1 if summed else 0] for t in (ta, tb))
    out.append(f'closure sizes {len(ca)} {len(cb)}')
    for (na, xa), (nb, xb) in zip(ca, cb):
        if LIT.sub('N', xa) != LIT.sub('N', xb):
            out.append(f'first differing node: {na} {nb}')
            wa, wb = xa.split(' '), xb.split(' ')
            shown = 0
            for op, i1, i2, j1, j2 in difflib.SequenceMatcher(
                    None, wa, wb, autojunk=False).get_opcodes():
                if op == 'equal':
                    continue
                out.append(f'{op} at token {i1}:')
                out.append('  context: '
                           + ' '.join(wa[max(0, i1 - 25):i1])[-400:])
                out.append('  A: ' + ' '.join(wa[i1:i2])[:600])
                out.append('  B: ' + ' '.join(wb[j1:j2])[:600])
                shown += 1
                if shown == ops:
                    break
            return out
    out.append('no differing node in the common prefix')
    return out


def dump(tree, root, key, path):
    forced, summed = row_closures(tree, root, key)
    with open(path, 'w') as fh:
        for label, nodes in (('FORCED', forced), ('SUMMED', summed)):
            fh.write(f'##### {label}\n')
            for node, txt in nodes:
                fh.write(f'=== {node}\n{txt}\n\n')


def sections(path, sec):
    """[(node label, text)] of one section of a dump file."""
    try:
        with open(path) as fh:
            lines = fh.read().split('\n')
    except OSError as e:
        raise Unreadable(f'{path}: {e.strerror}')
    cur, out = None, []
    for i, line in enumerate(lines):
        if line.startswith('#####'):
            cur = line[6:]
        elif cur == sec and line.startswith('=== ') and i + 1 < len(lines):
            out.append((line[4:], lines[i + 1]))
    if not out:
        raise Unreadable(f'{path} has no node in a section {sec}')
    return out


def balanced(t, start, i):
    """The end of the parenthesised group opening at t[i], or len(t)."""
    d = 0
    for j in range(i, len(t)):
        d += {'(': 1, ')': -1}.get(t[j], 0)
        if d == 0:
            return j + 1
    return len(t)


def drop_groups(t, opener, repl):
    """t with each `opener(...)` group, its parentheses balanced, replaced
    by repl."""
    out, i = [], 0
    while (k := t.find(opener, i)) >= 0:
        out.append(t[i:k] + repl)
        i = balanced(t, k, k + len(opener) - 1)
    return ''.join(out) + t[i:]


def norm(t, deep=False):
    """A closure node's text with node numbers, local names and binder
    numbers normalised; deep, casts, type arguments and unit qualifiers
    dropped too."""
    if deep:
        t = UNITQ.sub('', t)
        t = drop_groups(t, ' `cast` (', '')
        t = drop_groups(t, '@(', '@T')
    t = re.sub(r'#\d+', '#', t)
    t = re.sub(r'\b(ww|ipv|bx|wild|ds|eta|x|y|s|unbx|lvl|sat|a|b|n|xs|ys|go'
               r'|fail|exit|v)(_\d+)?\b', r'\1', t)
    t = re.sub(r'\$(w|s)*(j|go|wgo|lvl|lvl\d+)(_?\d+)?\b', '$J', t)
    return re.sub(r'_\d+\b', '', t)


def shown(t):
    """A node's text as printed: unit qualifiers and binder numbers gone."""
    t = UNITQ.sub('', re.sub(r'_0\b', '', t))
    return t.replace('GHC.Internal.Prim.', '').replace('GHC.Internal.Types.',
                                                       '')


def nodes(fa, fb, sec, width=600):
    A, B = sections(fa, sec), sections(fb, sec)
    ca = collections.Counter(norm(t) for _, t in A)
    cb = collections.Counter(norm(t) for _, t in B)
    out = [f'{sec}: nodes {len(A)} {len(B)}']
    for side, xs, mine, other in (('A only', A, ca, cb),
                                  ('B only', B, cb, ca)):
        left = mine - other
        for name, t in xs:
            k = norm(t)
            if left[k] > 0:
                left[k] -= 1
                out.append(f'--- {side} {name} ({len(t.split())} tokens)')
                out.append('    ' + shown(t)[:width])
    return out


def tokens(fa, fb, mod, na, nb, sec, width=400):
    def get(f, name):
        for node, t in sections(f, sec):
            if node == repr((mod, name)):
                return t
        raise Unreadable(f'{f} has no node {(mod, name)} in {sec}')
    A, B = norm(get(fa, na), True).split(), norm(get(fb, nb), True).split()
    out = [f'tokens {len(A)} {len(B)}']
    for op, i1, i2, j1, j2 in difflib.SequenceMatcher(
            None, A, B, autojunk=False).get_opcodes():
        if op != 'equal':
            out.append(f'{op} | A: '
                       + ' '.join(A[max(0, i1 - 5):i2 + 3])[:width])
            out.append('   | B: ' + ' '.join(B[max(0, j1 - 5):j2 + 3])[:width])
            out.append('')
    return out


def option(argv, flag, default):
    if flag not in argv:
        return default, argv
    i = argv.index(flag)
    if i + 1 >= len(argv) or not argv[i + 1].isdigit():
        raise Unreadable(f'{flag} needs a count')
    return int(argv[i + 1]), argv[:i] + argv[i + 2:]


def need(argv, k):
    if len(argv) != k:
        raise Unreadable('usage:\n' + __doc__.split('\n\n')[1])


def run(argv):
    cmd, argv = argv[0], argv[1:]
    if cmd == 'rows':
        sample, argv = option(argv, '--sample', None)
        need(argv, 3)
        return compare(*argv, sample=sample)
    if cmd == 'diff':
        summed = '--summed' in argv
        argv = [a for a in argv if a != '--summed']
        ops, argv = option(argv, '--ops', 6)
        need(argv, 7)
        return diff(argv[0], argv[1], argv[2], tuple(argv[3:7]), summed, ops)
    if cmd == 'dump':
        need(argv, 7)
        dump(argv[0], argv[1], tuple(argv[2:6]), argv[6])
        return [f'wrote {argv[6]}']
    if cmd == 'nodes':
        width, argv = option(argv, '--width', 600)
        need(argv, 3)
        return nodes(*argv, width=width)
    if cmd == 'tokens':
        width, argv = option(argv, '--width', 400)
        need(argv, 6)
        return tokens(*argv, width=width)
    raise Unreadable(f'no subcommand {cmd}')


HEAD = ('\n==================== Tidy Core ====================\n'
        '2026-10-17 10:00:00.000000 UTC\n\nResult size of Tidy Core\n'
        '  = {terms: 99, types: 9, coercions: 0, joins: 0/0}\n\n')
SMALL = '-- RHS size: {terms: 2, types: 0, coercions: 0, joins: 0/0}\n'
# A comment GHC wraps: a binding's continuation lines to the eye of a
# reader that drops comment lines one at a time.
WRAPPED = ('-- RHS size: {terms: 2,382,\n              types: 1,005,\n'
           '              coercions: 10,\n              joins: 87/113}\n')


def binding(name, ty, rhs, size=SMALL):
    return f'{size}{name} :: {ty}\n{name}\n  = {rhs}\n\n'


def call(k):
    return binding(f'call{k}', 'Call', 'Call.Call\n      @Int\n      @Int\n'
                   '      dNF1\n      dNF2\n'
                   '      ghc-internal:GHC.Internal.Classes.$fEqInt\n'
                   '      ghc-internal:GHC.Internal.Show.$fShowInt\n'
                   f'      dTy\n      name{k}\n      f{k}\n      x1\n      g1')


def dynamic(lib, lit, big, sum4):
    """OpsDynamic's dump: rows r1 (calling L.lib), r2 (adding lit), r3,
    whose next binding has the size comment big, and r4 (calling
    L.sum4)."""
    parts = [HEAD]
    for k, rhs in ((1, f'\\ (x :: Int) -> L.{lib} x'),
                   (2, '\\ (x :: Int) -> ghc-internal:GHC.Internal.Prim.+# x'
                       f' {lit}#'),
                   (3, '\\ (x :: Int) -> x'),
                   (4, f'\\ (x :: Int) -> L.{sum4} x')):
        parts.append(binding(f'f{k}', 'Int -> Int', rhs))
        if k == 3:
            parts.append(binding('big', 'Int', '7#', big))
        parts.append(binding(f'name{k}', 'Addr#', f'"r{k}"#'))
        parts.append(call(k))
    nf = 'Control.DeepSeq.C:NFData @Int lvl1'
    parts += [binding('dNF1', 'NFData Int', nf),
              binding('dNF2', 'NFData Int', nf),
              binding('dTy', 'Typeable Int', 'lvl1'),
              binding('x1', 'Int', 'ghc-internal:GHC.Internal.Types.I# 3#'),
              binding('g1', 'Int -> Int', '\\ (y :: Int) -> y'),
              binding('lvl1', 'Int', '3#'),
              binding('opsBSmall', '[Call]',
                      ': @Call call1 (: @Call call2 (: @Call call3'
                      ' (: @Call OpsDynamic.call4 ([] @Call))))')]
    return ''.join(parts)


# OpsRanked's lvl1 reaches its row, where OpsDynamic's lvl1 reaches nothing.
RANKED = (HEAD + binding('f9', 'Int -> Int', '\\ (x :: Int) -> x')
          + binding('name9', 'Addr#', '"r9"#')
          + call(9).replace('dNF1', 'OpsDynamic.dNF1').replace(
              'dNF2', 'OpsDynamic.dNF2').replace('dTy', 'OpsDynamic.dTy')
          .replace('x1\n', 'OpsDynamic.x1\n').replace('g1', 'OpsDynamic.g1')
          + binding('lvl1', '[Call]', ': @Call call9 ([] @Call)')
          + binding('opsUEmpty', '[Call]', '++ @Call lvl1 lvl1'))


def library(foo):
    return (HEAD + binding('foo', 'Int -> Int', f'\\ (y :: Int) -> {foo}')
            + binding('bar', 'Int -> Int', '\\ (y :: Int) ->'
                      ' ghc-internal:GHC.Internal.Prim.*# y y'))


def plant(td, name, dyn, lib):
    """A -dumpdir tree under td: OpsDynamic, OpsRanked and Data.Array.Lib."""
    tree = os.path.join(td, name)
    os.makedirs(os.path.join(tree, 'Data', 'Array'))
    for rel, text in (('OpsDynamic', dyn), ('OpsRanked', RANKED),
                      ('Data/Array/Lib', lib)):
        with open(os.path.join(tree, rel + '.dump-simpl'), 'w') as fh:
            fh.write(text)
    return tree


def checks(bad, td):
    """The self-test's cases, each failure appended to bad; a status
    to exit with where the fixtures cannot be built."""
    src = os.path.join(td, 'src')
    for rel, text in (('bench/OpsDynamic.hs', 'module OpsDynamic where\n'
                       'import qualified Data.Array.Lib as L\n'),
                      ('bench/OpsRanked.hs', 'module OpsRanked where\n'
                       'import OpsDynamic\n'),
                      ('Data/Array/Lib.hs', 'module Data.Array.Lib where\n')):
        os.makedirs(os.path.dirname(os.path.join(src, rel)), exist_ok=True)
        with open(os.path.join(src, rel), 'w') as fh:
            fh.write(text)
    ta = plant(td, 'A', dynamic('foo', 1, WRAPPED, 'foo'), library('y'))
    tb = plant(td, 'B', dynamic('foo', 2, SMALL, 'bar'),
               library('ghc-internal:GHC.Internal.Prim.+# y y'))
    if module_name('specialisation/specialisation-tmp/bench/OpsDynamic') \
            != 'OpsDynamic' or module_name('Data/Array/Lib') \
            != 'Data.Array.Lib':
        bad.append('module names not the capitalised end of a key')
    with contextlib.redirect_stderr(io.StringIO()):
        got = run(['rows', ta, tb, src])
    want = ['OpsDynamic\tsmall\tB\tr1\tsame\tsame\tdiffers\tsame\t\tLib.foo',
            'OpsDynamic\tsmall\tB\tr2\tliterals\tsame\tliterals\tsame\t\t',
            'OpsDynamic\tsmall\tB\tr3\tsame\tsame\tsame\tsame\t\t',
            'OpsDynamic\tsmall\tB\tr4\tdiffers\tsame\tdiffers\tsame\t\t',
            'OpsRanked\tempty\tU\tr9\tsame\tsame\tsame\tsame\t\t']
    if got[1:] != want:
        bad.append('rows:\n  ' + '\n  '.join(got[1:]))
    got = run(['diff', ta, tb, src, 'OpsDynamic', 'small', 'B', 'r4'])
    if len(got) < 3 or got[1] != (
            "first differing node: ('OpsDynamic', 'f4')"
            " ('OpsDynamic', 'f4')") \
            or not got[2].startswith('replace at token') \
            or got[4:6] != ['  A: @Data.Array.Lib.foo',
                            '  B: @Data.Array.Lib.bar']:
        bad.append(f'diff of r4: {got}')
    got = run(['diff', '--summed', ta, tb, src, 'OpsDynamic', 'small', 'B',
               'r4'])
    if got[-1] != 'no differing node in the common prefix':
        bad.append(f'diff of r4 summed: {got}')
    da, db = os.path.join(td, 'r4-a.txt'), os.path.join(td, 'r4-b.txt')
    run(['dump', ta, src, 'OpsDynamic', 'small', 'B', 'r4', da])
    run(['dump', tb, src, 'OpsDynamic', 'small', 'B', 'r4', db])
    with open(da) as fh:
        text = fh.read()
    if not text.startswith('##### FORCED\n=== None\n#0 #1\n\n'
                           "=== ('OpsDynamic', 'f4')\n") \
            or '##### SUMMED\n' not in text:
        bad.append(f'dump of r4: {text[:200]!r}')
    got = run(['nodes', da, db, 'FORCED'])
    if len(got) != 5 or got[0] != 'FORCED: nodes 4 4' \
            or not got[1].startswith("--- A only ('OpsDynamic', 'f4')") \
            or 'Lib.foo' not in got[2] or 'Lib.bar' not in got[4]:
        bad.append(f'nodes of r4: {got}')
    got = run(['tokens', da, db, 'OpsDynamic', 'f4', 'f4', 'FORCED'])
    if len(got) < 3 or got[0] != 'tokens 14 14' \
        or not got[1].startswith('replace | A: ') \
            or not got[1].endswith('@Data.Array.Lib.foo x') \
            or not got[2].endswith('@Data.Array.Lib.bar x'):
        bad.append(f'tokens of f4: {got}')
    t = ('f @(Vector (Maybe Int)) (x `cast` (Sym (N:V <Int>_N) :: V ~R# W))'
         ' primitive_0-0.9.1.0-abc_0:Data.Primitive.foo ww_3 #12')
    if norm(t, True) != 'f @T (x) Data.Primitive.foo ww #':
        bad.append(f'deep normalisation: {norm(t, True)!r}')
    with contextlib.redirect_stderr(io.StringIO()):
        sample = run(['rows', '--sample', '2', ta, tb, src])
    if len(sample) != 2 or not sample[0].startswith('OpsDynamic | small'):
        bad.append(f'--sample: {sample}')
    empty = os.path.join(td, 'empty')
    os.makedirs(empty)
    nocall = os.path.join(td, 'nocall')
    os.makedirs(nocall)
    with open(os.path.join(nocall, 'Data.dump-simpl'), 'w') as fh:
        fh.write(library('y'))
    for argv, what in ((['rows', empty, tb, src], 'a tree without dumps'),
                       (['rows', nocall, tb, src], 'dumps without a Call'),
                       (['rows', ta, tb], 'too few arguments'),
                       (['diff', ta, tb, src, 'OpsDynamic', 'small', 'B',
                         'r7'], 'a row not found'),
                       (['nodes', da, db, 'MIDDLE'], 'a section not found'),
                       (['tokens', da, db, 'OpsDynamic', 'f7', 'f4',
                         'FORCED'], 'a node not found'),
                       (['nodes', da, os.path.join(td, 'none'), 'FORCED'],
                        'a missing file')):
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            rc = main(argv)
        if rc != 2 or not err.getvalue().startswith('row-core: '):
            bad.append(f'{what} did not exit 2 with a reason: {rc}')


def self_test():
    """Two builds' dumps of a benchmark of five rows and a library, written
    here: a row whose library callee changed, one changing in a literal, one
    after whose forced function a wrapped size comment changed, one calling
    another library function, and one in a second module that reaches its
    row through a binder whose name the first module binds too."""
    bad = []
    try:
        with tempfile.TemporaryDirectory() as td:
            rc = checks(bad, td)
            if rc is not None:
                return rc
    except Unreadable as e:
        bad.append(f'a run the self-test needs did not happen: {e}')
    for x in bad:
        print('FAIL', x)
    print('self-test', 'FAILED' if bad else 'passed')
    return 1 if bad else 0


def main(argv):
    if argv == ['--self-test']:
        return self_test()
    if not argv:
        print(__doc__.split('\n\n')[1], file=sys.stderr)
        return 2
    try:
        out = run(argv)
    except Unreadable as e:
        print(f'row-core: {e}', file=sys.stderr)
        return 2
    for line in out:
        print(line)
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
