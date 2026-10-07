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
the `$s`, `$w` and similar prefixes of specialisations and workers, an
operator without the parentheses its pragma writes it in --- and prints
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
removable: it may be dead only at today's inliner thresholds (CLAUDE.md,
Pragmas and optimisation flags). A name the diff removes a pragma from
twice is marked, since its counts cover every binding of that name.

The token counts of each dump tree are cached beside it, in
DUMPS.tokens.pickle, since tokenising 1.5 GB of Core takes a minute. The
cache records every dump file's size and modification time, the tokeniser
and the module keying it was counted with, and is recounted when any
of them differs, as after a rebuild into the same builddir.

`--inline` reads one build. For every INLINE pragma at column 0 of the
`.hs` files under SRCDIR it counts, in every module's Core but the defining
module's own, which its definition hides, two things. CALLED: the target,
its worker or its specialisation, qualified by the defining module, called
there. COPIED: a `$s` copy the module made itself, unqualified or qualified
by that module, counted only where the module defines no function of that
name. A line says `inlined` where neither is left, and RECURSIVE where the
target is a binder of a `Rec {` group of its own module's Core. A survivor
is a call too unsaturated to inline, the eta-expansion question of
docs/perf-checklist.md's I1, a recursive target, or one a phase holds back;
RECURSIVE is I2, an INLINE that on GHC HEAD blocks worker/wrapper and is
never honoured. A name with INLINE in several modules is marked, and its
copies, which may be any of theirs, are listed once, after the lines. A
pragma inside an instance, a class or a `where` is passed over, its name
being a method's or a local's. Its own token counts, unnormalised, are
cached beside the tree as DUMPS.rawtokens.pickle.

Exit 0 when the verdicts were printed, 2 when they could not be: a dump
tree without `.dump-simpl` files, a WORKTREE that git cannot diff, or a
diff that removes no pragma. `--inline` exits 1 when a target is called,
copied or recursive, 0 when every one is inlined, and 2 when no INLINE pragma
is found under SRCDIR or none of their modules has a dump.
"""

import collections
import os
import pickle
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dumps  # noqa: E402

# The module keying the cache was written with, part of its signature so a
# cache keyed the old way is recounted (pragma-calls-03).
KEYS = 'dumps.module_key'

TOK = re.compile(r"(?:[A-Z][\w']*\.)*"
                 r"(?:\$*[\w'][\w$']*|[!#$%&*+./<=>?@\\^|~:-]+)")
PRAGMA = re.compile(r'-\s*\{-#\s*(?:INLINE|INLINABLE|INLINEABLE|NOINLINE)'
                    r'\s*(?:\[~?\d\])?\s*(\S+)\s*#-\}')
INLINE_SRC = re.compile(r'^\{-#\s*INLINE\s*(?:\[~?\d\])?\s*(\S+)\s*#-\}', re.M)
MODULE = re.compile(r'^module\s+([A-Z][\w.]*)', re.M)


def target(n):
    """A pragma's target as Core names it: an operator without the
    parentheses its pragma writes it in."""
    return n[1:-1] if n.startswith('(') and n.endswith(')') else n


def pragmas(wt):
    """(file, name) of every pragma the worktree's diff removes, or None
    when git cannot diff it."""
    r = subprocess.run(['git', '-C', wt, 'diff', '-U0'],
                       capture_output=True, text=True)
    if r.returncode != 0:
        return None
    names, cur = [], None
    for line in r.stdout.split('\n'):
        if line.startswith('+++ '):
            cur = line[6:]
        m = PRAGMA.match(line)
        if m:
            names.append((cur, target(m.group(1))))
    return names


def normalise(tok):
    """A Core token as the name it refers to: module qualifier and the
    one-letter `$` prefixes of specialisations and workers dropped."""
    tok = re.sub(r"^(?:[A-Z][\w']*\.)+", '', tok)
    return re.sub(r'^(?:\$[a-z])+', '', tok)


def signature(root):
    """What a cached count must match: the tokeniser, the module keying, and
    every dump file's path, size and modification time. A dump is a file
    ending in .dump-simpl, gzipped or not, and not the .dump-simpl-stats
    beside it (pragma-calls-04)."""
    files = []
    for p, _ in dumps.walk(root, '.dump-simpl'):
        st = os.stat(p)
        files.append((p, st.st_size, st.st_mtime_ns))
    return TOK.pattern, KEYS, files


def load(root, raw=False):
    """Module key -> Counter of normalised tokens, or with raw of tokens as
    they print, cached beside root."""
    cache = root.rstrip('/') + ('.rawtokens.pickle' if raw else
                                '.tokens.pickle')
    sig = signature(root)
    if os.path.exists(cache):
        with open(cache, 'rb') as fh:
            got = pickle.load(fh)
        if isinstance(got, tuple) and len(got) == 2 and got[0] == sig:
            return got[1]
    out = {}
    for p, _, _ in sig[-1]:
        counts = collections.Counter(TOK.findall(dumps.read_text(p)))
        c = collections.Counter()
        for t, n in counts.items():
            c[t if raw else normalise(t)] += n
        out[dumps.module_key(p, root, '.dump-simpl')] = c
    if out:
        with open(cache, 'wb') as fh:
            pickle.dump((sig, out), fh)
    return out


def verdicts(a, b, names):
    dup = collections.Counter(n for _, n in names)
    lines = []
    for f, n in names:
        moved = []
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
    for dp, ds, fs in os.walk(src):
        ds[:] = [d for d in ds if not d.startswith(('.', 'dist'))]
        for f in fs:
            if not f.endswith('.hs'):
                continue
            p = os.path.join(dp, f)
            with open(p, errors='replace') as fh:
                txt = fh.read()
            m = MODULE.search(txt)
            mod = m.group(1) if m else 'Main'
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


def inline_census(root, tokens, prags):
    """(lines, number of targets left behind or recursive, number whose
    module has a dump)."""
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
        called_re = re.compile(rf"{re.escape(mod)}\.(?:\$[sw])*{e}[0-9]*")
        copy_re = re.compile(rf"((?:[A-Z][\w']*\.)*)\$s(?:\$[sw])*{e}[0-9]*")
        called, copied = [], []
        for k in sorted(tokens):
            if k in own:
                continue
            here, c = k.rsplit('/', 1)[-1], tokens[k]
            ncall = sum(v for t, v in c.items() if called_re.fullmatch(t))
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
        rec = any(n in rec_binders(dumps.read_text(paths[k])) for k in own)
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
    dump tree of it, with a copy qualified by a third module and a module
    copying a function of its own of the same name."""
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
            ('dist-newstyle/Q.hs', 'module Q where\n{-# INLINE q #-}\nq = 1\n')):
        with open(os.path.join(src, name), 'w') as fh:
            fh.write(text)
    tree = os.path.join(td, 'I')
    for rel, text in (
            ('build/src/M.dump-simpl',
             'Rec {\nM.r = \\ x -> M.r x\nend Rec }\n\nM.f = \\ x -> x\n'
             'M.g = \\ x -> x\n'),
            ('build/src/N.dump-simpl', 'N.f = 1\n'),
            ('build/src/User.dump-simpl',
             'User.u = \\ y -> M.f y\nUser.$sf1 = \\ y -> y\n'
             'User.v = N.$wf 2\nUser.w = Other.$sg 3\nUser.x = User.$sk2\n'),
            ('build/src/User2.dump-simpl',
             'User2.g = \\ x -> x\nUser2.$sg1 = User2.g 1\n')):
        p = os.path.join(tree, rel)
        os.makedirs(os.path.dirname(p), exist_ok=True)
        with open(p, 'w') as fh:
            fh.write(text)
    prags = inline_pragmas(src)
    want = [('M.hs', 'M', 'f'), ('M.hs', 'M', 'g'), ('M.hs', 'M', 'k'),
            ('M.hs', 'M', 'r'), ('N.hs', 'N', 'f'), ('P.hs', 'P', 'p')]
    if prags != want:
        bad.append(f'INLINE pragmas found: {prags}')
    got, flagged, seen = inline_census(tree, load(tree, raw=True), prags)
    want = ['M.hs\tf (name not unique)\tCALLED User 1',
            'M.hs\tg\tinlined', 'M.hs\tk\tCOPIED User 1',
            'M.hs\tr\tRECURSIVE',
            'N.hs\tf (name not unique)\tCALLED User 1',
            'P.hs\tp\tNO DUMP of P',
            '== copies of names with INLINE in several modules',
            'f\tCOPIED User 1']
    if got != want or flagged != 4 or seen != 5:
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


def self_test():
    """A git repository whose diff removes two pragmas, and two dump trees
    in which one target's call sites change and the other's do not."""
    import tempfile
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
        # over C then keyed by each dump's whole path, must be recounted.
        croot = os.path.join(td, 'C')
        with open(croot + '.tokens.pickle', 'wb') as fh:
            pickle.dump(((TOK.pattern, signature(croot)[-1]),
                         {os.path.join(croot, 'src/User'):
                          collections.Counter({'g': 9})}), fh)
        got = verdicts(load(croot), load(os.path.join(td, 'D')), names or [])
        want = ['M.hs\tf\tDEAD', 'M.hs\tg\tDEAD', 'M.hs\t+++\tDEAD']
        if got != want:
            bad.append('verdicts over -dumpdir trees, one module with a '
                       'stats file:\n  ' + '\n  '.join(got))
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
        lines, flagged, seen = inline_census(argv[1], tokens, prags)
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
    print('\n'.join(verdicts(*trees, names)))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
