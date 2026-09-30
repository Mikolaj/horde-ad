#!/usr/bin/env python3
"""Which removed inlining pragmas change the optimised Core, and where.

Usage: python3 tools/pragma-calls.py DUMPS_A DUMPS_B WORKTREE_B
       python3 tools/pragma-calls.py --self-test

DUMPS_A and DUMPS_B are the dump trees of two builds made with
`--ghc-options="-ddump-simpl -ddump-to-file -dsuppress-uniques
-dsuppress-idinfo"` (tools/core-diff.py says how to keep two builds apart);
WORKTREE_B is the git checkout B was built from, whose uncommitted diff
removes the pragmas. For each `INLINE`, `INLINABLE` or `NOINLINE` pragma
the diff deletes, the script counts the occurrences of its target's name in
every module's Core in both builds --- bare or module-qualified, and behind
the `$s`, `$w` and similar prefixes of specialisations and workers --- and
prints one line per pragma: DEAD when every module's count agrees, MOVED
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
DUMPS.tokens.pickle, since tokenising 1.5 GB of Core takes a minute.

Exit 0 when the verdicts were printed, 2 when they could not be: a dump
tree without `.dump-simpl` files, a WORKTREE that git cannot diff, or a
diff that removes no pragma.
"""

import collections
import gzip
import os
import pickle
import re
import subprocess
import sys

TOK = re.compile(r"[\w$'.]+")
PRAGMA = re.compile(r'-\s*\{-#\s*(?:INLINE|INLINABLE|INLINEABLE|NOINLINE)'
                    r'\s*(?:\[~?\d\])?\s*(\S+)\s*#-\}')


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
            names.append((cur, m.group(1)))
    return names


def normalise(tok):
    """A Core token as the name it refers to: module qualifier and the
    one-letter `$` prefixes of specialisations and workers dropped."""
    tok = re.sub(r"^(?:[A-Z][\w']*\.)+", '', tok)
    return re.sub(r'^(?:\$[a-z])+', '', tok)


def load(root):
    """Module key -> Counter of normalised tokens, cached beside root."""
    cache = root.rstrip('/') + '.tokens.pickle'
    if os.path.exists(cache):
        with open(cache, 'rb') as fh:
            return pickle.load(fh)
    out = {}
    for dp, _, fs in os.walk(root):
        for f in fs:
            if '.dump-simpl' not in f:
                continue
            p = os.path.join(dp, f)
            op = gzip.open if f.endswith('.gz') else open
            with op(p, 'rt', errors='replace') as fh:
                raw = collections.Counter(TOK.findall(fh.read()))
            c = collections.Counter()
            for t, n in raw.items():
                c[normalise(t)] += n
            out[p.rsplit('/build/', 1)[-1].split('.dump-simpl')[0]] = c
    if out:
        with open(cache, 'wb') as fh:
            pickle.dump(out, fh)
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


def self_test():
    """A git repository whose diff removes two pragmas, and two dump trees
    in which one target's call sites change and the other's do not."""
    import tempfile
    bad = []
    with tempfile.TemporaryDirectory() as td:
        repo = os.path.join(td, 'repo')
        os.makedirs(repo)
        src = ('module M where\n{-# INLINE f #-}\nf x = x\n'
               '{-# INLINE [1] g #-}\ng x = x\n{-# NOINLINE h #-}\nh x = x\n')
        with open(os.path.join(repo, 'M.hs'), 'w') as fh:
            fh.write(src)
        git = ['git', '-C', repo, '-c', 'user.name=t', '-c', 'user.email=t@t']
        for cmd in (['init', '-q'], ['add', 'M.hs'],
                    ['commit', '-q', '-m', 'x', '--no-gpg-sign']):
            subprocess.run(git + cmd, check=True, capture_output=True)
        with open(os.path.join(repo, 'M.hs'), 'w') as fh:
            fh.write(src.replace('{-# INLINE f #-}\n', '')
                        .replace('{-# INLINE [1] g #-}\n', ''))
        dumps = {
            'A/build/src/M.dump-simpl': 'f = \\ x -> x\ng = \\ x -> x\n',
            'A/build/src/User.dump-simpl': 'u = \\ y -> y\nv = M.g 1\n',
            'B/build/src/M.dump-simpl': 'f = \\ x -> x\ng = \\ x -> x\n',
            'B/build/src/User.dump-simpl':
                'u = \\ y -> M.f y\nw = $sf 2\nv = M.g 1\n',
        }
        for rel, text in dumps.items():
            os.makedirs(os.path.dirname(os.path.join(td, rel)), exist_ok=True)
            with open(os.path.join(td, rel), 'w') as fh:
                fh.write(text)
        names = pragmas(repo)
        if names != [('M.hs', 'f'), ('M.hs', 'g')]:
            bad.append(f'pragmas the diff removes: {names}')
        got = verdicts(load(os.path.join(td, 'A')),
                       load(os.path.join(td, 'B')), names or [])
        want = ['M.hs\tf\tMOVED User 0->2', 'M.hs\tg\tDEAD']
        if got != want:
            bad.append('verdicts:\n  ' + '\n  '.join(got))
        if not os.path.exists(os.path.join(td, 'A.tokens.pickle')):
            bad.append('token counts not cached')
        empty = os.path.join(td, 'empty')
        os.makedirs(empty)
        if main([os.path.join(td, 'A'), empty, repo]) != 2:
            bad.append('a tree without dumps did not exit 2')
        if main([os.path.join(td, 'A'), os.path.join(td, 'B'), td]) != 2:
            bad.append('a directory git cannot diff did not exit 2')
    for b in bad:
        print('FAIL', b)
    print('self-test', 'FAILED' if bad else 'passed')
    return 1 if bad else 0


def main(argv):
    if argv == ['--self-test']:
        return self_test()
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
