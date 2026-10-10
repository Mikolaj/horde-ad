#!/usr/bin/env python3
"""Fold text edits into the commits they belong to, and reword commits,
by rebuilding a branch tree by tree rather than by rebase.

Usage: python3 tools/rewrite-fold.py SPEC [--dry] [-C REPO]
       python3 tools/rewrite-fold.py --self-test

SPEC is a Python file defining BASE and TIP, two revisions with no merge
between them; SUBS, a list of (COMMIT, PATH, OLD, NEW), each replacing the
text OLD by NEW in PATH from COMMIT's tree on; and REWORD, a dict from
COMMIT to a file holding that commit's whole new message, trailers
included. One of SUBS and REWORD may be absent. A relative message path is
read against SPEC's directory, and the revisions are resolved in REPO, the
working directory by default.

Every commit of BASE..TIP is built again with `git commit-tree`, in order.
Its tree is the old one with every substitution whose COMMIT it is or
follows applied, the substitutions of one path to one copy of it in the
order SUBS gives them, and its message is the old one or its REWORD file.
So no commit can conflict, a commit's diff changes only where a
substitution falls inside it, and a commit that no substitution or reword
reaches keeps its tree and message and gets a new hash. Authors and author
dates are kept, and committer dates are new; a commit is signed where
`commit.gpgsign` is set, as it is here and in orthotope.

Before anything is written, each substitution must find OLD exactly once in
every tree it reaches, at the point of the run where it applies, and NEW,
unless it is empty or part of OLD, in none of those trees as they were: a
substitution already applied, or one whose text a later commit changed, is
refused rather than applied to the wrong place. With --dry the run stops
there and lists the commits that a substitution starts at or a reword
reaches. Otherwise it prints each old commit beside its replacement,
`NEW_TIP <hash>`, and last `CHECK` and the `tools/rewrite-check.py` command
that checks the result: an --expect for every commit a substitution starts
at or a reword reaches, and none for a later commit whose diff a
substitution falls inside, which the check then reports for a reading; an
--allow-tree for every path whose text differs at the tip; and --signed
where the commits are signed. It moves no ref; run that check, then move
the branch by a reset guarded by the hash it expects to find.

Exit 0 when it ran, 2 when it did not: wrong arguments, an unreadable SPEC
or message file, a revision git cannot resolve, a merge in BASE..TIP or a
BASE that is not its fork point, a COMMIT outside it, a substitution
refused as above, or a failing git command. A refusal of the SPEC or of a
substitution comes before anything is written; a git command failing later
leaves objects that no ref reaches.
"""

import io
import os
import shlex
import subprocess
import sys
import tempfile


class Refusal(Exception):
    pass


def git(repo, *args, stdin=None, env=None):
    e = dict(os.environ, **env) if env else None
    r = subprocess.run(['git', '-C', repo] + list(args), input=stdin,
                       capture_output=True, text=True, encoding='utf-8',
                       errors='surrogateescape', env=e)
    if r.returncode != 0:
        raise Refusal('git %s: %s' % (' '.join(args), r.stderr.strip()))
    return r.stdout


def resolve(repo, rev):
    try:
        return git(repo, 'rev-parse', '--verify', rev + '^{commit}').strip()
    except Refusal:
        raise Refusal('%r is no commit' % rev)


def load_spec(path):
    spec = {}
    try:
        with open(path) as fh:
            exec(compile(fh.read(), path, 'exec'), spec)
    except (OSError, SyntaxError) as e:
        raise Refusal('cannot read %s: %s' % (path, e))
    for k in ('BASE', 'TIP'):
        if not isinstance(spec.get(k), str):
            raise Refusal('%s defines no %s' % (path, k))
    subs = spec.get('SUBS', [])
    if not (isinstance(subs, (list, tuple)) and all(
            isinstance(s, (list, tuple)) and len(s) == 4
            and all(isinstance(x, str) for x in s) for s in subs)):
        raise Refusal('SUBS is not a list of (COMMIT, PATH, OLD, NEW)')
    reword = spec.get('REWORD', {})
    if not (isinstance(reword, dict) and all(
            isinstance(k, str) and isinstance(v, str)
            for k, v in reword.items())):
        raise Refusal('REWORD is not a dict from commits to message files')
    if not subs and not reword:
        raise Refusal('%s has neither SUBS nor REWORD' % path)
    where = os.path.dirname(os.path.abspath(path))
    msgs = {}
    for c, f in reword.items():
        p = os.path.join(where, f)
        try:
            with open(p) as fh:
                msgs[c] = fh.read()
        except OSError as e:
            raise Refusal('cannot read %s: %s' % (p, e))
    return spec['BASE'], spec['TIP'], [tuple(s) for s in subs], msgs


def plan(repo, base_rev, tip_rev, subs, msgs):
    """The chain, and the files each of its commits gets anew; refuses
    before anything is written."""
    base, tip = resolve(repo, base_rev), resolve(repo, tip_rev)
    chain = git(repo, 'rev-list', '--reverse', base + '..' + tip).split()
    if not chain:
        raise Refusal('%s..%s is empty' % (base_rev, tip_rev))
    if git(repo, 'rev-list', '--merges', base + '..' + tip).strip():
        raise Refusal('%s..%s holds a merge' % (base_rev, tip_rev))
    if resolve(repo, chain[0] + '^') != base:
        raise Refusal('%s is not where %s forks' % (base_rev, tip_rev))
    pos = {c: i for i, c in enumerate(chain)}
    starts = []
    for c, p, o, n in subs:
        cc = resolve(repo, c)
        if cc not in pos:
            raise Refusal('%s is not in %s..%s' % (c, base_rev, tip_rev))
        if not o:
            raise Refusal('a substitution in %s has an empty OLD' % p)
        starts.append((pos[cc], p, o, n))
    rw = {}
    for c, m in msgs.items():
        cc = resolve(repo, c)
        if cc not in pos:
            raise Refusal('%s is not in %s..%s' % (c, base_rev, tip_rev))
        rw[cc] = m
    files, olds = [], {}
    for i, c in enumerate(chain):
        act = [(p, o, n) for j, p, o, n in starts if j <= i]
        new = {}
        for p in sorted({p for p, _, _ in act}):
            try:
                old = git(repo, 'show', '%s:%s' % (c, p))
            except Refusal:
                raise Refusal('%s has no %s' % (c[:9], p))
            s = olds[p] = old
            for q, o, n in act:
                if q != p:
                    continue
                k = s.count(o)
                if k != 1:
                    raise Refusal('%s:%s holds %r %d times, not once'
                                  % (c[:9], p, o[:60], k))
                if n and n not in o and n in old:
                    raise Refusal('%s:%s already holds %r'
                                  % (c[:9], p, n[:60]))
                s = s.replace(o, n)
            new[p] = s
        files.append(new)
    changed = sorted(p for p, t in files[-1].items() if t != olds[p])
    return base, chain, starts, rw, files, changed


def build(repo, base, chain, starts, rw, files, changed, out):
    r = subprocess.run(['git', '-C', repo, 'config', '--bool',
                        'commit.gpgsign'], capture_output=True, text=True)
    sign = r.stdout.strip() == 'true'
    parent = base
    with tempfile.TemporaryDirectory() as td:
        env = {'GIT_INDEX_FILE': os.path.join(td, 'index')}
        for c, new in zip(chain, files):
            git(repo, 'read-tree', c, env=env)
            for p, s in new.items():
                sha = git(repo, 'hash-object', '-w', '--stdin',
                          stdin=s).strip()
                mode = git(repo, 'ls-tree', c, '--', p).split()[0]
                git(repo, 'update-index', '--cacheinfo',
                    '%s,%s,%s' % (mode, sha, p), env=env)
            tree = git(repo, 'write-tree', env=env).strip()
            if c in rw:
                msg = rw[c]
            else:
                msg = git(repo, 'cat-file', 'commit', c).split('\n\n', 1)[1]
            who = git(repo, 'log', '-1', '--format=%an%x00%ae%x00%ad',
                      '--date=raw', c).strip().split('\0')
            author = {'GIT_AUTHOR_NAME': who[0], 'GIT_AUTHOR_EMAIL': who[1],
                      'GIT_AUTHOR_DATE': who[2]}
            args = ['commit-tree', tree, '-p', parent]
            if sign:
                args.append('-S')
            parent = git(repo, *args, stdin=msg, env=author).strip()
            print(c[:9], '->', parent[:9], file=out, flush=True)
    print('NEW_TIP', parent, file=out, flush=True)
    tool = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        'rewrite-check.py')
    cmd = ['python3', tool, '-C', repo, base + '..' + chain[-1],
           base + '..' + parent]
    for c in chain:
        if c in rw or any(chain[j] == c for j, _, _, _ in starts):
            cmd += ['--expect', c]
    for p in changed:
        cmd += ['--allow-tree', p]
    if sign:
        cmd.append('--signed')
    print('CHECK', ' '.join(shlex.quote(a) for a in cmd), file=out)
    return parent


def report(repo, chain, starts, rw, out):
    for i, c in enumerate(chain):
        folds = [p for j, p, _, _ in starts if j == i]
        if folds or c in rw:
            subject = git(repo, 'log', '-1', '--format=%s', c).strip()
            print(c[:9], subject, ' folds:', ' '.join(folds),
                  ' reword' if c in rw else '', file=out)
    print('every substitution applies once in every tree it reaches',
          file=out)


def run(argv, out, err=None):
    repo, dry, rest, i = '.', False, [], 0
    while i < len(argv):
        if argv[i] == '-C' and i + 1 < len(argv):
            repo, i = argv[i + 1], i + 2
        elif argv[i] == '--dry':
            dry, i = True, i + 1
        else:
            rest.append(argv[i])
            i += 1
    if len(rest) != 1:
        print(__doc__.split('\n\n')[1], file=err or sys.stderr)
        return 2
    try:
        base_rev, tip_rev, subs, msgs = load_spec(rest[0])
        base, chain, starts, rw, files, changed = plan(repo, base_rev,
                                                       tip_rev, subs, msgs)
        if dry:
            report(repo, chain, starts, rw, out)
        else:
            build(repo, base, chain, starts, rw, files, changed, out)
    except Refusal as e:
        print('REFUSED', e, file=err or sys.stderr)
        return 2
    return 0


def self_test():
    """A branch of three commits over a base: two substitutions of one file
    and a reword folded in, the result checked by rewrite-check; then
    refusals, and a dry run that writes nothing. The spec and the message
    file live outside the repository, which commits everything it holds."""
    bad = []
    with tempfile.TemporaryDirectory() as td, \
            tempfile.TemporaryDirectory() as sd:
        g = ['git', '-C', td, '-c', 'user.name=Ann', '-c', 'user.email=a@a',
             '-c', 'commit.gpgsign=false']

        def sh(*a, env=None):
            r = subprocess.run(g + list(a), capture_output=True, text=True,
                               env=dict(os.environ, **(env or {})))
            if r.returncode != 0:
                raise RuntimeError('%s: %s' % (a, r.stderr))
            return r.stdout.strip()

        def put(name, text, where=td):
            with open(os.path.join(where, name), 'w') as fh:
                fh.write(text)

        def commit(msg, date):
            sh('add', '-A')
            sh('commit', '-qm', msg, env={'GIT_AUTHOR_DATE': date,
                                          'GIT_COMMITTER_DATE': date})
            return sh('rev-parse', 'HEAD')

        def fold(spec, *extra):
            put('spec.py', spec, sd)
            out = io.StringIO()
            rc = run(['-C', td, os.path.join(sd, 'spec.py')] + list(extra),
                     out, io.StringIO())
            return rc, out.getvalue()

        sh('init', '-q')
        sh('config', 'commit.gpgsign', 'false')
        sh('config', 'user.name', 'Ann')
        sh('config', 'user.email', 'a@a')
        put('a', 'one\ntwo\nthree\n')
        put('b', 'x\n')
        base = commit('Base', '1000000000 +0000')
        put('a', 'one\ntwo\nthree\nfour\n')
        c1 = commit('Add four', '1000000100 +0000')
        put('b', 'x\ny\n')
        c2 = commit('Edit b', '1000000200 +0000')
        put('a', 'one\ntwo\nthree\nfour\nfive\n')
        c3 = commit('Add five', '1000000300 +0000')
        put('msg2.txt', 'Edit b, reworded\n', sd)
        head = 'BASE = %r\nTIP = %r\n' % (base, c3)
        rc, got = fold(head + "SUBS = [(%r, 'a', 'four\\n', 'FOUR\\n'),"
                       " (%r, 'a', 'one\\n', 'ONE\\n')]\n"
                       "REWORD = {%r: 'msg2.txt'}\n" % (c1, c1, c2))
        tips = [l.split()[1] for l in got.splitlines()
                if l.startswith('NEW_TIP ')]
        if rc != 0 or len(tips) != 1:
            bad.append('the fold did not run: rc %s, %r' % (rc, got))
        else:
            new = tips[0]
            if sh('show', new + ':a') != 'ONE\ntwo\nthree\nFOUR\nfive':
                bad.append('both substitutions of a did not reach the tip')
            if sh('show', new + '~2:a') != 'ONE\ntwo\nthree\nFOUR':
                bad.append('the substitutions did not start at their commit')
            if sh('rev-parse', new + '~3') != base:
                bad.append('the new chain is not built on BASE')
            reworded = sh('log', '-1', '--format=%B', new + '~1')
            if reworded != 'Edit b, reworded':
                bad.append('the reword did not reach its commit')
            who = sh('log', '-1', '--format=%an %ae %ad', '--date=raw',
                     new + '~2')
            if who != 'Ann a@a 1000000100 +0000':
                bad.append('the author or author date was not kept')
            checks = [l[len('CHECK '):] for l in got.splitlines()
                      if l.startswith('CHECK ')]
            want = ['--expect', c1, '--expect', c2, '--allow-tree', 'a']
            if len(checks) != 1 or shlex.split(checks[0])[-6:] != want:
                bad.append('the printed check is not the one owed: %r'
                           % checks)
            else:
                r = subprocess.run(shlex.split(checks[0]),
                                   capture_output=True, text=True)
                if r.returncode != 0:
                    bad.append('the printed check found more than the fold:\n'
                               + r.stdout + r.stderr)
        sub = head + "SUBS = [(%r, 'a', %%r, %%r)]\n" % c1
        for why, spec in [
                ('an OLD missing from its commit',
                 sub % ('five\n', 'FIVE\n')),
                ('an OLD found twice', sub % ('t', 'T')),
                ('a NEW already present', sub % ('two\n', 'three\n')),
                ('a COMMIT outside the chain', head + "SUBS = [(%r, 'a',"
                 " 'one\\n', 'ONE\\n')]\n" % base),
                ('a TIP git cannot resolve',
                 "BASE = %r\nTIP = 'nosuch'\nREWORD = {%r: 'msg2.txt'}\n"
                 % (base, c2)),
                ('a message file that is missing',
                 head + "REWORD = {%r: 'nosuch.txt'}\n" % c2)]:
            rc, _ = fold(spec)
            if rc != 2:
                bad.append('%s did not exit 2 but %s' % (why, rc))
        sh('checkout', '-q', '-b', 'side', c1)
        put('c', 'side\n')
        commit('Side', '1000000400 +0000')
        rc, _ = fold("BASE = %r\nTIP = 'side'\n"
                     "REWORD = {'side': 'msg2.txt'}\n" % c2)
        if rc != 2:
            bad.append('a BASE that is not the fork point did not exit 2'
                       ' but %s' % rc)
        sh('checkout', '-q', '-b', 'merged', c3)
        sh('merge', '-q', '--no-ff', '-m', 'Merge side', 'side')
        rc, _ = fold("BASE = %r\nTIP = 'merged'\nREWORD = {%r: 'msg2.txt'}\n"
                     % (base, c2))
        if rc != 2:
            bad.append('a merge in the range did not exit 2 but %s' % rc)
        before = sh('count-objects', '-v')
        rc, got = fold(head + "SUBS = [(%r, 'a', 'four\\n', 'FOUR\\n')]\n"
                       % c1, '--dry')
        if rc != 0 or 'NEW_TIP' in got or sh('count-objects', '-v') != before:
            bad.append('a dry run did not stop before writing: rc %s, %r'
                       % (rc, got))
    for b_ in bad:
        print('FAIL', b_)
    print('self-test', 'FAILED' if bad else 'passed')
    return 1 if bad else 0


def main(argv):
    if argv == ['--self-test']:
        return self_test()
    return run(argv, sys.stdout)


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
