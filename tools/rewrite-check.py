#!/usr/bin/env python3
"""Check a history rewrite: what changed between a branch and its rewrite.

Usage: python3 tools/rewrite-check.py OLD_BASE..OLD_TIP NEW_BASE..NEW_TIP
           [--expect REV]... [--allow-tree PATH]... [--signed] [-C REPO]
       python3 tools/rewrite-check.py --self-test

The two ranges are the branch before and after a rewrite --- a fold, an
amended message, a reorder --- given as git ranges, so a backup ref or a
reflog entry names the old one. The commits are paired by their subjects in
order; a commit of the old range with no counterpart is dropped, which is
expected of a `fixup!`, `squash!` or `amend!` commit and of one named by
`--expect`, and a finding otherwise. Each pair's patch is compared by `git
patch-id --stable`. Where the two differ the change is
  expected, the old commit being one an `--expect REV` names;
  context-only, the lines the two patches add and remove being the same,
    only the context around them or their line numbers having moved, which
    is what a commit replayed over an earlier fold looks like; or
  a finding.
A changed message or author is a finding unless the commit is expected, as
is a commit an `--expect` names whose patch did not change at all. The two
tips' trees must be equal but for the paths `--allow-tree` names (a fold of
uncommitted work moves the tip's tree by that work); with `--signed`, every
commit of the new range must carry a good signature.

This is the check a history rewrite owes before the old branch is let go:
without it the evidence that nothing else moved was a session's own
reading, and a rewrite replays every later commit. On orthotope's
`pr-mikolaj-toVectorListT` it confirmed a fold of a commit and of
uncommitted work into two earlier commits: those two and the one whose
conflict the fold resolved expected, the folded commit dropped, one later
commit context-only, the tip's tree moved by the folded file alone, and
every new commit signed.

Exit 0 when the rewrite changed nothing it was not expected to, 1 with the
findings listed, 2 when it could not be checked: a range git cannot resolve
or an empty one, or an `--expect` that is no commit.
"""

import collections
import difflib
import os
import subprocess
import sys

FOLDED = ('fixup! ', 'squash! ', 'amend! ')
# Subject, message and author, NUL-separated, the date raw so a rewrite that
# kept it compares equal.
FORMAT = '%s%x00%B%x00%an <%ae> %ad'


class GitError(Exception):
    pass


def git(repo, *args, stdin=None):
    r = subprocess.run(['git', '-C', repo] + list(args), input=stdin,
                       capture_output=True, text=True)
    if r.returncode != 0:
        raise GitError(f'git {" ".join(args)}: {r.stderr.strip()}')
    return r.stdout


def commits(repo, rng):
    out = git(repo, 'rev-list', '--reverse', '--topo-order', rng).split()
    if not out:
        raise GitError(f'{rng} holds no commit')
    return out


def info(repo, rev):
    """(subject, message, author, patch id, changed lines) of a commit."""
    fmt = git(repo, 'log', '-1', '--date=raw', '--format=' + FORMAT, rev)
    subject, message, author = fmt.split('\x00')
    patch = git(repo, 'show', '--format=', '--no-color', rev)
    pid = git(repo, 'patch-id', '--stable', stdin=patch).split()
    lines, cur = collections.Counter(), None
    for line in patch.split('\n'):
        if line.startswith('diff --git '):
            cur = line
        elif line.startswith(('+++', '---')):
            continue
        elif line[:1] in ('+', '-'):
            lines[(cur, line)] += 1
    return (subject, message.rstrip('\n'), author.strip(),
            pid[0] if pid else '', lines)


def check(repo, old, new, expect, allow, signed):
    """(report lines, number of findings)."""
    oc, nc = commits(repo, old), commits(repo, new)
    exp = {git(repo, 'rev-parse', '--verify', e + '^{commit}').strip(): e
           for e in expect}
    oi = {c: info(repo, c) for c in oc}
    ni = {c: info(repo, c) for c in nc}
    lines, findings, used = [], 0, set()
    def find(text):
        nonlocal findings
        findings += 1
        lines.append('FINDING ' + text)
    sm = difflib.SequenceMatcher(None, [oi[c][0] for c in oc],
                                 [ni[c][0] for c in nc], autojunk=False)
    counts = collections.Counter()
    for op, i1, i2, j1, j2 in sm.get_opcodes():
        if op == 'equal' or (op == 'replace' and i2 - i1 == j2 - j1):
            for o, n in zip(oc[i1:i2], nc[j1:j2]):
                so, mo, ao, po, lo = oi[o]
                sn, mn, an, pn, ln = ni[n]
                tag = f'{o[:9]} -> {n[:9]} {sn}'
                if o in exp:
                    used.add(o)
                    if po == pn and mo == mn:
                        find(f'expected to change, unchanged: {tag}')
                    else:
                        counts['expected'] += 1
                        lines.append(f'expected     {tag}')
                    continue
                if so != sn:
                    find(f'subject changed: {o[:9]} {so} -> {sn}')
                if po == pn:
                    counts['unchanged'] += 1
                elif lo == ln:
                    counts['context-only'] += 1
                    lines.append(f'context-only {tag}')
                else:
                    find(f'patch changed: {tag}')
                if mo != mn and so == sn:
                    find(f'message changed: {tag}')
                if ao != an:
                    find(f'author changed: {tag} ({ao} -> {an})')
            continue
        for o in oc[i1:i2]:
            if oi[o][0].startswith(FOLDED) or o in exp:
                used.add(o)
                counts['folded'] += 1
                lines.append(f'folded       {o[:9]} {oi[o][0]}')
            else:
                find(f'dropped: {o[:9]} {oi[o][0]}')
        for n in nc[j1:j2]:
            find(f'added: {n[:9]} {ni[n][0]}')
    for h, e in exp.items():
        if h not in used:
            find(f'--expect {e} is in neither range as a commit paired '
                 'or dropped')
    diff = git(repo, 'diff', '--name-only', oc[-1], nc[-1]).split('\n')
    moved = [p for p in diff if p]
    for p in moved:
        if any(p == a or p.startswith(a.rstrip('/') + '/') for a in allow):
            lines.append(f'tree moved   {p} (allowed)')
        else:
            find(f'tree differs: {p}')
    if signed:
        for n in nc:
            g = git(repo, 'log', '-1', '--format=%G?', n).strip()
            if g != 'G':
                find(f'signature {g or "none"}: {n[:9]} {ni[n][0]}')
    lines.append(f'{len(oc)} commits -> {len(nc)}: ' + ', '.join(
        f'{counts[k]} {k}' for k in ('unchanged', 'context-only', 'expected',
                                     'folded') if counts[k])
        + f'; {findings} finding{"s" if findings != 1 else ""}')
    return lines, findings


def self_test():
    """A branch and its rewrite: a fold into an earlier commit, the later
    commits replayed above it; then the old branch with a fixup the rewrite
    dropped and with a commit nothing expects dropped, and the new one with
    a reworded message and an unexpected edit, unsigned throughout."""
    import tempfile
    bad = []
    with tempfile.TemporaryDirectory() as td:
        g = ['git', '-C', td, '-c', 'user.name=t', '-c', 'user.email=t@t',
             '-c', 'commit.gpgsign=false']
        def run(*a, env=None):
            r = subprocess.run(g + list(a), capture_output=True, text=True,
                               env=env)
            if r.returncode != 0:
                raise RuntimeError(f'{a}: {r.stderr}')
            return r.stdout.strip()
        def put(name, text):
            with open(os.path.join(td, name), 'w') as fh:
                fh.write(text)
        def commit(msg, date):
            env = dict(os.environ, GIT_AUTHOR_DATE=date,
                       GIT_COMMITTER_DATE=date)
            run('commit', '-qam', msg, env=env)
            return run('rev-parse', 'HEAD')
        def text(*numbers):
            """File a, the lines numbered spelt out."""
            words = {2: 'two', 4: 'four', 6: 'six'}
            return ''.join(f'line {words[i] if i in numbers else i}\n'
                           for i in range(1, 9))
        def report(why, got):
            bad.append(why + ':\n  ' + '\n  '.join(got))
        run('init', '-q')
        put('a', text())
        run('add', 'a')
        base = commit('base', '1000000000 +0000')
        OLD, NEW = f'{base}..old', f'{base}..new'
        def chk(expect, allow, signed=False):
            return check(td, OLD, NEW, expect, allow, signed)
        put('a', text(2))
        c2 = commit('Change line 2', '1000000100 +0000')
        put('a', text(2, 6))
        commit('Change line 6', '1000000200 +0000')
        put('b', 'b\n')
        run('add', 'b')
        c4 = commit('Add b', '1000000300 +0000')
        run('branch', 'old')
        # The rewrite: line 4 folded into c2, the later two replayed above it.
        run('checkout', '-q', '-b', 'new', base)
        put('a', text(2, 4))
        commit('Change line 2', '1000000100 +0000')
        put('a', text(2, 4, 6))
        commit('Change line 6', '1000000200 +0000')
        put('b', 'b\n')
        run('add', 'b')
        commit('Add b', '1000000300 +0000')
        got, n = chk([c2], ['a'])
        if n or not any(l.startswith('expected ') for l in got) or not any(
                l.startswith('context-only') for l in got):
            report('the fold', got)
        got, n = chk([c2], [])
        if n != 1 or not any('tree differs: a' in l for l in got):
            report('the fold without --allow-tree', got)
        got, n = chk([], ['a'])
        if n != 1 or not any('patch changed' in l and 'line 2' in l
                             for l in got):
            report('the fold not expected', got)
        got, n = chk([c2, c4], ['a'])
        if n != 1 or not any('expected to change, unchanged' in l
                             for l in got):
            report('an --expect that missed', got)
        # A fixup on the old branch, dropped by the rewrite.
        run('checkout', '-q', 'old')
        put('a', text(2, 4, 6))
        commit('fixup! Change line 2', '1000000400 +0000')
        got, n = chk([c2], [])
        if n or not any(l.startswith('folded') for l in got):
            report('a dropped fixup', got)
        # A dropped commit that is no fixup, and that nothing expects.
        put('c', 'c\n')
        run('add', 'c')
        commit('Extra', '1000000500 +0000')
        got, n = chk([c2], ['c'])
        if n != 1 or not any(l.startswith('FINDING dropped') and 'Extra' in l
                             for l in got):
            report('a dropped commit nothing expects', got)
        run('reset', '-q', '--hard', 'HEAD~1')
        # A reworded message, then an unexpected edit.
        run('checkout', '-q', 'new')
        run('commit', '-q', '--amend', '-m', 'Add b\n\nA body.')
        got, n = chk([c2], [])
        if n != 1 or not any('message changed' in l for l in got):
            report('a reworded message', got)
        put('b', 'b!\n')
        run('commit', '-q', '--amend', '-am', 'Add b')
        got, n = chk([c2], ['b'])
        if n != 1 or not any('patch changed' in l and 'Add b' in l
                             for l in got):
            report('an unexpected edit', got)
        got, n = chk([c2], ['b'], signed=True)
        if n < 2 or not any(l.startswith('FINDING signature') for l in got):
            report('unsigned commits under --signed', got)
        if main(['-C', td, f'{base}..nosuch', NEW]) != 2:
            bad.append('a range git cannot resolve did not exit 2')
        if main(['-C', td, f'{base}..{base}', NEW]) != 2:
            bad.append('an empty range did not exit 2')
        if main(['-C', td, OLD, NEW, '--expect', 'nosuch']) != 2:
            bad.append('an --expect that is no commit did not exit 2')
    for b_ in bad:
        print('FAIL', b_)
    print('self-test', 'FAILED' if bad else 'passed')
    return 1 if bad else 0


def main(argv):
    if argv == ['--self-test']:
        return self_test()
    repo, expect, allow, signed, rest = '.', [], [], False, []
    i = 0
    while i < len(argv):
        a = argv[i]
        if a in ('--expect', '--allow-tree', '-C') and i + 1 < len(argv):
            if a == '-C':
                repo = argv[i + 1]
            elif a == '--expect':
                expect.append(argv[i + 1])
            else:
                allow.append(argv[i + 1])
            i += 2
        elif a == '--signed':
            signed, i = True, i + 1
        else:
            rest.append(a)
            i += 1
    if len(rest) != 2 or not all('..' in r for r in rest):
        print(__doc__.split('\n\n')[1], file=sys.stderr)
        return 2
    try:
        lines, findings = check(repo, rest[0], rest[1], expect, allow, signed)
    except GitError as e:
        print(e, file=sys.stderr)
        return 2
    print('\n'.join(lines))
    return 1 if findings else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
