#!/usr/bin/env python3
"""List the workaround comments that name no cause, and where filed issues
are cited.

Usage: python3 tools/workaround-cites.py SRC [DOCS]
       python3 tools/workaround-cites.py --self-test

SRC is a Haskell source tree; DOCS a directory of issue texts, by default
the `docs/` beside this tool's own directory, whose `ghc-issue-*.md` and
`vector-issue-*.md` files name their issue in their first lines, by its link
or reference-style, `[vector issue 570][570]`.

The first list is every comment block under SRC --- a run of `--` lines, a
trailing `--` comment, or a `{- -}` block --- that speaks of a workaround
(work around, stands in for, instead of, SpecConstr, `-O2`, slower, faster,
allocates, bug) and names no cause: no URL, no issue number after `#`, no
GHC flag, and neither "stands in for" nor "unidentified". Those are the
forms docs/perf-checklist.md's W1 accepts: the issue's URL, the flag or
optimisation the code stands in for, and "a workaround for an unidentified
issue". The second list is each issue of DOCS, with the files under SRC
that cite its number after `#`, `issues/`, `work_items/` or "issue", or
`(none)`.

Both are candidates for reading and not verdicts: a design note may speak
of speed without working around anything, and a file may cite an issue for
another reason. A shape with no comment at all is what no search of
comments reaches (W3).

Exit 0 when no block lacks a cause, 1 when one does, 2 when the run did not
happen: SRC holding no `.hs` file, or DOCS no issue file.
"""

import collections
import os
import re
import sys

VOCAB = re.compile(r'work ?around|stands? in for|instead of|SpecConstr|-O2\b'
                   r'|slower|faster|allocat|\bbug\b', re.I)
CAUSE = re.compile(r'https?://|#\d{3,}\b|(?<![\w-])-f[a-z][\w-]*'
                   r'|\bunidentified\b|stands? in for', re.I)
COMMENT = re.compile(r'--(?![!#$%&*+./<=>?@\\^|~:-])|---+')
# A link, or a reference-style `[vector issue 570][570]` or `[#27737][...]`.
ISSUE_LINK = re.compile(r'(?:work_items|issues)/(\d+)|\bissue (\d+)|#(\d{3,})')


def blocks(src):
    """[(first line number, text)] of a file's comment blocks: runs of
    whole-line `--` comments, trailing comments, and `{- -}` blocks, pragmas
    excepted."""
    out, run, start = [], [], None
    lines = src.split('\n')
    i = 0
    while i < len(lines):
        line = lines[i]
        s = line.lstrip()
        if s.startswith('{-') and not s.startswith('{-#'):
            j, text = i, [line]
            while '-}' not in lines[j] and j + 1 < len(lines):
                j += 1
                text.append(lines[j])
            if run:
                out.append((start, ' '.join(run)))
                run = []
            out.append((i + 1, ' '.join(text)))
            i = j + 1
            continue
        m = COMMENT.search(line)
        if m and not line[:m.start()].strip():
            if not run:
                start = i + 1
            run.append(line[m.end():].strip())
        else:
            if run:
                out.append((start, ' '.join(run)))
                run = []
            if m and '"' not in line[:m.start()]:
                out.append((i + 1, line[m.end():].strip()))
        i += 1
    if run:
        out.append((start, ' '.join(run)))
    return out


def sources(src):
    for dp, ds, fs in os.walk(src):
        ds[:] = sorted(d for d in ds if not d.startswith(('.', 'dist')))
        for f in sorted(fs):
            if f.endswith('.hs'):
                p = os.path.join(dp, f)
                with open(p, errors='replace') as fh:
                    yield os.path.relpath(p, src), fh.read()


def uncited(files):
    out = []
    for rel, txt in files:
        for n, text in blocks(txt):
            if VOCAB.search(text) and not CAUSE.search(text):
                out.append(f'  {rel}:{n}  {text[:100]}')
    return out


def issues(docs):
    """{(tracker, number): [doc file names]} of DOCS's issue files."""
    out = collections.defaultdict(list)
    for f in sorted(os.listdir(docs)):
        m = re.match(r'(ghc|vector)-issue-.*\.md$', f)
        if not m:
            continue
        with open(os.path.join(docs, f), errors='replace') as fh:
            head = ''.join(fh.readline() for _ in range(5))
        link = ISSUE_LINK.search(head)
        if link:
            num = next(g for g in link.groups() if g)
            out[(m.group(1).upper() if m.group(1) == 'ghc' else m.group(1),
                 num)].append(f)
    return out


def citations(files, found):
    lines = []
    for (tracker, num), docs in sorted(found.items()):
        pat = re.compile(r'(?:#|issues/|work_items/|issue )' + num + r'(?!\d)')
        citing = [rel for rel, txt in files if pat.search(txt)]
        lines.append(f'  {tracker} {num}  {", ".join(docs)}  '
                     + (', '.join(citing) if citing else '(none)'))
    return lines


def report(src, docs):
    files = list(sources(src))
    found = issues(docs) if os.path.isdir(docs) else {}
    bad = uncited(files)
    lines = (['== comment blocks speaking of a workaround and naming no cause '
              '(file:line, text)'] + bad
             + ['== filed issues and the files citing them'] + citations(files, found))
    return lines, len(bad), len(files), len(found)


def self_test():
    """A module with comment blocks citing a URL, an issue number, a flag,
    "unidentified" and "stands in for", two naming no cause, one a trailing
    comment, a design note, a pragma and an operator; and issue files of two
    trackers, one issue in two files and one cited nowhere."""
    import tempfile
    src = ('module M where\n'
           '-- Works around https://github.com/haskell/vector/issues/570.\n'
           'a = 1\n'
           '-- The loop is slower without this, GHC #27737.\n'
           'b = 2\n'
           '-- Faster than the fold with -fspec-constr off.\n'
           'c = 3\n'
           '-- A workaround for an unidentified issue.\n'
           'd = 4\n'
           '-- This stands in for the SpecConstr -O1 leaves off.\n'
           'e = 5\n'
           '-- Written as a case: the <> form\n'
           '-- retired more instructions, slower.\n'
           'f = 6\n'
           '{- The fill\n   allocates nothing here. -}\n'
           'g = 7  -- a workaround\n'
           '-- The plain design of h.\n'
           'h = 8\n'
           '{-# INLINE i #-}\n'
           'i = a --> b\n')
    bad = []
    with tempfile.TemporaryDirectory() as td:
        os.makedirs(os.path.join(td, 'S'))
        os.makedirs(os.path.join(td, 'D'))
        os.makedirs(os.path.join(td, 'E'))
        with open(os.path.join(td, 'S', 'M.hs'), 'w') as fh:
            fh.write(src)
        for name, text in (
                ('ghc-issue-reloads.md', '# GHC issue\n\nFiled as '
                 '[#27737](https://gitlab.haskell.org/ghc/ghc/-/work_items/27737)\n'),
                ('ghc-issue-reloads-comment.md',
                 '# A comment on https://gitlab.haskell.org/ghc/ghc/-/work_items/27737\n'),
                ('vector-issue-lazy.md',
                 '# vector\nhttps://github.com/haskell/vector/issues/571\n'),
                ('vector-issue-ref.md', '# vector issue: x\n\nFiled as '
                 '[vector issue 572][572]; this file stays.\n'),
                ('position-effect.md', '# not an issue\n')):
            with open(os.path.join(td, 'D', name), 'w') as fh:
                fh.write(text)
        got, nbad, nfiles, nissues = report(os.path.join(td, 'S'),
                                            os.path.join(td, 'D'))
        want = ['== comment blocks speaking of a workaround and naming no '
                'cause (file:line, text)',
                '  M.hs:12  Written as a case: the <> form retired more '
                'instructions, slower.',
                '  M.hs:15  {- The fill    allocates nothing here. -}',
                '  M.hs:17  a workaround',
                '== filed issues and the files citing them',
                '  GHC 27737  ghc-issue-reloads-comment.md, '
                'ghc-issue-reloads.md  M.hs',
                '  vector 571  vector-issue-lazy.md  (none)',
                '  vector 572  vector-issue-ref.md  (none)']
        if got != want or (nbad, nfiles, nissues) != (3, 1, 3):
            bad.append(f'report ({nbad}, {nfiles}, {nissues}):\n  '
                       + '\n  '.join(got))
        S, D, E = (os.path.join(td, x) for x in 'SDE')
        for argv, want, why in (([S, D], 1, 'blocks without a cause'),
                                ([E, D], 2, 'a tree without .hs files'),
                                ([S, E], 2, 'docs without issue files')):
            if main(argv) != want:
                bad.append(f'{why} did not exit {want}')
    for b in bad:
        print('FAIL', b)
    print('self-test', 'FAILED' if bad else 'passed')
    return 1 if bad else 0


def main(argv):
    if argv == ['--self-test']:
        return self_test()
    if len(argv) not in (1, 2) or any(a.startswith('--') for a in argv):
        print(__doc__.split('\n\n')[1], file=sys.stderr)
        return 2
    docs = argv[1] if len(argv) == 2 else os.path.join(
        os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'docs')
    lines, nbad, nfiles, nissues = report(argv[0], docs)
    if not nfiles:
        print(f'no .hs file under {argv[0]}', file=sys.stderr)
        return 2
    if not nissues:
        print(f'no ghc-issue-*.md or vector-issue-*.md file with its link '
              f'under {docs}', file=sys.stderr)
        return 2
    print('\n'.join(lines))
    return 1 if nbad else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
