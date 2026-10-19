#!/usr/bin/env python3
"""Inlining pragmas of two source trees compared binding by binding.

Usage: python3 tools/pragma-map.py TREE_A TREE_B
       python3 tools/pragma-map.py --self-test

Reads every `.hs` file under each tree, build directories (`dist*`) and
hidden ones passed over, comments blanked (tools/hssource.py), and keys
each `INLINE`, `INLINABLE` (or `INLINEABLE`) and `NOINLINE` pragma, with
its phase and `CONLIKE` or not alike, by its file's path below the tree,
the head of the instance or class it is indented under (its context, up to
`=>`, dropped) or `top`, the name it targets, and its occurrence under that
key, in order. Prints, in key order, every key whose pragma differs between
the trees, as `FILE [HEAD] NAME#K: A -> B`, `none` where a tree has no
pragma for a key the other has. This is how the pragmas of two commits of a
library are set side by side, where tools/pragma-calls.py reads what
removing some did to the Core.

Exit 0 when the comparison was printed, an empty one where every pragma
agrees, 2 when it could not be: a tree that is not a directory, a file that
cannot be read, or two trees with no pragma at all.
"""

import collections
import contextlib
import io
import os
import re
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hssource  # noqa: E402

# The longest spelling first and a word's end after it: INLINE first read
# INLINEABLE h as an INLINE of a name ABLE (pragma-map-01).
PRAGMA = re.compile(r'\{-#\s*(INLINEABLE|INLINABLE|NOINLINE|INLINE)\b\s*'
                    r'(?:CONLIKE\s*)?(\[~?\d+\])?\s*\(?([^\s)#,]+)')
HEAD = re.compile(r'^(class|instance)\b')


def head(lines, i):
    """The key of the class or instance whose head starts at lines[i], its
    context dropped."""
    k = hssource.head_key(lines, i)
    word = k.split()[0]
    return word + ' ' + k[len(word):].split('=>')[-1].strip()


def load(root):
    """(file, head or 'top', name, occurrence) -> pragma and phase."""
    out = {}
    for p in hssource.hs_paths(root):
        rel = os.path.relpath(p, root)
        with open(p, errors='replace') as fh:
            lines = hssource.strip_comments(fh.read()).split('\n')
        cnt, inst = collections.Counter(), 'top'
        for i, line in enumerate(lines):
            if HEAD.match(line):
                inst = head(lines, i)
            elif line[:1].isalpha():
                inst = 'top'
            for g in PRAGMA.finditer(line):
                key = (rel, inst if line[:1] in (' ', '\t') else 'top',
                       g.group(3))
                cnt[key] += 1
                out[key + (cnt[key],)] = (g.group(1).replace(
                    'INLINEABLE', 'INLINABLE') + (g.group(2) or ''))
    return out


def compare(a, b):
    return [f'{k[0]} [{k[1]}] {k[2]}#{k[3]}: {a.get(k, "none")} -> '
            f'{b.get(k, "none")}'
            for k in sorted(set(a) | set(b)) if a.get(k) != b.get(k)]


SRC_A = '''module Data.Array.X where

{-# INLINE f #-}
{-# INLINE CONLIKE [1] k #-}
k :: Int
k = 0
f :: Int -> Int
f x = x
-- {-# INLINE g #-} is a comment, no pragma
{-# INLINABLE [1] g #-}
g :: Int -> Int
g = f

instance (Show a,
          Eq a) => C (T a) where
  {-# INLINE m #-}
  m = id
  {-# INLINE (+.) #-}
  (+.) = const

class D a where
  {-# INLINE m #-}
  m :: a -> a
  m = id
'''
# B: g's phase moved, the instance's m NOINLINE and its context changed,
# its operator's pragma gone, and h added, spelled INLINEABLE.
SRC_B = (SRC_A.replace('{-# INLINABLE [1] g #-}', '{-# INLINABLE [2] g #-}')
         .replace('(Show a,\n          Eq a)', '(Show a)')
         .replace('  {-# INLINE m #-}\n  m = id\n  {-# INLINE (+.) #-}\n',
                  '  {-# NOINLINE m #-}\n  m = id\n')
         + '{-# INLINEABLE h #-}\nh :: Int\nh = 1\n')


def self_test():
    """Two trees of one module each, written here, whose pragmas differ in
    phase, in kind, in presence and in an instance's context alone, with a
    pragma in a comment, a class's method of an instance's name, and one
    in a build directory, which is not read."""
    bad = []
    with tempfile.TemporaryDirectory() as td:
        trees = []
        for name, text in (('a', SRC_A), ('b', SRC_B)):
            for rel in ('Data/Array/X.hs', 'dist-newstyle/Data/Array/X.hs'):
                p = os.path.join(td, name, rel)
                os.makedirs(os.path.dirname(p), exist_ok=True)
                with open(p, 'w') as fh:
                    fh.write(text if rel.startswith('Data') else
                             '{-# %sINLINE stray #-}\n'
                             % ('' if name == 'a' else 'NO'))
            trees.append(os.path.join(td, name))
        a, b = load(trees[0]), load(trees[1])
        if a.get(('Data/Array/X.hs', 'class D a', 'm', 1)) != 'INLINE':
            bad.append(f"the class's method not under its head: {sorted(a)}")
        if a.get(('Data/Array/X.hs', 'top', 'k', 1)) != 'INLINE[1]':
            bad.append(f'a CONLIKE pragma misread: {sorted(a)}')
        got = compare(a, b)
        want = ['Data/Array/X.hs [instance C (T a)] +.#1: INLINE -> none',
                'Data/Array/X.hs [instance C (T a)] m#1: INLINE -> NOINLINE',
                'Data/Array/X.hs [top] g#1: INLINABLE[1] -> INLINABLE[2]',
                'Data/Array/X.hs [top] h#1: none -> INLINABLE']
        if got != want:
            bad.append('comparison:\n  ' + '\n  '.join(got))
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            if main([trees[0], trees[0]]) != 0 or out.getvalue():
                bad.append('a tree against itself did not exit 0, silent')
        empty = os.path.join(td, 'empty')
        os.makedirs(empty)
        for argv, what in (([empty, empty], 'two trees without a pragma'),
                           ([trees[0], os.path.join(td, 'none')],
                            'a missing tree'),
                           ([trees[0]], 'one tree')):
            with contextlib.redirect_stderr(io.StringIO()):
                if main(argv) != 2:
                    bad.append(f'{what} did not exit 2')
    for x in bad:
        print('FAIL', x)
    print('self-test', 'FAILED' if bad else 'passed')
    return 1 if bad else 0


def main(argv):
    if argv == ['--self-test']:
        return self_test()
    if len(argv) != 2:
        print(__doc__.split('\n\n')[1], file=sys.stderr)
        return 2
    for t in argv:
        if not os.path.isdir(t):
            print(f'pragma-map: {t} is not a directory', file=sys.stderr)
            return 2
    try:
        a, b = load(argv[0]), load(argv[1])
    except OSError as e:  # a traceback and exit 1 before (pragma-map-02)
        print(f'pragma-map: cannot read {e.filename}: {e.strerror}',
              file=sys.stderr)
        return 2
    if not a and not b:
        print('pragma-map: no inlining pragma in either tree', file=sys.stderr)
        return 2
    for line in compare(a, b):
        print(line)
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
