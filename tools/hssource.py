"""What the readers of Haskell source share, kept once so a fix lands once.

Imported by bang-drops.py, hascallstack.py, lazy-reads.py, pragma-calls.py,
pragma-census.py, pragma-map.py and workaround-cites.py, never run: each
puts its own directory first on sys.path, as for common.py.

hs_paths walks a tree's .hs files in sorted order, the dist* build
directories and hidden ones passed over.

strip_comments blanks comments but keeps pragmas and every line break, so
a line number still names its line; an operator that begins with `--`, such
as `-->`, is no comment. Block comments nest, as in GHC, so a pragma inside
one does not end it, and a `{-` inside a line comment opens none.
blank_blocks blanks the block comments alone and keeps the columns too,
for a reader of the layout. split_functions files every line under the
top-level definition above it, a `data` or `newtype` under its first two
words, a `class` or `instance` under its whole head, read to its `where`
with the spaces normalised, and a function under its name, so that two
versions of a module can be compared definition by definition; the lines
above the first definition are filed under no name and dropped. It reads
the layout only, so a definition of an infix operator files under the
definition above it.
"""

import collections
import os
import re

NOT_DEFINITIONS = ('import', 'module', 'infixl', 'infixr', 'infix', 'type',
                   'deriving', 'default', 'foreign', 'pattern')


def hs_paths(root):
    """The .hs files under root in a sorted walk, the dist* build
    directories and hidden ones passed over."""
    for dp, ds, fs in os.walk(root):
        ds[:] = sorted(d for d in ds if not d.startswith(('.', 'dist')))
        yield from (os.path.join(dp, f) for f in sorted(fs)
                    if f.endswith('.hs'))


# Outside a block comment: a pragma or a line comment, each stepped over so
# that a {- inside it opens nothing, or a block comment's opening. Inside
# one: an opening, a pragma's included, as block comments nest, or a close.
OUTSIDE = re.compile(r"\{-#.*?#-\}|\{-(?!#)|(?<![!#$%&*+./<=>?@\\^|~:])--"
                     r"(?![!#$%&*+./<=>?@\\^|~:])[^\n]*", re.S)
INSIDE = re.compile(r"\{-|-\}")


def block_comments(src):
    """(start, end) of each block comment of src, the ones nested in it
    inside its span, an opening never closed left as code. A pragma inside
    one ended it (hssource-03), and a {- inside a line comment opened one
    (hssource-04)."""
    spans, pos, depth, start = [], 0, 0, 0
    while m := (INSIDE if depth else OUTSIDE).search(src, pos):
        pos = m.end()
        if m.group(0) == '{-':
            if depth == 0:
                start = m.start()
            depth += 1
        elif m.group(0) == '-}':
            depth -= 1
            if depth == 0:
                spans.append((start, pos))
    return spans


def sub_blocks(src, repl):
    """src with each block comment c replaced by repl(c)."""
    out, kept = [], 0
    for s, e in block_comments(src):
        out += [src[kept:s], repl(src[s:e])]
        kept = e
    return ''.join(out) + src[kept:]


def strip_comments(src):
    src = sub_blocks(src, lambda c: '\n' * c.count('\n'))
    return '\n'.join(re.sub(r'--(?![!#$%&*+./<=>?@\\^|~:]).*$', '', line)
                     for line in src.split('\n'))


def blank_blocks(src):
    """src with each block comment blanked but for its line breaks, the
    pragmas and line comments outside them kept, and trailing blanks
    dropped: columns and line numbers kept, for pragma-census's walks
    (pragma-census-21 to -23)."""
    return re.sub(r'[ \t]+$', '',
                  sub_blocks(src, lambda c: re.sub(r'[^\n]', ' ', c)),
                  flags=re.M)


def head_key(lines, i):
    """The key of the class or instance whose head starts at lines[i]: the
    head to its `where`, its continuation lines included, the spaces
    normalised. Keyed by the first token, every head beginning with one
    constraint, or with a bare `(`, shared a key (hssource-01)."""
    head, j = [lines[i]], i + 1
    while (not re.search(r'\bwhere\b', head[-1]) and j < len(lines)
           and lines[j][:1] in (' ', '\t')):
        head.append(lines[j])
        j += 1
    s = ' '.join(re.split(r'\bwhere\b', ' '.join(head))[0].split())
    s = re.sub(r'([(\[,]|=>) ', r'\1', s)
    return re.sub(r' ([)\],]|=>)', r'\1', s)


def split_functions(src):
    """{definition name: its lines, joined}."""
    cur, out = None, collections.defaultdict(str)
    lines = src.split('\n')
    for i, line in enumerate(lines):
        m = re.match(r"^(data|newtype|class|instance)\s+(\S+)", line)
        if m and m.group(1) in ('class', 'instance'):
            cur = head_key(lines, i)
        elif m:
            cur = m.group(1) + ' ' + m.group(2)
        else:
            # Not \b after the name, which backtracks past a prime and
            # filed f' under f (hssource-02).
            m = re.match(r"^([a-z_][\w']*)(?![\w'])", line)
            if m and m.group(1) not in NOT_DEFINITIONS:
                cur = m.group(1)
        if cur is not None:
            out[cur] += line + '\n'
    return out
