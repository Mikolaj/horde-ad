"""What the readers of Haskell source share, kept once so a fix lands once.

Imported by bang-drops.py, hascallstack.py, lazy-reads.py and
pragma-census.py, never run: each puts its own directory first on sys.path,
as for common.py.

strip_comments blanks comments but keeps pragmas and every line break, so
a line number still names its line; an operator that begins with `--`, such
as `-->`, is no comment. split_functions files every line under the
top-level definition above it, a `data` or `newtype` under its first two
words, a `class` or `instance` under its whole head, read to its `where`
with the spaces normalised, and a function under its name, so that two
versions of a module can be compared definition by definition; the lines
above the first definition are filed under no name and dropped. It reads
the layout only, so a definition of an infix operator files under the
definition above it.
"""

import collections
import re

NOT_DEFINITIONS = ('import', 'module', 'infixl', 'infixr', 'infix', 'type',
                   'deriving', 'default', 'foreign', 'pattern')


def strip_comments(src):
    src = re.sub(r'\{-(?!#).*?-\}', lambda m: '\n' * m.group(0).count('\n'),
                 src, flags=re.S)
    return '\n'.join(re.sub(r'--(?![!#$%&*+./<=>?@\\^|~:]).*$', '', line)
                     for line in src.split('\n'))


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
