"""What the readers of Haskell source share, kept once so a fix lands once.

Imported by bang-drops.py and lazy-reads.py, never run: each puts its own
directory first on sys.path, as for common.py.

strip_comments blanks comments but keeps pragmas and every line break, so
a line number still names its line; an operator that begins with `--`, such
as `-->`, is no comment. split_functions files every line under the
top-level definition above it, a declaration (`data`, `newtype`, `class`,
`instance`) under its head and a function under its name, so that two
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


def split_functions(src):
    """{definition name: its lines, joined}."""
    cur, out = None, collections.defaultdict(str)
    for line in src.split('\n'):
        m = re.match(r"^(data|newtype|class|instance)\s+(\S+)", line)
        if m:
            cur = m.group(1) + ' ' + m.group(2)
        else:
            m = re.match(r"^([a-z_][\w']*)\b", line)
            if m and m.group(1) not in NOT_DEFINITIONS:
                cur = m.group(1)
        if cur is not None:
            out[cur] += line + '\n'
    return out
