"""What the readers of Haskell source share, kept once so a fix lands once.

Imported by bang-drops.py, bang-lazy-check.py, hascallstack.py,
lazy-reads.py, pragma-calls.py, pragma-census.py, pragma-map.py,
src-attrib.py and workaround-cites.py, never run: each puts its own
directory first on sys.path, as for common.py.

hs_paths walks a tree's .hs files in sorted order, the build directories,
dist and dist-*, and hidden ones passed over. imports returns a module's
aliases and the modules it imports unqualified.

strip_comments blanks comments but keeps pragmas and every line break, so
a line number still names its line; an operator holding dashes, such as
`-->`, `<--` or `--->`, is no comment, and a `--` or `{-` inside a string
or character literal opens none. Block comments nest, as in GHC, so a
pragma inside one does not end it, and a `{-` inside a line comment opens
none. blank_blocks blanks the block comments alone and keeps the columns
too, for a reader of the layout, and blank_comments drops the line
comments from that besides.

split_functions files every line under the top-level definition above it,
a `data` or `newtype` under its first two words, a `class` or `instance`
under head_key's key, its whole head read to its `where` with the spaces
normalised, which pragma-map keys an instance's pragmas by too, and a
function under its name, so that two versions of a module can be compared
definition by definition; the lines above the first definition are filed
under no name and dropped. It parses the layout only, so a definition of an
infix operator files under the definition above it.
"""

import collections
import os
import re

NOT_DEFINITIONS = ('import', 'module', 'infixl', 'infixr', 'infix', 'type',
                   'deriving', 'default', 'foreign', 'pattern')


def hs_paths(root):
    """The .hs files under root in a sorted walk, the build directories,
    dist and dist-*, and hidden ones passed over; a distrib/ is source
    (hssource-05)."""
    for dp, ds, fs in os.walk(root):
        ds[:] = sorted(d for d in ds
                       if d[:1] != '.' and d.split('-')[0] != 'dist')
        yield from (os.path.join(dp, f) for f in sorted(fs)
                    if f.endswith('.hs'))


# An import: qualified before or after the module's name, an alias, and
# an import list of () with or without a hiding before it.
IMPORT = re.compile(r'^import\s+(qualified\s+)?([A-Z][\w.]*)(\s+qualified)?'
                    r'(?:\s+as\s+([A-Z][\w.]*))?(\s+hiding)?\s*(\(\s*\))?',
                    re.M)


def imports(src):
    """({alias: {module}}, [modules imported unqualified]) of a module's
    source. An import of () brings no names, and one hiding () all of them:
    pragma-census took the first to open its module and pragma-calls the
    second to open none (pragma-census-24, pragma-calls-19)."""
    aliases, opens = {}, []
    for m in IMPORT.finditer(src):
        aliases.setdefault(m.group(4) or m.group(2), set()).add(m.group(2))
        if not (m.group(1) or m.group(3)) and (m.group(5) or not m.group(6)):
            opens.append(m.group(2))
    return aliases, opens


# What a scan for comments steps over whole, so that a {- or -- inside
# opens nothing: a pragma, a string literal and a character literal, which
# stands where no name ends, so x' opens none and '"' opens no string
# (hssource-06). A line comment is two dashes or more with neither a symbol
# nor a dash on either side, so <-- and ---> are operators (hssource-07).
SYM = r"!#$%&*+./<=>?@\\^|~:"
LITERALS = (r"\{-#.*?#-\}|\"(?:[^\"\\\n]|\\.)*\""
            r"|(?<![\w'])'(?:[^'\\\n]|\\.[^'\n]*)'")
LINE_COMMENT = rf"(?<![{SYM}-])--+(?![{SYM}-])[^\n]*"
# Outside a block comment: a literal or a line comment, each stepped over,
# or a block comment's opening. Inside one: an opening, a pragma's
# included, as block comments nest, or a close.
OUTSIDE = re.compile(rf"{LITERALS}|\{{-(?!#)|{LINE_COMMENT}", re.S)
INSIDE = re.compile(r"\{-|-\}")
# A literal kept, or a line comment dropped.
LINES = re.compile(rf"({LITERALS})|{LINE_COMMENT}", re.S)


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
    return LINES.sub(lambda m: m.group(1) or '', src)


def blank_blocks(src):
    """src with each block comment blanked but for its line breaks, the
    pragmas and line comments outside them kept, and trailing blanks
    dropped: columns and line numbers kept, for pragma-census's walks
    (pragma-census-21 to -23)."""
    return re.sub(r'[ \t]+$', '',
                  sub_blocks(src, lambda c: re.sub(r'[^\n]', ' ', c)),
                  flags=re.M)


def blank_comments(src):
    """src with its block comments blanked as blank_blocks blanks them and
    its line comments dropped: columns and line numbers kept, for
    bang-lazy-check's equations (bang-lazy-check-07)."""
    return LINES.sub(lambda m: m.group(1) or '', blank_blocks(src))


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
