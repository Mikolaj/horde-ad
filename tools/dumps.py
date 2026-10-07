"""What the readers of GHC's dump trees share, kept once so a fix lands once.

Imported by core-diff.py, pragma-calls.py, ctime-diff.py, rules-diff.py and
spec-audit.py, never run: each puts its own directory first on sys.path, as for common.py.

A dump tree is either a cabal build directory, the dumps beside the objects
under some `build/` directory, or a tree written with `-dumpdir`, which has
none. module_key names a module by its dump's path below the last `build/`,
or below the tree's root where there is none, so that one module of two
builds has one key. Keyed by the part below the last `/build/` of the whole
path, a `-dumpdir` tree kept every path whole, and two such trees shared no
module (core-diff-02, pragma-calls-03).

walk lists a tree's dumps of one kind, gzipped ones included, and read_text
reads one. core_digests reduces a Core dump to the two fingerprints an
identity verdict compares: one exact but for the timestamp lines GHC writes
under each dump's header, and one blind to unboxed numeric literals as well,
which is what an edit elsewhere moves --- a call stack carries its source line
as such a literal, so a module that inlined an `error` call from a file
since grown by a line above it differs from its other build by that alone.
"""

import gzip
import hashlib
import os
import re

TIMESTAMP = re.compile(r'^\d{4}-\d\d-\d\d \d\d:\d\d:\d\d(?:\.\d+)? UTC\n', re.M)
# 1600#, -1#, 5##, 1.5##, 2.0e-3#: an unboxed numeric literal, not the digits
# ending a name such as I# or W8#.
LITERAL = re.compile(r"(?<![\w$'])-?\d+(?:\.\d+)?(?:e-?\d+)?##?")


def module_key(path, root, suffix):
    """The key of the dump at path in the tree at root: its path relative to
    root, below the last `build/` directory where there is one, without the
    suffix (or the suffix and `.gz`)."""
    rel = os.path.relpath(path, root).replace(os.sep, '/')
    rel = ('/' + rel).rsplit('/build/', 1)[-1].lstrip('/')
    for end in (suffix + '.gz', suffix):
        if rel.endswith(end):
            return rel[:-len(end)]
    return rel


def walk(root, suffix):
    """[(path, key)] of every file under root whose name ends in suffix or in
    suffix + '.gz', sorted by path."""
    out = []
    for dp, _, fs in os.walk(root):
        for f in fs:
            if f.endswith(suffix) or f.endswith(suffix + '.gz'):
                p = os.path.join(dp, f)
                out.append((p, module_key(p, root, suffix)))
    return sorted(out)


def read_text(path):
    """A dump's text, gzipped or not; undecodable bytes replaced."""
    op = gzip.open if path.endswith('.gz') else open
    with op(path, 'rt', errors='replace') as fh:
        return fh.read()


def core_digests(text):
    """(exact, literal-blind) fingerprints of a Core dump's text."""
    exact = TIMESTAMP.sub('', text)
    blind = LITERAL.sub('N#', exact)
    return (hashlib.sha256(exact.encode()).hexdigest(),
            hashlib.sha256(blind.encode()).hexdigest())
