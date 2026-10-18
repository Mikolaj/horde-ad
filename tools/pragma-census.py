#!/usr/bin/env python3
"""List the overloaded bindings of a source tree that carry no pragma.

Usage: python3 tools/pragma-census.py [--skip FILE]... SRC
       python3 tools/pragma-census.py --rule [--skip FILE]... SRC
       python3 tools/pragma-census.py --write [--release] [--keep FILE]
                                      [--skip FILE]... SRC
       python3 tools/pragma-census.py --self-test

`--skip FILE`, a path relative to SRC, leaves that `.hs` file out of every
mode, `--write` included, for code a ruling puts out of scope; the files
left out head the report, and one naming no file under SRC stops the run.

For every `.hs` file under SRC, the top-level functions whose signature has
a context, the methods of the instances that have one and the default
methods of every class, which carry
no `INLINE`, `INLINABLE`, `NOINLINE` or `SPECIALISE` pragma of their name:
what docs/perf-checklist.md's P asks a pragma, or a comment above the
haddock, of where their callers' speed is protected. A context counts only where it
holds a class constraint. `HasCallStack`, an equality
`a ~ b`, a `TypeError` and a type-level `<=` give a caller nothing
to specialise, so a signature or an instance with only those is passed over,
as are a `TypeError` instance, whose methods cannot be called, and a method
defined as `undefined`.

A signature may span lines, its `::` on the line of its names or starting
the next, its context running to the first `=>` outside parentheses,
a rank-2 argument's context being its own; a method may be defined prefix,
as an operator section, `(<*>) = ...`, or infix, `x == y`,
`` a@(T x) `compare` b `` or `T u ==. T v`, and on the instance's own line
after its `where`;
an instance or class head may span lines too, a comment line inside it left
out, and only the lines at the body's own indentation define a method,
the deeper ones continuing it, a blank line or a comment at column 0 ending
the body only where the code after it is not indented, the lines of a block
comment being read as blank. A method's pragma
is looked for in its instance or class, a top-level function's anywhere
in its module, and a line `m :: ...` or `m:: ...` in an instance or class
is its signature while a definition holding `(Proxy :: Proxy n)` is not.
A default method defined as `undefined` or `error ...` is passed over, as
is a default signature. It is a reader of lines and not a parser:
a top-level binding without a signature, a local function and a pragma
naming a binding of another module are not seen, and its verdict is a list
of candidates for P's rule, which only the callers decide.

`--rule` checks every top-level function with a signature, every
instance method and every class default method against the pragma P's rule
gives it by its own type: INLINE where the type takes an argument of function
type; otherwise INLINABLE where it is overloaded, a class constraint in the
signature, in the instance's context or in the class method's own type,
and a default method always, by its class; otherwise none. A method's type
is its class's, read from the tree's class declarations or from a table of
the standard classes. SPECIALISE counts as INLINABLE. A binding wants INLINE
where it is directly fusing (F1): its body names build or augment and its
result is a list, or it takes a list and its body names foldr or another
good consumer defined outside the tree, sum, all or map among them, lists of
Int or Bool, a shape's, left out, each equation naming that list once, not
taking it apart by a pattern. A binding also wants INLINE where it
forwards to one needing it: its body calls that binding, by its name in its
own module, in one it imports unqualified or through a qualified alias, a
module defining no such name followed through its unqualified imports as a
facade re-exports them, or through a class method one of whose instances it
is, and its type shares a list type with it, or, where the callee's INLINE
stands on a comment giving P's reason that cites no F1, the call heads the
right-hand side of its first equation, constructors applied to it aside. A
directly fusing binding, and an INLINE binding whose comment above it gives
P's reason, need it, and so, to a fixed point, does each forwarder. A
binding wants INLINE where it is a thin wrapper too: the right-hand side
of each of its equations, unguarded and holding no local binding,
comprehension, case, conditional or do block, makes at most one call, its
constructors, the fields of the tree's newtypes, `coerce`, `$` and `.` aside, any other
operator, a backticked name and a range each counting as one. A
binding whose comment names F1 but whose body hands a list of its type to a
tree binding is listed too: the innermost binding should carry it; and so is
a directly fusing binding whose type does not want INLINE already and whose
comment gives no P's reason citing F1.
A binding wants INLINE where its type names a sum marked as never to be
built (A3), by a plain comment directly above the type's haddock whose
first line opens `-- Unmaterialized:`: a data type of two constructors or
more, read across its lines without their comments, or a type synonym,
which is taken for the sum it names; a product marked so is left
to measurement. The binding's own comment must give P's reason naming each
such sum it takes or returns and citing A3, or it is listed too. Its callers
need nothing for it.
It lists each binding whose pragma differs, unless a plain comment directly
above its haddock, or for a method above the method or its instance or
class, a default method's signature too, gives P's reason, a declaration
covers it, or the pragma has a phase;
the recursive bindings the rule makes INLINE that carry INLINE, which want
a wrapper over a worker instead, a body naming its own name outside string
literals being recursive; and the methods of classes whose method types
it does not know. A method defined
as `undefined` or `error ...` is passed over.

P's reason is a comment whose first line opens with the pragma the binding
carries, or with No pragma for none, and a colon, `-- INLINE:`, and which
cites one of the checks I1, I2, I3, F1, A3, S2, W3 and W4, a GHC version,
HEAD included, with a date, or, saying see, another comment.

A declaration is a comment saying INLINE throughout, INLINABLE (or
INLINEABLE) throughout or No pragma throughout, and it may go on with `but`
and the names it leaves out, a method's as `Class.method` or `method`, up to
a colon, a semicolon or a full stop: `INLINE throughout but rotate and
window:`. In the module's header, above its `module` line, it covers each
binding of the module carrying that pragma, or none, that it does not name;
directly above an instance or class, each of its methods, overriding the
module's there. A binding it names is held to the rule and to its own
comment, or to the declaration's where that cites what P's reason does, F1
for a directly fusing one. It lists each binding of a declaration's scope
that carries another pragma and is not named there; each name that is no
binding of that scope, or only of ones carrying the declared pragma; and each
word after the `but` that is no name.

`--write` writes into SRC the pragmas `--rule` lists as differing, round
after round until a round has none to write, then prints what `--rule`
still lists. It adds or strengthens a pragma, none to INLINABLE or INLINE
and INLINABLE to INLINE, which the rule asks for whatever is measured; with
`--release` it weakens and removes them too, building the tree on which
P's rule on removing measures a release, not one to commit. A finding
is left as it is where a line of the `--keep` file gives its file and name
as `--rule` prints them, a line number there being ignored. It writes no
comment, leaves a NOINLINE and a SPECIALISE alone, puts a new pragma
directly above the signature, or a method's first equation, and lists what
it left and each keep line matching no finding.

Exit 0 when every overloaded binding carries a pragma, or with `--rule`
or `--write` when nothing differs, 1 when one does not, 2 when SRC holds no
`.hs` file, a keep line is not in a finding's form or a round's writes
did not take.
"""

import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hssource import blank_blocks, strip_comments  # noqa: E402

# A pragma's kind ends at a word boundary, and CONLIKE, or a SPECIALISE's
# INLINE or NOINLINE, may stand between it and the phase or the name:
# INLINE first in the alternation read INLINEABLE f as an INLINE of ABLE,
# INLINE CONLIKE g as one of CONLIKE (pragma-census-17, -18).
KIND = r'INLINE|INLINABLE|INLINEABLE|NOINLINE|SPECIALI[SZ]E'
MODIFIERS = r'\b\s*(?:(?:CONLIKE|(?:NO)?INLINE)\b\s*)*'
PRAGMA = re.compile(r'\{-#\s*(?:' + KIND + ')' + MODIFIERS
                    + r'(?:\[~?\d+\]\s*)?\(?([^\s)#,]+)')
TOP_SIG = re.compile(r"^([a-z_][\w']*(?:\s*,\s*[a-z_][\w']*)*"
                     r"|\([!#$%&*+./<=>?@\\^|~:-]+\))\s*::(.*)")
OP = r"[!#$%&*+./<=>?@\\^|~:-]+"
NAMES = (r"(?:[a-z_][\w']*|\(" + OP + r"\))"
         r"(?:\s*,\s*(?:[a-z_][\w']*|\(" + OP + r"\)))*")
SPLIT = re.compile(r"^\s*(" + NAMES + r")\s*(?:--.*)?$")
SECTION = re.compile(r'^\((' + OP + r')\)')
INFIX_OP = re.compile(r"\s+(`[\w']+`|" + OP + r")(?=\s)")
SIGNATURE = re.compile(r"^(?:[\w']+|\(" + OP + r"\))(?:\s*,\s*[\w']+)*"
                       r"\s*::(?![!#$%&*+./<=>?@\\^|~:-])")
# A line at column 0 that is no code: a pragma or a line comment.
ASIDE = re.compile(r"\{-#|--(?![!#$%&*+./<=>?@\\^|~:])")


def code(lines):
    """LINES with their comments blanked, pragmas and line breaks kept: what
    the pragma regexes are run over. Over the raw lines a commented-out pragma
    read as the binding's own (pragma-census-14 to -16)."""
    return strip_comments('\n'.join(lines)).split('\n')


def past_asides(lines, j):
    """The first line from j that is neither blank nor a pragma or a comment
    at column 0, blank_blocks having blanked the block comments."""
    while j < len(lines) and (not lines[j].strip() or ASIDE.match(lines[j])):
        j += 1
    return j


def constraints(ctx):
    """The class constraints of a context, the rest dropped."""
    ctx = re.sub(r'^\s*forall\b[^.]*\.', '', ctx).strip()
    if ctx.startswith('(') and ctx.endswith(')'):
        depth = 0
        for i, ch in enumerate(ctx):
            depth += ch == '('
            depth -= ch == ')'
            if depth == 0 and i < len(ctx) - 1:
                break
        else:
            ctx = ctx[1:-1]
    parts, depth, cur = [], 0, ''
    for ch in ctx:
        depth += ch in '(['
        depth -= ch in ')]'
        if ch == ',' and depth == 0:
            parts.append(cur)
            cur = ''
        else:
            cur += ch
    parts.append(cur)
    return [' '.join(p.split()) for p in parts
            if p.strip() and p.strip() != 'HasCallStack' and '~' not in p
            and not p.strip().startswith('TypeError') and '<=' not in p]


def context(sig):
    """The context of a signature, before its first `=>` outside parentheses
    and brackets, or None where it has none."""
    depth = 0
    for i, ch in enumerate(sig):
        depth += ch in '(['
        depth -= ch in ')]'
        if depth == 0 and sig.startswith('=>', i):
            return sig[:i]
    return None


def bracket_end(s, i):
    """Where the bracketed group opening at s[i] closes, or None."""
    close = {'(': ')', '[': ']'}[s[i]]
    depth = 0
    for j in range(i, len(s)):
        depth += s[j] == s[i]
        depth -= s[j] == close
        if depth == 0:
            return j + 1
    return None


def pattern_end(s):
    """Where the first pattern of a definition ends: a variable, a constructor
    with its arguments, `T u` in `T u ==. T v`, or a parenthesised pattern,
    either behind an as-pattern's `x@`."""
    m = re.match(r"[\w']+@", s)
    i = m.end() if m else 0
    if s[i:i + 1] == '(':
        return bracket_end(s, i)
    m = re.match(r"[\w'.]+", s[i:])
    if not m:
        return None
    end = i + m.end()
    while s[i:i + 1].isupper():
        m = re.match(r"\s+(?=[\w'(\[])", s[end:])
        if not m:
            break
        j = end + m.end()
        end = (bracket_end(s, j) if s[j] in '([' else
               j + re.match(r"[\w'.]+", s[j:]).end())
        if end is None:
            return None
    return end


def method_name(line):
    """The method a line of an instance body defines, or None."""
    s = line.strip()
    if not s or s.startswith(('--', '{-', '|')) or SIGNATURE.match(s):
        return None
    m = SECTION.match(s)
    if m:
        return m.group(1)
    end = pattern_end(s)
    m = INFIX_OP.match(s, end) if end else None
    if m and m.group(1) not in ('=', '|'):
        return m.group(1).strip('`')
    m = re.match(r"^([a-z_][\w']*)", s)
    return m.group(1) if m else None


def indent(line):
    return len(line) - len(line.lstrip())


def split_signature(lines, n, k=None):
    """The names of a signature at line n whose :: starts the next line,
    indented deeper, before line k, or None."""
    m = SPLIT.match(lines[n])
    k = len(lines) if k is None else k
    if m and n + 1 < k and lines[n + 1].lstrip().startswith('::') \
            and indent(lines[n + 1]) > indent(lines[n]):
        return m.group(1)
    return None


def top_signature(lines, i):
    """TOP_SIG's match at line i, or SPLIT's where the signature's ::
    starts the next line, or None."""
    m = TOP_SIG.match(lines[i])
    if m is None and lines[i][:1] not in (' ', '\t') \
            and split_signature(lines, i) is not None:
        m = SPLIT.match(lines[i])
    return m


def signature_at(lines, i, m):
    """The signature top_signature matched as m at line i, its lines joined
    and the leading :: of a split one dropped, and the line after it."""
    sig, j = (m.group(2) if m.re is TOP_SIG else ''), i + 1
    while (j < len(lines) and lines[j][:1] in (' ', '\t')
           and not lines[j].strip().startswith('--')):
        sig += ' ' + lines[j]
        j += 1
    return (sig if m.re is TOP_SIG else sig.strip()[2:]), j


def decl_at(lines, i, kw='instance'):
    """(head, its last line, the line after the body, the head's match) of the
    instance, or the class with kw `class`, whose head starts at line i, the
    comment lines inside the head left out."""
    head, j = lines[i], i
    while not re.search(r'\bwhere\b', head) and j + 1 < len(lines) \
            and lines[j + 1][:1] in (' ', '\t'):
        j += 1
        if not lines[j].lstrip().startswith('--'):
            head += ' ' + lines[j].strip()
    hm = re.match(r'^' + kw + r'\b(.*?)(?:\bwhere\b(.*))?$', head)
    k = j + 1
    while k < len(lines) and (lines[k][:1] in (' ', '\t') or gap(lines[k])):
        if gap(lines[k]):
            n = k
            while n < len(lines) and gap(lines[n]):
                n += 1
            if n == len(lines) or lines[n][:1] not in (' ', '\t'):
                break
            k = n
            continue
        k += 1
    return head, j, k, hm


def gap(line):
    """Whether a line is blank or a comment at column 0, which ends a body
    only where the next line of code is not indented."""
    return not line.strip() or bool(re.match(r'--+(?!' + OP + ')', line))


def instance_body(lines, j, k, hm):
    """[(line, text)] of an instance's or a class's lines that can define
    a method: what follows its where on the head's last line, and the lines
    at the body's own indentation."""
    return [(j, hm.group(2) or '')] + [
        (n, b) for n, b in base_lines(lines, j, k)
        if split_signature(lines, n, k) is None]


def base_lines(lines, j, k):
    """[(line, text)] of the lines after j and before k at the body's own
    indentation."""
    rest = [(n, lines[n]) for n in range(j + 1, k) if not gap(lines[n])]
    base = min((indent(b) for _, b in rest), default=0)
    return [(n, b) for n, b in rest if indent(b) == base]


def class_at(lines, i):
    """(class, {method: (type, its signature's line)}, [(line, text)] of the
    body's lines that can define a default method, {name: (kind, phased)} of
    its pragmas, the line after the body) of the class whose head starts at
    line i, the class None where the head names none."""
    head, j, k, hm = decl_at(lines, i, 'class')
    if not hm:
        return None, {}, [], {}, k
    h = hm.group(1)
    ctx = context(h)
    h = h[len(ctx) + 2:] if ctx is not None else h
    words = re.findall(r"[A-Za-z_][\w']*", h.split('|')[0])
    body = instance_body(lines, j, k, hm)
    sigs = body_signatures(lines, j, k)
    pk = {}
    for b in code(lines[i:k]):
        for p in KINDS.finditer(b):
            pk[p.group(3)] = (p.group(1), bool(p.group(2)))
    return (words[0] if words else None), sigs, body, pk, k


def body_signatures(lines, j, k):
    """{method: (type, its signature's line)} of the signatures in the body
    of a class or an instance whose head ends at line j and whose body ends
    before line k."""
    sigs = {}
    for n, b in base_lines(lines, j, k):
        split = split_signature(lines, n, k)
        sm = re.match(r"^\s*(" + NAMES + r")\s*::(.*)", b)
        if split or sm:
            names, ty = (split, '') if split else sm.groups()
            c = n + 1
            while c < k and indent(lines[c]) > indent(b) and lines[c].strip():
                ty += ' ' + lines[c].strip()
                c += 1
            ty = ty.strip()[2:] if split else ty
            for name in re.split(r'\s*,\s*', names):
                sigs[name.strip('() ')] = (ty, n)
    return sigs


def stub(b):
    """Whether a method's defining line defines it as undefined or error."""
    rhs = b.split('=', 1)[1].strip() if '=' in b else ''
    return rhs == 'undefined' or rhs.startswith('error ')


def defaults(lines, i):
    """(class, [(line, method, its signature's line, its pragma or None)],
    the line after the body) of the default methods the class at line i
    defines, one an equation group, those defined as undefined or error left
    out."""
    cls, sigs, body, pk, k = class_at(lines, i)
    out, seen = [], set()
    for n, b in body:
        name = method_name(b)
        if name in sigs and name not in seen and not stub(b):
            out.append((n, name, sigs[name][1], pk.get(name)))
        seen.add(name)
    return cls, out, k


def census(text):
    """([(line, name, constraints)] of the top-level functions,
    [(line, class, method)] of the instance methods and [(line, class,
    method)] of the class default methods carrying no pragma."""
    lines = blank_blocks(text).split('\n')
    module_pragmas = {m.group(1) for line in code(lines)
                      for m in PRAGMA.finditer(line)}
    funs, meths, dms = [], [], []
    i = 0
    while i < len(lines):
        line = lines[i]
        m = top_signature(lines, i)
        if m:
            sig, j = signature_at(lines, i, m)
            ctx = context(sig)
            if ctx is not None:
                cs = constraints(ctx)
                for name in re.split(r'\s*,\s*', m.group(1).strip()):
                    name = name.strip('()')
                    if cs and name not in module_pragmas:
                        funs.append((i + 1, name, cs))
            i = j
            continue
        if re.match(r'^class\b', line):
            cls, dm, k = defaults(lines, i)
            dms += [(n + 1, cls, name) for n, name, _, p in dm if p is None]
            i = k
            continue
        if line.startswith('instance'):
            head, j, k, hm = decl_at(lines, i)
            if hm and '=>' in hm.group(1):
                ctx, cls_head = hm.group(1).split('=>', 1)
                cs = constraints(ctx)
                if cs:
                    cls = cls_head.split()[0]
                    body = instance_body(lines, j, k, hm)
                    pragmas = {p.group(1) for b in code(lines[i:k])
                               for p in PRAGMA.finditer(b)}
                    seen = set()
                    for n, b in body:
                        name = method_name(b)
                        if name and name not in seen and name not in pragmas \
                                and not b.rstrip().endswith('= undefined'):
                            meths.append((n + 1, cls, name))
                        seen.add(name)
            i = k
            continue
        i += 1
    return funs, meths, dms


KINDS = re.compile(r'\{-#\s*(' + KIND + ')' + MODIFIERS
                   + r'(\[~?\d+\]\s*)?\(?([^\s)#,]+)')
NOTE = re.compile(r'\b(?:INLINE|INLINABLE|NOINLINE)\b|\bpragma\b')
F1NOTE = re.compile(r'\bF1\b')
A3NOTE = re.compile(r'\bA3\b')
UNMAT = re.compile(r'--\s*Unmaterialized:')
TYPE_DECL = re.compile(r"^(?:data|newtype|type)\s+([A-Z][\w']*)")
# The methods of the standard classes, the class's own type spelled self.
UN, BIN = 'self -> self', 'self -> self -> self'
STD = {
    'Functor': {'fmap': '(a -> b) -> self a -> self b',
                '<$': 'a -> self b -> self a'},
    'Foldable': {'foldr': '(a -> b -> b) -> b -> self a -> b',
                 "foldr'": '(a -> b -> b) -> b -> self a -> b',
                 'foldl': '(b -> a -> b) -> b -> self a -> b',
                 "foldl'": '(b -> a -> b) -> b -> self a -> b',
                 'foldr1': '(a -> a -> a) -> self a -> a',
                 'foldl1': '(a -> a -> a) -> self a -> a',
                 'foldMap': 'Monoid m => (a -> m) -> self a -> m',
                 'toList': 'self a -> [a]', 'null': 'self a -> Bool',
                 'length': 'self a -> Int',
                 'elem': 'Eq a => a -> self a -> Bool',
                 'sum': 'Num a => self a -> a',
                 'product': 'Num a => self a -> a',
                 'maximum': 'Ord a => self a -> a',
                 'minimum': 'Ord a => self a -> a'},
    'Traversable': {
        'traverse': 'Applicative f => (a -> f b) -> self a -> f (self b)',
        'sequenceA': 'Applicative f => self (f a) -> f (self a)',
        'mapM': 'Monad m => (a -> m b) -> self a -> m (self b)',
        'sequence': 'Monad m => self (m a) -> m (self a)'},
    'Applicative': {'pure': 'a -> self a',
                    '<*>': 'self (a -> b) -> self a -> self b',
                    'liftA2': '(a -> b -> c) -> self a -> self b -> self c',
                    '*>': 'self a -> self b -> self b',
                    '<*': 'self a -> self b -> self a'},
    'Num': {'+': BIN, '-': BIN, '*': BIN, 'negate': UN, 'abs': UN,
            'signum': UN, 'fromInteger': 'Integer -> self'},
    'Fractional': {'/': BIN, 'recip': UN, 'fromRational': 'Rational -> self'},
    'Floating': dict({'pi': 'self', '**': BIN, 'logBase': BIN},
                     **{f: UN for f in ('exp', 'log', 'sqrt', 'sin', 'cos',
                                        'tan', 'asin', 'acos', 'atan', 'sinh',
                                        'cosh', 'tanh', 'asinh', 'acosh',
                                        'atanh', 'log1p', 'expm1')}),
    'Real': {'toRational': 'self -> Rational'},
    'Enum': {'toEnum': 'Int -> self', 'fromEnum': 'self -> Int',
             'succ': UN, 'pred': UN, 'enumFrom': 'self -> [self]',
             'enumFromThen': 'self -> self -> [self]',
             'enumFromTo': 'self -> self -> [self]',
             'enumFromThenTo': 'self -> self -> self -> [self]'},
    'Integral': {'quot': BIN, 'rem': BIN, 'div': BIN, 'mod': BIN,
                 'quotRem': 'self -> self -> (self, self)',
                 'divMod': 'self -> self -> (self, self)',
                 'toInteger': 'self -> Integer'},
    'Eq': {'==': 'self -> self -> Bool', '/=': 'self -> self -> Bool'},
    'Ord': {'compare': 'self -> self -> Ordering', '<': 'self -> self -> Bool',
            '<=': 'self -> self -> Bool', '>': 'self -> self -> Bool',
            '>=': 'self -> self -> Bool', 'max': BIN, 'min': BIN},
    'Show': {'showsPrec': 'Int -> self -> ShowS', 'show': 'self -> String',
             'showList': '[self] -> ShowS'},
    'Read': {'readsPrec': 'Int -> ReadS self', 'readList': 'ReadS [self]'},
    'Pretty': {'pPrintPrec': 'PrettyLevel -> Rational -> self -> Doc',
               'pPrint': 'self -> Doc',
               'pPrintList': 'PrettyLevel -> [self] -> Doc'},
    'NFData': {'rnf': 'self -> ()'},
    'Arbitrary': {'arbitrary': 'Gen self', 'shrink': 'self -> [self]'},
    'Semigroup': {'<>': BIN},
    'Monoid': {'mempty': 'self'},
}


def depth0(s, sep):
    """The parts of s split at sep outside parentheses and brackets."""
    parts, depth, cur, i = [], 0, '', 0
    while i < len(s):
        ch = s[i]
        depth += ch in '(['
        depth -= ch in ')]'
        if depth == 0 and s.startswith(sep, i):
            parts.append(cur)
            cur, i = '', i + len(sep)
            continue
        cur += ch
        i += 1
    return parts + [cur]


def body_type(ty):
    """A type behind its foralls and its context."""
    ty = re.sub(r'^\s*forall\b[^.]*\.', '', ty)
    ctx = context(ty)
    return ty[len(ctx) + 2:] if ctx is not None else ty


def fun_arg(ty):
    """Whether a type takes an argument of function type."""
    for arg in depth0(body_type(ty), '->')[:-1]:
        a = arg.strip()
        if a.startswith('(') and a.endswith(')') and \
                len(depth0(a[1:-1], '->')) > 1:
            return True
    return False


def overloaded(ty):
    ctx = context(re.sub(r'^\s*forall\b[^.]*\.', '', ty))
    return ctx is not None and bool(constraints(ctx))


def want(ty, overloaded_too):
    """(pragma, reasons) the rule gives a binding of type ty."""
    if fun_arg(ty):
        return 'INLINE', ['function argument']
    if overloaded_too or overloaded(ty):
        return 'INLINABLE', ['class constraint']
    return 'none', ['no class constraint']


def plain_lines(lines, i):
    """The plain comment lines directly above line i, above the pragmas and
    the haddock directly above it, those at line i's own indentation:
    a deeper one ends the body above."""
    k = i - 1
    while k >= 0 and indent(lines[k]) == indent(lines[i]) and (
            lines[k].lstrip().startswith('{-#')
            or lines[k].lstrip().startswith('--')):
        k -= 1
    block = [x.lstrip() for x in lines[k + 1:i]]
    plain, inside = [], False
    for x in block:
        if x.startswith(('-- |', '-- ^')):
            inside = True
        elif not x.startswith('--'):
            inside = False
        elif not inside:
            plain.append(x)
    return plain


def noted(lines, i, pat=NOTE):
    """Whether the plain comment lines above line i name a pragma, or match
    pat."""
    plain = plain_lines(lines, i)
    return any(pat.search(x) for x in plain)


LEAD = re.compile(r'--\s*(INLINE(?: \[~?\d+\])?|INLINABLE|INLINEABLE|NOINLINE'
                  r'|SPECIALI[SZ]E|No pragma):')
CITE = re.compile(r'\b(?:I[123]|F1|A3|S2|W[34])\b|\bsee\b')
VERSION = re.compile(r'\bGHC (?:\d+\.\d+[\d.]*|HEAD)\b')
DATE = re.compile(r'\b\d{4}-\d{2}-\d{2}\b')


def reasoned(lines, i, has):
    """Whether the plain comment above line i gives the reason P asks of a
    binding carrying has: its first line opens with that pragma, or with
    No pragma for none, and a colon, and it cites one of the checks, a GHC
    version with a date, or, saying see, another comment."""
    plain = plain_lines(lines, i)
    m = LEAD.match(plain[0]) if plain else None
    if not m:
        return False
    lead = re.sub(r' \[.*', '', m.group(1))
    lead = {'INLINEABLE': 'INLINABLE', 'SPECIALISE': 'INLINABLE',
            'SPECIALIZE': 'INLINABLE', 'No pragma': 'none'}.get(lead, lead)
    text = ' '.join(plain)
    cited = CITE.search(text) or (VERSION.search(text) and DATE.search(text))
    return lead == has and bool(cited)


# Its exceptions run to a colon, a semicolon or a full stop, a dot inside
# a qualified name not ending them.
DECL = re.compile(r'\b(INLINE|INLINABLE|INLINEABLE|[Nn]o pragma) throughout\b'
                  r'(?:\s+but\s+((?:[^:;.]|\.(?=\S))*))?')
EXCEPTION = re.compile(r"^(?:[A-Z][\w']*\.)?(?:[a-z_][\w']*|" + OP + r")$")


class Decl:
    """A declaration: the pragma it covers, `none` for No pragma throughout;
    the names it leaves out after its `but`, a method's as `Class.method` or
    `method`, and the words there that are no name; whether its text cites
    what P's reason does, and F1; its line, from 1."""

    def __init__(self, pragma, but, bad, cited, f1, line):
        self.pragma, self.but, self.bad = pragma, but, bad
        self.cited, self.f1, self.line = cited, f1, line

    def names(self, name):
        return name in self.but or name.rsplit('.', 1)[-1] in self.but

    def covers(self, name, has):
        return has == self.pragma and not self.names(name)


def declared(comments, line=0):
    """The declaration among comment lines, read joined, or None where they
    make none."""
    text = ' '.join(re.sub(r'^\s*--\s?', '', x) for x in comments)
    m = DECL.search(text)
    if not m:
        return None
    pragma = {'INLINEABLE': 'INLINABLE', 'No pragma': 'none',
              'no pragma': 'none'}.get(m.group(1), m.group(1))
    words = [x.strip().strip('`') for x in
             re.split(r',\s*(?:and\s+)?|\s+and\s+', (m.group(2) or '').strip())
             if x.strip()]
    words = [x[1:-1] if x.startswith('(') and x.endswith(')') else x
             for x in words]
    cited = bool(CITE.search(text) or (VERSION.search(text)
                                       and DATE.search(text)))
    return Decl(pragma, [x for x in words if EXCEPTION.match(x)],
                [x for x in words if not EXCEPTION.match(x)], cited,
                bool(F1NOTE.search(text)), line)


def class_methods(text):
    """{class: {method: type}} of the classes a module declares."""
    lines, out = text.split('\n'), {}
    for i, line in enumerate(lines):
        if re.match(r'^class\b', line):
            cls, sigs, _, _, _ = class_at(lines, i)
            if cls:
                out[cls] = {n: ty for n, (ty, _) in sigs.items()}
    return out


def definition(lines, start, name):
    """The equations of name from line start, joined, their string literals
    and comments blanked and each one's leading name dropped; a pragma or
    a comment at column 0 between them is passed over. A line is one of
    them by the name ending where it does: read by its prefix, foo's ran on
    into foobar's (pragma-census-20)."""
    body, j = [], start
    pat = re.compile(r"(?<![\w.'])" + re.escape(name) + r"(?![\w'])")
    while j < len(lines):
        line = lines[j]
        if line[:1] not in (' ', '\t') and line.strip():
            if past_asides(lines, j) > j:
                j = past_asides(lines, j)
                continue
            if not pat.match(line):
                break
        line = re.sub(r'"(?:[^"\\]|\\.)*"', '""', line)
        line = re.sub(r'(^|\s)--(\s.*)?$', '', line)
        body.append(pat.sub('', line, count=1) if pat.match(line) else line)
        j += 1
    return ' '.join(x for x in body if not x.lstrip().startswith('--'))


def recursive(lines, start, name):
    """Whether the equations of name from line start mention name."""
    return bool(re.search(r"(?<![\w.'])" + re.escape(name) + r"(?![\w'])",
                          definition(lines, start, name)))


def module_info(text):
    """(the module's name, {alias: {module}}, [modules imported unqualified])."""
    m = re.search(r'^module\s+([A-Z][\w.]*)', text, re.M)
    aliases, opens = {}, []
    for im in re.finditer(r'^import\s+(qualified\s+)?([A-Z][\w.]*)'
                          r'(\s+qualified)?(?:\s+as\s+([A-Z][\w.]*))?',
                          text, re.M):
        aliases.setdefault(im.group(4) or im.group(2), set()).add(im.group(2))
        if not (im.group(1) or im.group(3)):
            opens.append(im.group(2))
    return (m.group(1) if m else ''), aliases, opens


def lists_of(ty):
    """The list types a type holds, promoted lists left out."""
    out = set()
    for start in (i for i, ch in enumerate(ty)
                  if ch == '[' and ty[i - 1:i] != "'"):
        depth = 0
        for end in range(start, len(ty)):
            depth += ty[end] == '['
            depth -= ty[end] == ']'
            if depth == 0:
                break
        out.add(' '.join(ty[start:end + 1].split()))
    return out


REF = re.compile(r"(?<![\w'.])((?:[A-Z][\w']*\.)*)([a-z_][\w']*)")
# F1's directly fusing binding: one whose body holds the build or augment of
# its list result, or applies foldr, or a good consumer outside the tree
# defined by it, to a list argument; lists of Int, shapes, are left out.
PRODUCES = re.compile(r"(?<![\w'])(?:build|augment)(?![\w'])")
CONSUMES = re.compile(
    r"(?<![\w'])((?:[A-Z][\w']*\.)*)(foldr|foldl'?|sum|product|and|or|any|"
    r"all|concat|concatMap|elem|notElem|length|mapM_|sequence_|zip|zipWith|"
    r"unzip|map|filter)(?![\w'])")


def elements(lists):
    """The list types but those built of Int and Bool alone, a shape's and its
    flags."""
    return {x for x in lists
            if set(re.findall(r"[A-Za-z_][\w']*", x)) - {'Int', 'Bool'}}


DEF_EQ = re.compile(r"(?<![=<>/!:|])=(?![=>])")
HEAD_FUN = re.compile(r"(?:\s|\(|\$|\.(?![\w'])|[A-Z][\w']*(?![\w'.]))*"
                      r"((?:[A-Z][\w']*\.)*)([a-z_][\w']*)")
KEYWORDS = {'case', 'let', 'if', 'do', 'where', 'of', 'in', 'then', 'else'}


def wrapped(body):
    """The (qualifier, name) heading the right-hand side of a binding's first
    equation, constructors applied to it and $ and . left aside, or None where
    a guard or a keyword comes first."""
    m = DEF_EQ.search(body)
    if not m or '|' in body[:m.start()]:
        return None
    h = HEAD_FUN.match(body, m.end())
    return None if not h or h.group(2) in KEYWORDS else (h.group(1), h.group(2))


NEWTYPE_FIELD = re.compile(r"^newtype\b[^=\n]*=\s*[A-Z][\w']*\s*\{\s*"
                           r"([a-z_][\w']*)\s*::", re.M)
TOKEN = re.compile(r"`[^`]*`|(?:[A-Z][\w']*\.)*[A-Za-z_][\w']*|\d\w*(?:\.\d+)?"
                   r"|'(?:[^'\\]|\\.)'|[!#$%&*+./<=>?@\\^|~:-]+|[()\[\],;{}]")
FREE_OPS = {'$', '.', '->', '\\', '@', '~', '!'}


def newtype_fields(texts):
    """The fields of the tree's newtypes, whose selectors cost no call."""
    return {m.group(1) for t in texts.values()
            for m in NEWTYPE_FIELD.finditer(t)}


def untyped(s):
    """s without its type annotations, each from `::` to the end of the group
    holding it, and its type applications, an `@` after a space, a bracket
    or a comma."""
    out, depth, skip, i = [], 0, None, 0
    while i < len(s):
        if skip is None and s.startswith('::', i):
            skip, i = depth, i + 2
            continue
        if skip is None and s[i] == '@' and (i == 0 or s[i - 1] in ' ([,'):
            i += 1 + (s[i + 1:i + 2] == "'")
            if s[i:i + 1] in ('(', '['):
                i = bracket_end(s, i) or len(s)
            else:
                while i < len(s) and (s[i].isalnum() or s[i] in "_'"):
                    i += 1
            continue
        depth += s[i] in '(['
        depth -= s[i] in ')]'
        if skip is not None and depth < skip:
            skip = None
        if skip is None:
            out.append(s[i])
        i += 1
    return ''.join(out)


def thin(eqs, fields=frozenset()):
    """Whether a binding is a thin wrapper: it has equations, and the
    right-hand side of each, unguarded and holding no local binding,
    comprehension, case, conditional or do block, makes at most one call, its
    constructors, its newtype fields, `coerce`, `$` and `.` aside, any other
    operator, a backticked name and a range each counting as one."""
    if not eqs:
        return False
    for pats, rest in eqs:
        if not rest.startswith('='):
            return False
        bound = {v for p in pats
                 for v in re.findall(r"(?<![\w'.])[a-z_][\w']*", p)}
        calls, lam = 0, False
        for t in TOKEN.findall(untyped(rest[1:])):
            if t == '\\':
                lam = True
            elif lam:
                if t == '->':
                    lam = False
                elif re.fullmatch(r"[a-z_][\w']*", t):
                    bound.add(t)
            elif t in KEYWORDS or t in ('<-', '|', '=', ';'):
                return False
            elif t[0] == '`':
                calls += 1
            elif t[0].isalpha() or t[0] == '_':
                name = t.split('.')[-1]
                calls += not (name[0].isupper() or name == '_'
                              or name in bound or name in fields
                              or name == 'coerce')
            elif t[0] in "!#$%&*+./<=>?@\\^|~:-" and t not in FREE_OPS:
                calls += t[0] != ':'
            if calls > 1:
                return False
    return True


def element_lists(ty):
    """The list types of ty but a shape's and its flags."""
    return elements(lists_of(ty))


def own_start(lines, start, name, names):
    """The line from start at which name's equations begin, past those of
    the other names its signature declares, names, which may come first,
    and past pragmas and comments: ending at one, a pragma between the
    signature and the equations left the binding none (pragma-census-19)."""
    others = [re.compile(r"\(?" + re.escape(o) + r"\)?(?![\w'])")
              for o in names if o != name]
    j = past_asides(lines, start)
    while j < len(lines):
        line = lines[j]
        if line[:1] not in (' ', '\t') and \
                not any(o.match(line) for o in others):
            return j
        j = past_asides(lines, j + 1)
    return start


def equations(lines, start, name):
    """[(argument patterns, rest)] of the equations of name from line start:
    each one's left side split at depth 0 into its patterns, and the guards,
    right-hand side and where clause after them, string literals and
    comments blanked; a pragma or a comment at column 0 between them is
    passed over."""
    head = re.compile(r"\(?" + re.escape(name) + r"\)?(?![\w'])")
    eqs, j = [], start
    while j < len(lines):
        if lines[j][:1] not in (' ', '\t') and lines[j].strip() and \
                past_asides(lines, j) > j:
            j = past_asides(lines, j)
            continue
        line = re.sub(r'(^|\s)--(\s.*)?$', '',
                      re.sub(r'"(?:[^"\\]|\\.)*"', '""', lines[j]))
        if line[:1] in (' ', '\t') or not line.strip():
            if eqs:
                eqs[-1] += ' ' + line
            j += 1
            continue
        m = head.match(line)
        if not m:
            break
        eqs.append(line[m.end():])
        j += 1
    out = []
    for e in eqs:
        depth, cut = 0, len(e)
        for i, ch in enumerate(e):
            depth += ch in '(['
            depth -= ch in ')]'
            if depth == 0 and (ch == '|' and e[i:i + 2] != '||'
                               and e[i - 1:i] != '|'
                               or ch == '=' and e[i - 1:i] not in '=<>/'
                               and e[i + 1:i + 2] not in '=>'):
                cut = i
                break
        pats = [p for p in depth0(e[:cut].strip(), ' ') if p.strip()]
        out.append((pats, e[cut:]))
    return out


def consumed_once(eqs, ty):
    """Whether each equation binds each list argument of ty it names to
    a variable its rest names once: not where a pattern takes the list apart
    or leaves it unused, nor where the list goes to more than one consumer.
    An argument an equation leaves unnamed, eta-reduced, says nothing."""
    parts = depth0(body_type(ty).replace('ShapeL', '[Int]'), '->')
    at = [i for i, a in enumerate(parts[:-1]) if element_lists(a)]
    for pats, rest in eqs:
        for i in at:
            if i >= len(pats):
                continue
            m = re.fullmatch(r"[!~]?([a-z][\w']*)", pats[i].strip())
            if not m or len(re.findall(
                    r"(?<![\w'.])" + re.escape(m.group(1)) + r"(?![\w'])",
                    rest)) != 1:
                return False
    return True


def fusing(body, ty, outside=lambda qual, name: True, eqs=None):
    """Whether a binding of type ty and this body is directly fusing, a
    consumer counting where outside says its name is not the tree's and,
    given its equations, where each consumes its list argument once."""
    parts = depth0(body_type(ty).replace('ShapeL', '[Int]'), '->')
    args = set().union(*[element_lists(a) for a in parts[:-1]]) if parts else set()
    result = element_lists(parts[-1]) if parts else set()
    return bool((result and PRODUCES.search(body))
                or (args and (eqs is None or consumed_once(eqs, ty))
                    and any(outside(q, n)
                            for q, n in CONSUMES.findall(body))))


def method_body(lines, n, k):
    """The equations of the method defined at line n of a body ending
    before line k, joined, the deeper lines continuing it."""
    out, j = [lines[n]], n + 1
    while j < k and (indent(lines[j]) > indent(lines[n]) or not lines[j].strip()):
        out.append(lines[j])
        j += 1
    return ' '.join(re.sub(r'(^|\s)--(\s.*)?$', '', x) for x in out)


def method_equations(lines, n, k, name):
    """equations() of the method defined at line n of a body ending before
    line k, read from its lines at line n's indentation or deeper, dedented."""
    block, j, ind = [], n, indent(lines[n])
    while j < k and (not lines[j].strip() or indent(lines[j]) >= ind):
        block.append(lines[j][ind:])
        j += 1
    return equations(block, 0, name)


def forwarding(texts, classes=None):
    """({key: callee} of the bindings that forward to one needing INLINE,
    {key} of the directly fusing ones, and [(path, line, name, callee)] of
    the bindings whose comment names F1 but which hand a list of their type
    to a tree binding); a key is (module, name) for a top-level binding and
    (module, class.method, line) for an instance method. A binding needs
    INLINE where it is directly fusing (F1) or carries INLINE under a comment
    giving P's reason, and a forwarder calls one needing it, by its name in
    its module or one it imports unqualified or through a qualified alias, or
    through a class method with such an instance, and passes it a list
    of its type, or, where the callee's reason is a measurement rather than
    F1, calls it at all; to a fixed point. texts maps each path to its
    text."""
    classes = classes or {}
    table, info, where, methods, pending = {}, {}, {}, {}, {}
    eqs_of = {}
    for path, text in texts.items():
        lines = text.split('\n')
        mod, aliases, opens = module_info(text)
        info[mod] = (aliases, opens)
        kinds = {m.group(3): m.group(1) for x in code(lines)
                 if x[:1] not in ' \t' for m in KINDS.finditer(x)}
        for i, line in enumerate(lines):
            m = top_signature(lines, i)
            if not m:
                continue
            sig, j = signature_at(lines, i, m)
            names = [x.strip('()')
                     for x in re.split(r'\s*,\s*', m.group(1).strip())]
            for name in names:
                k = own_start(lines, j, name, names)
                body = definition(lines, k, name)
                eqs_of[(mod, name)] = equations(lines, k, name)
                table[(mod, name)] = (lists_of(body_type(sig)), None, body)
                pending[(mod, name)] = (lines, [i], kinds.get(name), sig)
                where[(mod, name)] = (path, i, noted(lines, i, F1NOTE))
        for i, line in enumerate(lines):
            if not line.startswith('instance'):
                continue
            head, j, k, hm = decl_at(lines, i)
            if not hm:
                continue
            cls = re.sub(r'^.*\.', '', (hm.group(1).split('=>', 1)[-1]).split()[0])
            pk = {}
            for b in code(lines[i:k]):
                for p in KINDS.finditer(b):
                    pk[p.group(3)] = p.group(1)
            seen = set()
            for n, b in instance_body(lines, j, k, hm):
                meth = method_name(b)
                ty = classes.get(cls, {}).get(meth)
                if not meth or meth in seen or ty is None:
                    continue
                seen.add(meth)
                body = method_body(lines, n, k)
                key = (mod, f'{cls}.{meth}', n)
                table[key] = (lists_of(body_type(ty)), None, body)
                pending[key] = (lines, [i, n], pk.get(meth), ty)
                methods.setdefault(meth, set()).add(key)

    def defining(x, name, seen):
        """The modules defining name that module x holds, itself or through
        the modules it imports unqualified, as a facade re-exports them."""
        if (x, name) in table:
            return {x}
        if x not in info or x in seen:
            return set()
        seen.add(x)
        return set().union(*[defining(y, name, seen) for y in info[x][1]])

    def resolve(mod, qual, name):
        aliases, opens = info[mod]
        if qual:
            mods = aliases.get(qual[:-1], ())
        elif (mod, name) in table:
            mods = [mod]
        else:
            mods = opens
        cands = set().union(*[defining(x, name, set()) for x in mods])
        return (cands.pop(), name) if len(cands) == 1 else None

    def callees(k, qual, name):
        c = resolve(k[0], qual, name)
        return [c] if c else sorted(methods.get(name, ()))

    over = {k for k, (lines, notes, has, _) in pending.items()
            if departs(lines, notes, has)}
    for k, (lines, notes, has, ty) in pending.items():
        lists, _, body = table[k]
        fuses = fusing(body, ty, lambda q, n: not resolve(k[0], q, n)
                       and n not in methods, eqs_of.get(k))
        table[k] = (lists, seed_kind(lines, notes, has, fuses), body)

    need = {k: seed for k, (_, seed, _) in table.items() if seed}
    fwd, grew = {}, True
    while grew:
        grew = False
        for k, (lists, _, body) in table.items():
            if k in need or k in over:
                continue
            head = wrapped(body)
            for qual, name in REF.findall(body):
                hit = [c for c in callees(k, qual, name) if c != k and c in need
                       and (need[c] != 'A3' and lists & table[c][0]
                            or need[c] == 'measured'
                            and (qual, name) == head)]
                if hit:
                    need[k] = need[hit[0]]
                    fwd[k] = f'{hit[0][0]}.{hit[0][1]}'
                    grew = True
                    break
    fus = {k for k, (_, seed, _) in table.items() if seed == 'fusing'}
    shallow = []
    for k, (path, n, f1) in where.items():
        if not f1 or not table[k][1]:
            continue
        for qual, name in REF.findall(table[k][2]):
            c = resolve(k[0], qual, name)
            if c and c != k and elements(table[k][0] & table[c][0]):
                shallow.append((path, n + 1, k[1], f'{c[0]}.{c[1]}'))
                break
    return fwd, fus, shallow


def departs(lines, notes, has):
    """Whether a comment above a binding gives P's reason for the pragma it
    carries, one other than INLINE, which overrides what its body and its
    callees would make it."""
    other = {'INLINEABLE': 'INLINABLE', 'SPECIALISE': 'INLINABLE',
             'SPECIALIZE': 'INLINABLE'}.get(has, has) or 'none'
    return other != 'INLINE' and any(reasoned(lines, x, other) for x in notes)


def seed_kind(lines, notes, has, fuses):
    """How a binding needs INLINE: 'fusing' where it is directly fusing,
    'F1', 'A3' or 'measured' where it carries INLINE under a comment giving
    P's reason, by whether the reason cites F1, A3 or neither, and None where
    it needs none, a departure overriding its body."""
    if departs(lines, notes, has):
        return None
    if fuses:
        return 'fusing'
    for x in notes:
        if has == 'INLINE' and reasoned(lines, x, 'INLINE'):
            return ('F1' if noted(lines, x, F1NOTE)
                    else 'A3' if noted(lines, x, A3NOTE) else 'measured')
    return None


def is_sum(lines, i):
    """Whether the declaration at line i is a sum: a data type of two
    constructors or more, its indented lines read without their comments,
    or a type synonym, taken for the sum it names."""
    if lines[i].startswith('type'):
        return True
    if lines[i].startswith('newtype'):
        return False
    decl, j = [lines[i]], i + 1
    while j < len(lines) and (not lines[j].strip() or lines[j][:1] in ' \t'):
        decl.append(lines[j])
        j += 1
    text = ' '.join(re.sub(r'--.*$', '', x) for x in decl)
    rhs = re.split(r'\bderiving\b', text)[0].partition('=')[2]
    return len(depth0(rhs, '|')) > 1


def marked_types(texts):
    """The sums marked as never to be built (A3): a plain comment directly
    above the declaration's haddock whose first line opens
    `-- Unmaterialized:`."""
    out = set()
    for text in texts.values():
        lines = text.split('\n')
        for i, line in enumerate(lines):
            m = TYPE_DECL.match(line)
            plain = plain_lines(lines, i) if m else []
            if plain and UNMAT.match(plain[0]) and is_sum(lines, i):
                out.add(m.group(1))
    return out


def carried(ty, marked):
    """The marked types a type names, qualified or not."""
    body = body_type(ty)
    return sorted(t for t in marked
                  if re.search(r"(?<![\w'])" + re.escape(t) + r"(?![\w'])",
                               body))


def rule_check(text, classes, fwd=None, fus=None, marked=(),
               fields=frozenset()):
    """The bindings of a module whose pragma differs from what the rule gives
    with no comment naming a pragma above them: [(line, name, has, wants,
    reasons)]; the recursive ones the rule makes INLINE: [(line, name, has)];
    and the instance methods of unknown classes: [(line, class, method)].
    fwd and fus are forwarding()'s forwarders and directly fusing bindings,
    each wanting INLINE; the directly fusing ones whose type does not want
    INLINE already and whose comment does not give P's reason citing F1:
    [(line, name)]; and the bindings whose type names one of the marked sums
    and whose comment does not give P's reason naming each it names and
    citing A3, a departure aside: [(line, name, sums)]. fields are the
    tree's newtype fields, which thin() reads as costing no call."""
    lines, fwd, mod = text.split('\n'), fwd or {}, module_info(text)[0]
    fus = fus or set()
    unmarked, unbuilt = [], []
    kinds = {}
    for line in code(lines):
        for m in KINDS.finditer(line):
            if line[:1] not in (' ', '\t'):
                kinds[m.group(3)] = (m.group(1), bool(m.group(2)))
    start = next((n for n, x in enumerate(lines) if re.match(r'module\b', x)),
                 0)
    mdecl = declared([x for x in lines[:start] if x.lstrip().startswith('--')],
                     next((n + 1 for n, x in enumerate(lines[:start])
                           if 'throughout' in x), 0))
    off, rec, unknown, judged = [], [], [], []

    def judge(n, name, has, phased, ty, over, notes, extra=(), decl=mdecl,
              key=None, eqs=()):
        key = key or (mod, name)
        has = {'INLINEABLE': 'INLINABLE', 'SPECIALISE': 'INLINABLE',
               'SPECIALIZE': 'INLINABLE'}.get(has, has)
        if decl is not None:
            judged.append((decl, n + 1, name, has))
        if phased:
            return
        covered = decl is not None and decl.covers(name, has)
        if key in fus and not fun_arg(ty) and not covered and not (
                decl is not None and decl.names(name) and decl.f1) and not any(
                reasoned(lines, x, has) and noted(lines, x, F1NOTE)
                for x in notes):
            unmarked.append((n + 1, name))
        note = any(reasoned(lines, x, has) for x in notes)
        types = carried(ty, marked)
        if types and not departs(lines, notes, has) and \
                not any(reasoned(lines, x, has) and noted(lines, x, A3NOTE)
                        and all(noted(lines, x, re.compile(
                            r"(?<![\w'])" + re.escape(t) + r"(?![\w'])"))
                            for t in types)
                        for x in notes):
            unbuilt.append((n + 1, name, types))
        w, why = want(ty, over)
        why = why + list(extra)
        if w != 'INLINE' and types:
            w, why = 'INLINE', [f'takes or returns {", ".join(types)} (A3)']
        if w != 'INLINE' and key in fus:
            w, why = 'INLINE', ['directly fusing (F1)']
        if w != 'INLINE' and key in fwd:
            w, why = 'INLINE', [f'forwards to {fwd[key]}']
        if w != 'INLINE' and thin(eqs, fields):
            w, why = 'INLINE', ['thin wrapper']
        if w == 'INLINE' and recursive_here.get(name):
            if has == 'INLINE':
                rec.append((n + 1, name, has))
            return
        if has != w and not note and not covered and not (
                decl is not None and decl.names(name) and decl.cited):
            off.append((n + 1, name, has, w, why))

    recursive_here = {}
    i = 0
    while i < len(lines):
        line = lines[i]
        m = top_signature(lines, i)
        if m:
            sig, j = signature_at(lines, i, m)
            names = [x.strip('()')
                     for x in re.split(r'\s*,\s*', m.group(1).strip())]
            for name in names:
                k = own_start(lines, j, name, names)
                recursive_here[name] = recursive(lines, k, name)
                has, phased = kinds.get(name, ('none', False))
                judge(i, name, has, phased, sig, False, [i],
                      eqs=equations(lines, k, name))
            i = j
            continue
        if re.match(r'^class\b', line):
            cls, dm, k = defaults(lines, i)
            cdecl = declared(plain_lines(lines, i), i + 1)
            for n, name, sn, p in dm:
                has, phased = p or ('none', False)
                judge(n, f'{cls}.{name}', has, phased,
                      classes.get(cls, {}).get(name, ''), True,
                      [i, n, sn],
                      ['default method'], mdecl if cdecl is None else cdecl,
                      eqs=method_equations(lines, n, k, name))
            i = k
            continue
        if line.startswith('instance'):
            head, j, k, hm = decl_at(lines, i)
            if hm and 'TypeError' not in hm.group(1):
                ctx, cls_head = (hm.group(1).split('=>', 1)
                                 if '=>' in hm.group(1) else ('', hm.group(1)))
                cls = re.sub(r'^.*\.', '', cls_head.split()[0])
                over = bool(constraints(ctx)) if ctx else False
                body = instance_body(lines, j, k, hm)
                pk = {}
                for b in code(lines[i:k]):
                    for p in KINDS.finditer(b):
                        pk[p.group(3)] = (p.group(1), bool(p.group(2)))
                hdecl = declared(plain_lines(lines, i), i + 1)
                isigs = body_signatures(lines, j, k)
                seen = set()
                for n, b in body:
                    name = method_name(b)
                    if not name or name in seen or \
                            re.match(r'\s*(type|data)\b', b):
                        continue
                    seen.add(name)
                    if stub(b):
                        continue
                    ty = classes.get(cls, {}).get(name)
                    if ty is None:
                        unknown.append((n + 1, cls, name))
                        continue
                    has, phased = pk.get(name, ('none', False))
                    judge(n, f'{cls}.{name}', has, phased, ty, over,
                          [i, n] + ([isigs[name][1]] if name in isigs
                                    else []), (),
                          mdecl if hdecl is None else hdecl,
                          (mod, f'{cls}.{name}', n),
                          method_equations(lines, n, k, name))
            i = k
            continue
        i += 1
    return off, rec, unknown, unmarked, unbuilt, undeclared(judged)


def undeclared(judged):
    """What the declarations of a module claim and its bindings do not bear
    out: [(line, name, has, pragma, decl_line)] of the bindings a declaration's
    scope holds that carry another pragma and that it does not name, and
    [(decl_line, word, why)] of the words after its but that are no name,
    name no binding of its scope or name only ones carrying its pragma."""
    scope, order = {}, []
    for d, n, name, has in judged:
        if id(d) not in scope:
            scope[id(d)] = (d, [])
            order.append(id(d))
        scope[id(d)][1].append((n, name, has))
    out, bad = [], []
    for k in order:
        d, items = scope[k]
        out += [(n, name, has, d.pragma, d.line) for n, name, has in items
                if has != d.pragma and not d.names(name)]
        for w in d.but:
            hits = [has for _, name, has in items
                    if name == w or name.rsplit('.', 1)[-1] == w]
            if not hits:
                bad.append((d.line, w, 'names no binding there'))
            elif all(has == d.pragma for has in hits):
                bad.append((d.line, w, f'carries {d.pragma}'))
        bad += [(d.line, w, 'not a name') for w in d.bad]
    return out, bad


SKIP = frozenset()  # paths relative to SRC that --skip leaves out


def hs_files(src):
    files = []
    for d, dirs, names in os.walk(src):
        dirs[:] = sorted(x for x in dirs if not x.startswith(('.', 'dist')))
        files += [os.path.join(d, x) for x in sorted(names)
                  if x.endswith('.hs')
                  and os.path.relpath(os.path.join(d, x), src) not in SKIP]
    return files


def rule_findings(src):
    """(the .hs files read, and --rule's findings over them: rule_check's
    five lists, paths relative to src, and forwarding()'s shallow F1
    comments)."""
    files, texts, classes = hs_files(src), {}, dict(STD)
    for path in files:
        with open(path) as fh:
            texts[path] = blank_blocks(fh.read())
        classes.update(class_methods(texts[path]))
    fwd, fus, shallow = forwarding(texts, classes)
    marked, fields = marked_types(texts), newtype_fields(texts)
    off, rec, unknown, unmarked, unbuilt = [], [], [], [], []
    undecl, badbut = [], []
    for path in files:
        rel = os.path.relpath(path, src)
        o, r, u, f, b, (ud, bb) = rule_check(texts[path], classes, fwd, fus,
                                             marked, fields)
        off += [(rel, *x) for x in o]
        rec += [(rel, *x) for x in r]
        unknown += [(rel, *x) for x in u]
        unmarked += [(rel, *x) for x in f]
        unbuilt += [(rel, *x) for x in b]
        undecl += [(rel, *x) for x in ud]
        badbut += [(rel, *x) for x in bb]
    return (files, off, rec, unknown, unmarked, unbuilt, shallow, undecl,
            badbut)


def report_rule(src):
    """(lines, number of findings, number of .hs files read) of --rule."""
    (files, off, rec, unknown, unmarked, unbuilt, shallow, undecl,
     badbut) = rule_findings(src)
    out = ['== pragma unlike the rule and no comment above in its form'
           ' (file:line name: has -> wants [why])']
    out += [f'  {rel}:{n} {name}: {has} -> {w} [{", ".join(why)}]'
            for rel, n, name, has, w, why in off]
    out.append('== recursive and INLINE: an INLINE wrapper over a recursive'
               ' worker instead (file:line name)')
    out += [f'  {rel}:{n} {name}' for rel, n, name, _ in rec]
    out.append('== methods of a class whose method types are unknown'
               ' (file:line class.method)')
    out += [f'  {rel}:{n} {cls}.{name}' for rel, n, cls, name in unknown]
    out.append('== a comment naming F1 on a binding that hands its list to a'
               ' tree binding, the innermost one being the one to carry it'
               ' (file:line name -> callee)')
    out += [f'  {os.path.relpath(p, src)}:{n} {name} -> {c}'
            for p, n, name, c in sorted(shallow)]
    out.append('== directly fusing (F1) with no comment giving P\'s reason'
               ' citing F1 (file:line name)')
    out += [f'  {rel}:{n} {name}' for rel, n, name in unmarked]
    out.append('== takes or returns a sum marked Unmaterialized (A3) with no'
               ' comment giving P\'s reason naming it and citing A3'
               ' (file:line name: sums)')
    out += [f'  {rel}:{n} {name}: {", ".join(ts)}'
            for rel, n, name, ts in unbuilt]
    out.append('== a declaration\'s scope holding a binding of another pragma'
               ' that its but does not name (file:line name: has, declared'
               ' pragma at line)')
    out += [f'  {rel}:{n} {name}: {has}, {p} throughout at {dl}'
            for rel, n, name, has, p, dl in undecl]
    out.append('== a declaration\'s but naming what it should not'
               ' (file:line word: why)')
    out += [f'  {rel}:{dl} {w}: {why}' for rel, dl, w, why in badbut]
    return out, (len(off) + len(rec) + len(unknown) + len(shallow)
                 + len(unmarked) + len(unbuilt) + len(undecl)
                 + len(badbut)), len(files)


RANK = {'none': 0, 'INLINABLE': 1, 'INLINE': 2}


def pragma_lines(lines, i, name):
    """[(line, kind, phased)] of the pragmas of name that the binding defined
    at line i reads: at column 0 for a top-level one, in its instance or class
    for a method."""
    if lines[i][:1] not in (' ', '\t'):
        span = [n for n, x in enumerate(lines) if x[:1] not in (' ', '\t')]
    else:
        h = i
        while h > 0 and not re.match(r'(instance|class)\b', lines[h]):
            h -= 1
        span = range(h, decl_at(lines, h, lines[h].split()[0])[2])
    c = code(lines)
    return [(n, m.group(1), bool(m.group(2))) for n in span
            for m in KINDS.finditer(c[n]) if m.group(3) == name]


def plan(lines, n, name, has, want):
    """The edit giving the binding of a finding at line n, from 1, the pragma
    it wants: ('insert', line, text), ('replace', line, text) or ('delete',
    line), lines from 0; or why it is not written."""
    i = n - 1
    top = lines[i][:1] not in (' ', '\t')
    base = name if top else name.split('.', 1)[1]
    found = pragma_lines(lines, i, base)
    if has == 'NOINLINE':
        return 'a NOINLINE, which W3 settles'
    if has == 'none':
        if found:
            return 'a pragma of its name stands'
        spelt = f'({base})' if re.fullmatch(OP, base) else base
        ind = re.match(r'\s*', lines[i]).group(0)
        return ('insert', i, f'{ind}{{-# {want} {spelt} #-}}')
    if len(found) != 1:
        return f'{len(found)} pragmas of its name'
    c, kind, _ = found[0]
    if kind.startswith('SPECIALI'):
        return 'a SPECIALISE'
    if want == 'none':
        if not re.fullmatch(r'\s*\{-#[^#]*#-\}\s*', lines[c]):
            return 'its pragma shares its line'
        return ('delete', c)
    return ('replace', c, re.sub(r'\{-#\s*\w+', '{-# ' + want, lines[c], 1))


def read_keep(path):
    """The (file, name) pairs of a --keep file, each line as --rule prints
    a finding, its line number optional; None where a line is not one."""
    keep = set()
    with open(path) as fh:
        for line in fh:
            m = re.match(r'\s*(\S+?\.hs)(?::\d+)?\s+(\S+?):?(?:\s|$)', line)
            if m:
                keep.add(m.groups())
            elif line.strip() and not line.lstrip().startswith('#'):
                return None
    return keep


def write_rule(src, release=False, keep=frozenset()):
    """--write: (the lines it prints before the final --rule report, whether
    every round's writes took)."""
    out, used, before = [], set(), None
    for rnd in range(1, 21):
        files, off = rule_findings(src)[:2]
        todo, refused = {}, []
        for rel, n, name, has, w, why in off:
            if (rel, name) in keep:
                used.add((rel, name))
            elif has == 'NOINLINE' or release or RANK[w] > RANK[has]:
                todo.setdefault(rel, []).append((n, name, has, w, why))
        wrote = []
        for rel, items in todo.items():
            path = os.path.join(src, rel)
            with open(path) as fh:
                lines = fh.read().split('\n')
            edits = []
            for n, name, has, w, why in items:
                e = plan(lines, n, name, has, w)
                if isinstance(e, str):
                    refused.append(f'  {rel}:{n} {name}: {has} -> {w}: {e}')
                else:
                    edits.append(e)
                    wrote.append(f'  {rel}:{n} {name}: {has} -> {w}'
                                 f' [{", ".join(why)}]')
            # bottom-up, so that no edit moves a line another one names
            for e in sorted(edits, key=lambda e: e[1], reverse=True):
                if e[0] == 'insert':
                    lines.insert(e[1], e[2])
                elif e[0] == 'replace':
                    lines[e[1]] = e[2]
                else:
                    del lines[e[1]]
            if edits:
                with open(path, 'w') as fh:
                    fh.write('\n'.join(lines))
        if not wrote:
            break
        out.append(f'== round {rnd} wrote'
                   ' (file:line name: has -> wants [why])')
        out += wrote
        key = [re.sub(r':\d+ ', ' ', x) for x in wrote]
        if key == before:
            out.append('== the census still lists what the last round wrote')
            return out, False
        before = key
    else:
        out.append('== twenty rounds and still writing')
        return out, False
    out.append('== not written (file:line name: has -> wants: why)')
    out += refused
    out.append('== keep lines matching no finding (file name)')
    out += [f'  {rel} {name}' for rel, name in sorted(keep - used)]
    return out, True


def report(src):
    """(lines, number of bindings listed, number of .hs files read)."""
    files = hs_files(src)
    funs, meths, dms = [], [], []
    for path in files:
        with open(path) as fh:
            f, m, d = census(fh.read())
        rel = os.path.relpath(path, src)
        funs += [(rel, n, name, cs) for n, name, cs in f]
        meths += [(cls, rel, n, name) for n, cls, name in m]
        dms += [(cls, rel, n, name) for n, cls, name in d]
    out = ['== overloaded functions without a pragma'
           ' (file:line name [context])']
    out += [f'  {rel}:{n} {name} [{", ".join(cs)}]'
            for rel, n, name, cs in funs]
    out.append('== overloaded instance methods without a pragma'
               ' (class: file:line method)')
    out += [f'  {cls}: {rel}:{n} {name}'
            for cls, rel, n, name in sorted(meths)]
    out.append('== class default methods without a pragma'
               ' (class: file:line method)')
    out += [f'  {cls}: {rel}:{n} {name}'
            for cls, rel, n, name in sorted(dms)]
    return out, len(funs) + len(meths) + len(dms), len(files)


def self_test():
    import tempfile
    src = ('module M where\n'
           'f :: HasCallStack => Int -> Int\n'
           'f = id\n'
           'g :: (HasCallStack, Num a) => a -> a\n'
           'g = id\n'
           'h :: (a ~ b) => a -> b\n'
           'h = id\n'
           'k :: forall a .\n'
           '     (Show a)\n'
           '  => a -> String\n'
           'k = show\n'
           '{-# INLINABLE m #-}\n'
           'm :: Eq a => a -> Bool\n'
           'm x = x == x\n'
           'p :: ((o + n) <= s) => Int\n'
           'p = 0\n'
           'class C a where\n'
           '  c :: Eq a => a -> Int\n'
           '  c _ = 0\n'
           'instance Show a => Show (T a) where show = showT\n'
           'instance Eq a => Eq (T a) where\n'
           '  (T x) == (T y) = x == y\n'
           '  {-# INLINE (==) #-}\n'
           '  x /= y = not (x == y)\n'
           'instance Num a => Num (T a) where\n'
           '  (+) = liftT2 (+)\n'
           '  negate (T x) = T (negate x)\n'
           '  negate _ = undefined\n'
           '  {-# INLINE negate #-}\n'
           "instance (TypeError ('Text \"no\")) => C (T Bool) where\n"
           '  c = error "no"\n'
           'instance KnownNat n => D (P n) where\n'
           '  {-# INLINE d #-}\n'
           '  d = natVal (Proxy :: Proxy n)\n'
           'instance KnownNat n => E (P n) where\n'
           '  e = natVal (Proxy :: Proxy n)\n'
           'instance (Num a,\n'
           '          Show a) => F (T a) where\n'
           '  f1 = 1\n'
           '\n'
           '  a `f2` b = a\n'
           'instance Show U where show _ = "U"\n'
           'instance (a ~ b) => G a b where g = id\n'
           'instance Ord a => H (T a) where\n'
           '  hh :: T a -> Int\n'
           '  hh _ = 0\n'
           '  {-# INLINE hh #-}\n'
           'instance Ord a => J (T a) where\n'
           '  jj = undefined\n'
           'instance Ord a => K (T a) where\n'
           '  kk 0 = 1\n'
           '  kk _ = 2\n'
           'q1, q2 :: Num a => a\n'
           'q1 = 0\n'
           'q2 = 1\n'
           '{-# INLINE [1] r #-}\n'
           'r :: Num a => a\n'
           'r = 0\n'
           '{-# SPECIALISE s :: Int -> Int #-}\n'
           's :: Num a => a -> a\n'
           's = id\n'
           'instance Show a => Show (V a) where\n'
           '  showsPrec p v = showString "V " .\n'
           '    showsPrec p (unV v)\n'
           '  show v = s\n'
           '    where s = "V"\n'
           'instance (Ord a, Show a)\n'
           '         => Ord (V a) where\n'
           '  a@(V (W x)) `compare` (V y) = compare x y\n'
           '  {-# INLINE compare #-}\n'
           'instance Arbitrary a => Arbitrary (V a) where\n'
           '  arbitrary = do\n'
           '    x <- arbitrary\n'
           '    return (V x)\n'
           'withRank :: Int -> (forall n . KnownNat n => Proxy n -> r) -> r\n'
           'withRank = undefined\n'
           'hr :: Num a => (forall n . KnownNat n => Proxy n -> a) -> a\n'
           'hr = undefined\n'
           'instance Eq a => L (T a) where\n'
           '  T x ==. T y = x == y\n'
           'class (Show a,\n'
           '       -- a comment inside the head, saying where\n'
           '       Eq a) => CD a where\n'
           '  cd1, cd2 :: a -> a\n'
           '  cd1 = id\n'
           '  {-# INLINABLE cd2 #-}\n'
           '  cd2 = id\n'
           '  cd3 :: a\n'
           '  cd3 = undefined\n'
           '  cd4 :: a -> String\n'
           '  default cd4 :: Show a => a -> String\n'
           '  cd4 x = show x\n'
           '  cd4 _ = ""\n'
           '  cd5:: a -> a\n'
           'instance Ord a => G2 (T a) where\n'
           '  {-# INLINE g2a #-}\n'
           '  g2a = id\n'
           '-- a comment at column 0 inside the body\n'
           '  g2b = id\n'
           'sp\n'
           '  :: Num a => a -> a\n'
           'sp = id\n'
           'instance Ord a => SI (T a) where\n'
           '  si\n'
           '    :: T a -> Int\n'
           '  si _ = 0\n'
           'class CS a where\n'
           '  cs1\n'
           '    :: a -> a\n'
           '  cs1 = id\n'
           'instance Ord a => BC (T a) where\n'
           '  bc1 = id\n'
           '{- a block comment inside the body, holding\n'
           'instance {-# OVERLAPPABLE #-} Num a => BD a where\n'
           '  bd = id\n'
           'bs :: Num a => a -> a\n'
           '-}\n'
           '  bc2 = id\n')
    want = ['== overloaded functions without a pragma'
            ' (file:line name [context])',
            '  M.hs:4 g [Num a]',
            '  M.hs:8 k [Show a]',
            '  M.hs:53 q1 [Num a]',
            '  M.hs:53 q2 [Num a]',
            '  M.hs:77 hr [Num a]',
            '  M.hs:100 sp [Num a]',
            '== overloaded instance methods without a pragma'
            ' (class: file:line method)',
            '  Arbitrary: M.hs:72 arbitrary',
            '  BC: M.hs:112 bc1',
            '  BC: M.hs:118 bc2',
            '  E: M.hs:36 e',
            '  Eq: M.hs:24 /=',
            '  F: M.hs:39 f1',
            '  F: M.hs:41 f2',
            '  G2: M.hs:99 g2b',
            '  K: M.hs:51 kk',
            '  L: M.hs:80 ==.',
            '  Num: M.hs:26 +',
            '  SI: M.hs:106 si',
            '  Show: M.hs:20 show',
            '  Show: M.hs:63 showsPrec',
            '  Show: M.hs:65 show',
            '== class default methods without a pragma'
            ' (class: file:line method)',
            '  C: M.hs:19 c',
            '  CD: M.hs:85 cd1',
            '  CD: M.hs:92 cd4',
            '  CS: M.hs:110 cs1']
    bad = []
    with tempfile.TemporaryDirectory() as td:
        os.makedirs(os.path.join(td, 'S'))
        os.makedirs(os.path.join(td, 'E'))
        os.makedirs(os.path.join(td, 'C'))
        with open(os.path.join(td, 'S', 'M.hs'), 'w') as fh:
            fh.write(src)
        with open(os.path.join(td, 'C', 'N.hs'), 'w') as fh:
            fh.write('module N where\n{-# INLINE n #-}\n'
                     'n :: Num a => a\nn = 0\n')
        got, nbad, nfiles = report(os.path.join(td, 'S'))
        if got != want or (nbad, nfiles) != (25, 1):
            bad.append(f'report ({nbad}, {nfiles}):\n  ' + '\n  '.join(got))
        for d, code, why in (('S', 1, 'bindings without a pragma'),
                             ('E', 2, 'a tree without .hs files'),
                             ('C', 0, 'a tree whose bindings all carry one')):
            if main([os.path.join(td, d)]) != code:
                bad.append(f'{why} did not exit {code}')
    bad += self_test_rule()
    bad += self_test_write()
    for b in bad:
        print('FAIL', b)
    print('self-test', 'FAILED' if bad else 'passed')
    return 1 if bad else 0


def self_test_rule():
    """--rule over a module of one case per mechanism and modules covered by
    declarations, the findings compared without their line numbers."""
    import tempfile
    src = ('module R where\n'
           'class Vec v where\n'
           '  type VecElem v :: Type -> Constraint\n'
           '  vmap :: (a -> b) -> v a -> v b\n'
           '  vlen :: VecElem v a => v a -> Int\n'
           'class Conv a b where\n'
           '  conv :: a -> b\n'
           'f1 :: (a -> b) -> [a] -> [b]\n'
           'f1 = map\n'
           '{-# INLINE f2 #-}\n'
           'f2 :: (a -> b) -> T a -> T b\n'
           'f2 = mapT\n'
           '{-# INLINABLE f3 #-}\n'
           'f3 :: T a -> [a]\n'
           'f3 = toListT . id\n'
           'f4 :: Num a => T a -> a\n'
           'f4 = sumT . id\n'
           '{-# INLINE f5 #-}\n'
           'f5 :: Num a => T a -> a\n'
           'f5 = sumT . id\n'
           '-- INLINE: I3, measured faster.\n'
           '-- | Doc.\n'
           '{-# INLINE f6 #-}\n'
           'f6 :: Num a => T a -> a\n'
           'f6 = sumT . id\n'
           '-- | Doc,\n'
           '-- INLINE: I3, its second line in the form.\n'
           '{-# INLINE f7 #-}\n'
           'f7 :: Num a => T a -> a\n'
           'f7 = sumT . id\n'
           '{-# INLINABLE f8 #-}\n'
           'f8 :: HasCallStack => T a -> T a\n'
           'f8 = id . id\n'
           '{-# INLINE f9 #-}\n'
           'f9 :: (a ~ b) => T a -> T b\n'
           'f9 = id . id\n'
           'f10 :: T a -> Int\n'
           'f10 = lenT . id\n'
           '{-# INLINE [1] f11 #-}\n'
           'f11 :: Num a => T a -> a\n'
           'f11 = sumT . id\n'
           '{-# SPECIALISE f12 :: T Int -> Int #-}\n'
           'f12 :: Num a => T a -> a\n'
           'f12 = sumT . id\n'
           '{-# INLINE f14 #-}\n'
           'f14 :: (a -> a) -> [a] -> [a]\n'
           'f14 g (x : xs) = g x : f14 g xs\n'
           'f14 _ [] = []\n'
           '{-# INLINE f15 #-}\n'
           'f15 :: (a -> a) -> T a -> T a\n'
           'f15 g t | otherwise = error "f15: no"  -- f15 is not recursive\n'
           'f17 :: [Int] -> T a -> T a\n'
           'f17 = permT . id\n'
           'instance Functor T where\n'
           '  fmap = mapT\n'
           'instance Num a => Num (T a) where\n'
           '  (+) = zipT (+)\n'
           '  {-# INLINABLE (+) #-}\n'
           '  negate = mapT negate\n'
           '  {-# INLINE negate #-}\n'
           '  fromInteger _ = error "no"\n'
           'instance Vec T where\n'
           '  type VecElem T = Show\n'
           '  vmap = mapT\n'
           '  vlen = lenT . id\n'
           'instance Show (T a) where\n'
           '  showsPrec _ _ = id . id\n'
           '    -- INLINE: I3, a comment ending the body above.\n'
           '  {-# INLINE show #-}\n'
           '  show _ = id (id "")\n'
           '-- No pragma: reference semantics, on GHC 9.14.1 (2026-10-11).\n'
           'instance Functor U where\n'
           '  fmap = mapU\n'
           'instance Foo T where\n'
           '  foo = id\n'
           'instance Show a => Show (U a) where\n'
           '  show _ = id (id "")\n'
           'instance (a ~ b) => Conv (T a) (U b) where\n'
           '  conv (T x) = U (id (id x))\n'
           '  {-# INLINE conv #-}\n'
           'class ( Show a\n'
           '        -- a comment inside the head\n'
           '      )\n'
           '      => Dflt a where\n'
           '\n'
           '  d1 :: (a -> a) -> a -> a\n'
           '  d1 g = g\n'
           '  d2 :: a -> String\n'
           '  default d2 :: Show a => a -> String\n'
           '  d2 = show . id\n'
           '  {-# INLINE d3 #-}\n'
           '  d3 :: a -> String\n'
           '  d3 = show . id\n'
           '  {-# INLINABLE d4 #-}\n'
           '  d4 :: a -> String\n'
           '  d4 = show . id\n'
           '  d6 :: a -> a\n'
           '  d6 = undefined\n'
           '  -- INLINE: I3, measured faster.\n'
           '  {-# INLINE d7 #-}\n'
           '  d7 :: a -> String\n'
           '  d7 = show . id\n'
           '  d8 :: a -> String\n'
           '  -- INLINE: I3, measured faster, said above the definition.\n'
           '  {-# INLINE d8 #-}\n'
           '  d8 = show . id\n'
           '-- a comment at column 0 inside the class\n'
           '  d9 :: a\n'
           '     -> (a -> a) -> a\n'
           '  d9 x _ = x\n'
           'instance Show b => Dflt [b] where\n'
           '  d2 = concatMap show\n'
           '-- INLINE: I3, measured faster, said of the class.\n'
           'class Dnote a where\n'
           '  {-# INLINE dn #-}\n'
           '  dn :: a -> String\n'
           '  dn _ = id (id "")\n'
           '-- INLINE: measured faster, citing nothing.\n'
           '{-# INLINE s1 #-}\n'
           's1 :: Num a => T a -> a\n'
           's1 = sumT . id\n'
           '-- INLINABLE: I3, the lead naming another pragma.\n'
           '{-# INLINE s2 #-}\n'
           's2 :: Num a => T a -> a\n'
           's2 = sumT . id\n'
           '-- Measured faster, the pragma not leading:\n'
           '-- INLINE: I3.\n'
           '{-# INLINE s3 #-}\n'
           's3 :: Num a => T a -> a\n'
           's3 = sumT . id\n'
           '-- INLINE: on GHC 9.14.1, a version without a date.\n'
           '{-# INLINE s4 #-}\n'
           's4 :: Num a => T a -> a\n'
           's4 = sumT . id\n'
           '-- INLINE: on GHC HEAD (2026-10-10), 0.8 times the instructions.\n'
           '{-# INLINE s5 #-}\n'
           's5 :: Num a => T a -> a\n'
           's5 = sumT . id\n'
           '-- INLINE: see s5.\n'
           '{-# INLINE s6 #-}\n'
           's6 :: Num a => T a -> a\n'
           's6 = sumT . id\n'
           '-- No pragma: I3, measured no faster with one.\n'
           's7 :: Num a => T a -> a\n'
           's7 = sumT\n'
           'sf\n'
           '  :: (a -> b) -> T a -> T b\n'
           'sf = mapT\n'
           'class Vec3 v where\n'
           '  v3\n'
           '    :: (a -> b) -> v a -> v b\n'
           'instance Vec3 T where\n'
           '  v3 = mapT\n')
    layer = ('-- These are INLINE throughout but g2: their callers are INLINABLE.\n'
             'module L where\n'
             '{-# INLINE g1 #-}\n'
             'g1 :: Num a => T a -> a\n'
             'g1 = sumT\n'
             'g2 :: Num a => T a -> a\n'
             'g2 = sumT . id\n'
             'instance Num a => Num (T a) where\n'
             '  {-# INLINE (+) #-}\n'
             '  (+) = zipT (+)\n')
    nopr = ('-- No pragma throughout but n3, n4, n5 and n6: a reference implementation.\n'
            'module N where\n'
            'n1 :: Num a => T a -> a\n'
            'n1 = sumT\n'
            'n2 :: (a -> b) -> T a -> T b\n'
            'n2 = mapT\n'
            '{-# INLINABLE n3 #-}\n'
            'n3 :: T a -> Int\n'
            'n3 = lenT . id\n'
            '-- INLINABLE: I3, measured faster.\n'
            '{-# INLINABLE n4 #-}\n'
            'n4 :: T a -> Int\n'
            'n4 = lenT\n'
            '{-# INLINE n5 #-}\n'
            'n5 :: (a -> b) -> T a -> T b\n'
            'n5 = mapT\n'
            'n6 :: Num a => T a -> a\n'
            'n6 = sumT . id\n'
            'nfl :: [a] -> T a\n'
            'nfl xs = T (V.fromList (filter (const True) xs))\n'
            '-- INLINE throughout but fmap: the instance a measured exception.\n'
            'instance Functor T where\n'
            '  fmap = mapT\n')
    decl = ('module V where\n'
            'v1 :: Num a => a -> a\n'
            'v1 = id . id\n'
            'class Vec2 v where\n'
            '  vm :: (a -> b) -> v a -> v b\n'
            '  vs :: Num a => v a -> a\n'
            '-- No pragma throughout but vs: the reference instance.\n'
            'instance Vec2 [] where\n'
            '  vm = map\n'
            '  {-# INLINE vs #-}\n'
            '  vs = sum . id\n'
            '-- INLINABLE throughout but vs: measured faster.\n'
            'instance Vec2 T where\n'
            '  {-# INLINABLE vm #-}\n'
            '  vm = mapT\n'
            '  vs = sumT . id\n'
            '-- INLINEABLE throughout but dc2: each pragma measured.\n'
            'class Dc a where\n'
            '  dc1 :: (a -> a) -> a\n'
            '  {-# INLINABLE dc1 #-}\n'
            '  dc1 g = g undefined\n'
            '  dc2 :: a -> a\n'
            '  dc2 = id . id\n')
    low = ('module Low where\n'
           '-- INLINE: built with build, citing nothing.\n'
           '{-# INLINE rootU #-}\n'
           'rootU :: T a -> [a]\n'
           'rootU t = build (\\c n -> foldT c n t)\n'
           '-- INLINE: measured faster, citing nothing.\n'
           '{-# INLINE rootV #-}\n'
           'rootV :: T a -> Int\n'
           'rootV = lenT . id\n'
           '-- INLINE: directly fusing (F1), its list built with build.\n'
           '{-# INLINE rootT #-}\n'
           'rootT :: T a -> [a]\n'
           'rootT t = build (\\c n -> foldT c n t)\n'
           '{-# INLINE foldT #-}\n'
           'foldT :: (a -> b -> b) -> b -> T a -> b\n'
           'foldT = undefined\n')
    mid = ('module Mid where\n'
           'import qualified Low as L\n'
           '{-# INLINE mid #-}\n'
           'mid :: A a -> [a]\n'
           'mid = L.rootT . unA\n'
           '{-# INLINABLE mid2 #-}\n'
           'mid2 :: Num a => A a -> [a]\n'
           'mid2 = L.rootT . unA\n'
           'mid3 :: [Int] -> A a -> Int\n'
           'mid3 sh a = length (L.rootT (unA a)) + length sh\n'
           'import qualified Fac as F\n'
           '{-# INLINABLE mid4 #-}\n'
           'mid4 :: A a -> [a]\n'
           'mid4 = F.rootT . unA\n'
           '-- INLINE: directly fusing (F1), said of a wrapper.\n'
           '{-# INLINE mid5 #-}\n'
           'mid5 :: A a -> [a]\n'
           'mid5 = L.rootT . unA\n'
           '-- INLINE: measured faster.\n'
           '{-# INLINE mid6 #-}\n'
           'mid6 :: A a -> [a]\n'
           'mid6 = L.rootT . unA\n'
           'mid7 :: A a -> [a]\n'
           'mid7 = L.rootU . unA\n'
           'mid8 :: A a -> Int\n'
           'mid8 = L.rootV . unA\n')
    fusw = ('module W where\n'
            '{-# INLINE rootX #-}\n'
            'rootX :: T a -> [a]\n'
            'rootX t = build (\\c n -> foldT c n t)\n'
            'tot :: Num a => T a -> a\n'
            'tot t = sum (rootX t)\n'
            'sz :: [Int] -> Int\n'
            'sz = product . id\n'
            'pd :: [(Int, Int)] -> Int\n'
            'pd = sum . map fst\n'
            'fl2 :: [Bool] -> Bool\n'
            'fl2 = and . id\n'
            '-- INLINE: on GHC HEAD (2026-10-11), measured faster than INLINABLE.\n'
            '{-# INLINE cmpT #-}\n'
            'cmpT :: Ord a => T a -> T a -> Ordering\n'
            'cmpT = undefined\n'
            '{-# INLINABLE useC #-}\n'
            'useC :: Ord a => T a -> T a -> Bool\n'
            'useC a b = not (cmpT a b == EQ)\n'
            '-- INLINE: on GHC HEAD (2026-10-11), measured faster than INLINABLE.\n'
            '{-# INLINE msd #-}\n'
            'msd :: [a] -> T a -> ([a], [a])\n'
            'msd xs t = (xs, rootX t)\n'
            '-- INLINE: F1, directly fusing: it consumes its list once, by length.\n'
            '{-# INLINE sh1 #-}\n'
            'sh1 :: [Int] -> [a] -> Int\n'
            'sh1 is xs = sz is + length xs\n'
            # A body that fuses by its look, its list consumed once, under
            # a departure overriding it.
            '-- INLINABLE: F1 reads no fusion here: no caller builds its list.\n'
            '{-# INLINABLE nf #-}\n'
            'nf :: Num a => [a] -> T a -> a\n'
            'nf xs t = sum xs * 2 + sum (rootX t)\n'
            '{-# INLINABLE nfc #-}\n'
            'nfc :: Num a => [a] -> T a -> a\n'
            'nfc xs t = nf xs t + 0\n'
            # Consumers of their list more than once, or by a pattern: no
            # direct fusion (pragma-census-11).
            '-- INLINE: on GHC HEAD (2026-10-12), measured faster than INLINABLE.\n'
            '{-# INLINE twice #-}\n'
            'twice :: [Double] -> Double\n'
            'twice xs = sum xs + product xs\n'
            '-- INLINE: on GHC HEAD (2026-10-12), measured faster than INLINABLE.\n'
            '{-# INLINE taken #-}\n'
            'taken :: [Double] -> Double\n'
            'taken [] = 0\n'
            'taken (x : xs) = x + sum xs\n'
            'instance Ord a => Ord (T a) where\n'
            '  compare = cmpT\n'
            'class VL v where\n'
            '  vfl :: Int -> [a] -> v a\n'
            'instance VL Vector where\n'
            '  vfl _ xs = V.fromList (map id xs)\n'
            'fl :: VL v => [a] -> v a\n'
            'fl xs = vfl 3 xs\n')
    fac = ('module Fac(module L) where\n'
           'import Low as L\n')
    api = ('module Api where\n'
           'import Mid\n'
           'top :: B a -> [a]\n'
           'top = mid . unB\n'
           'top3, top4 :: B a -> [a]\n'
           'top3 = mid . unB\n'
           'top4 = mid . unB\n')
    unbuilt = ('module U where\n'
               'import qualified U as M\n'
               '-- Unmaterialized: built where it is taken apart.\n'
               '-- | A route.\n'
               'data Rt = RA !Int | RB\n'
               '-- Unmaterialized: see Rt.\n'
               'data Rg = Rg !Int !Int | NoRg\n'
               '-- A note.\n'
               '-- Unmaterialized: not the first line.\n'
               'data Late = L1 | L2\n'
               'u1 :: Int -> Rt\n'
               'u1 = RA\n'
               '-- INLINE: Rt, A3: it returns the Rt its callers take apart.\n'
               '{-# INLINE u2 #-}\n'
               'u2 :: Int -> Rt\n'
               'u2 = RA\n'
               '{-# INLINE u3 #-}\n'
               'u3 :: Rt -> Int\n'
               'u3 (RA x) = x\n'
               'u3 RB = 0\n'
               '-- INLINE: A3, naming no type.\n'
               '{-# INLINE u4 #-}\n'
               'u4 :: Rg -> Rt\n'
               'u4 _ = RB\n'
               '-- INLINE: Rt and Rg, A3: both.\n'
               '{-# INLINE u5 #-}\n'
               'u5 :: M.Rg -> Rt\n'
               'u5 _ = RB\n'
               '-- No pragma: nothing to gain, on GHC HEAD (2026-10-11).\n'
               'u6 :: Int -> Rt\n'
               'u6 = RA\n'
               '-- INLINE: Rt, A3: it takes apart the Rt its callers build.\n'
               '{-# INLINE u8 #-}\n'
               'u8 :: Rt -> Int\n'
               'u8 (RA x) = x\n'
               'u8 RB = 0\n'
               'u7 :: Int -> Int\n'
               'u7 x = u8 (RA x) + 0\n'
               'u9 :: Late -> Int\n'
               'u9 _ = id (id 0)\n'
               '-- Unmaterialized: a product, left to measurement.\n'
               'data Ax = Ax !Int !Int\n'
               '-- Unmaterialized: a synonym, taken for a sum.\n'
               'type Mb = Maybe Int\n'
               '-- Unmaterialized: a sum across lines.\n'
               'data Ml\n'
               '  = M1 !Int\n'
               '      -- ^ the first\n'
               '  | M2\n'
               '  deriving Eq\n'
               '-- Unmaterialized: a product whose comment holds a bar.\n'
               'data Pc = Pc !Int  -- one | two\n'
               'u10 :: Ax -> Int\n'
               'u10 (Ax a b) = a + b + 0\n'
               'u11 :: Int -> Mb\n'
               'u11 = Just\n'
               'u12 :: Ml -> Int\n'
               'u12 _ = 0\n'
               'u13 :: Pc -> Int\n'
               'u13 (Pc a) = id (id a)\n')
    thinw = ('module Th where\n'
             'newtype Bx a = Bx { unBx :: T a }\n'
             'th1 :: T a -> Int\n'
             'th1 = lenT\n'
             'th2 :: Bx a -> Int\n'
             'th2 = lenT . unBx\n'
             'th3 :: a -> T a\n'
             'th3 = T [] 0 . single\n'
             'th4 :: Int\n'
             'th4 = natT @(n + 1) (Proxy :: Proxy (Take d sh))\n'
             '{-# INLINE th5 #-}\n'
             'th5 :: T a -> Int\n'
             'th5 x = case x of T _ -> 0\n'
             '{-# INLINE th6 #-}\n'
             'th6 :: [Int] -> T a\n'
             'th6 sh = T (tail $ strides sh) 0\n'
             '{-# INLINE th7 #-}\n'
             'th7 :: T a -> ()\n'
             'th7 t = rnfT t `seq` rnfS t\n'
             '{-# INLINE th8 #-}\n'
             'th8 :: [Int] -> [Int]\n'
             'th8 xs = [ x | x <- xs ]\n'
             '{-# INLINE th9 #-}\n'
             'th9 :: Int -> Int\n'
             'th9 x | x > 0 = lenT x\n'
             '      | otherwise = 0\n'
             '{-# INLINE th10 #-}\n'
             'th10 :: Int -> Int -> Int\n'
             'th10 o i = o + i * 2\n'
             'th11 :: Int -> Int -> Int\n'
             'th11 o i = o + i\n'
             'th12 :: T a -> T a\n'
             'th12 = mapT (\\ x -> x)\n'
             'th13 :: T a -> Int -> T a\n'
             'th13 (T (s : ss)) i = T ss\n'
             'th13 _ _ = error "th13"\n'
             'th14, th15 :: T a -> Int\n'
             'th14 = lenT\n'
             'th15 = lenT\n'
             'th16 :: [Bx a] -> Int\n'
             'th16 = lenL . coerce\n'
             'class Sz t where\n'
             '  szz :: t -> Int\n'
             'instance Sz (T a) where\n'
             '  szz = lenT\n'
             'instance Sz [a] where\n'
             '  {-# INLINE szz #-}\n'
             '  szz [] = 0\n'
             '  szz xs = length xs + 1\n'
             'instance Sz Int where\n'
             '  -- INLINE: GHC HEAD 10.1.20260918, 2026-10-13: measured.\n'
             '  {-# INLINE szz #-}\n'
             '  szz :: Int -> Int\n'
             '  szz x = x + x * 2\n')
    want = ['== pragma unlike the rule and no comment above in its form'
            ' (file:line name: has -> wants [why])',
            '  Api.hs top: none -> INLINE [forwards to Mid.mid]',
            '  Api.hs top3: none -> INLINE [forwards to Mid.mid]',
            '  Api.hs top4: none -> INLINE [forwards to Mid.mid]',
            '  Dx.hs d4: none -> INLINABLE [class constraint]',
            '  L.hs g2: none -> INLINABLE [class constraint]',
            '  Low.hs rootV: INLINE -> none [no class constraint]',
            '  Mid.hs mid2: INLINABLE -> INLINE [forwards to Low.rootT]',
            '  Mid.hs mid4: INLINABLE -> INLINE [forwards to Low.rootT]',
            '  Mid.hs mid7: none -> INLINE [forwards to Low.rootU]',
            '  N.hs n3: INLINABLE -> none [no class constraint]',
            '  N.hs n6: none -> INLINABLE [class constraint]',
            '  N.hs Functor.fmap: none -> INLINE [function argument]',
            '  R.hs f1: none -> INLINE [function argument]',
            '  R.hs f3: INLINABLE -> none [no class constraint]',
            '  R.hs f4: none -> INLINABLE [class constraint]',
            '  R.hs f5: INLINE -> INLINABLE [class constraint]',
            '  R.hs f7: INLINE -> INLINABLE [class constraint]',
            '  R.hs f8: INLINABLE -> none [no class constraint]',
            '  R.hs f9: INLINE -> none [no class constraint]',
            '  R.hs Functor.fmap: none -> INLINE [function argument]',
            '  R.hs Num.negate: INLINE -> INLINABLE [class constraint]',
            '  R.hs Vec.vmap: none -> INLINE [function argument]',
            '  R.hs Vec.vlen: none -> INLINABLE [class constraint]',
            '  R.hs Show.show: INLINE -> none [no class constraint]',
            '  R.hs Show.show: none -> INLINABLE [class constraint]',
            '  R.hs Conv.conv: INLINE -> none [no class constraint]',
            '  R.hs Dflt.d1: none -> INLINE'
            ' [function argument, default method]',
            '  R.hs Dflt.d2: none -> INLINABLE'
            ' [class constraint, default method]',
            '  R.hs Dflt.d3: INLINE -> INLINABLE'
            ' [class constraint, default method]',
            '  R.hs Dflt.d9: none -> INLINE'
            ' [function argument, default method]',
            '  R.hs Dflt.d2: none -> INLINABLE [class constraint]',
            '  R.hs s1: INLINE -> INLINABLE [class constraint]',
            '  R.hs s2: INLINE -> INLINABLE [class constraint]',
            '  R.hs s3: INLINE -> INLINABLE [class constraint]',
            '  R.hs s4: INLINE -> INLINABLE [class constraint]',
            '  R.hs sf: none -> INLINE [function argument]',
            '  R.hs Vec3.v3: none -> INLINE [function argument]',
            '  Th.hs th1: none -> INLINE [thin wrapper]',
            '  Th.hs th2: none -> INLINE [thin wrapper]',
            '  Th.hs th3: none -> INLINE [thin wrapper]',
            '  Th.hs th4: none -> INLINE [thin wrapper]',
            '  Th.hs th5: INLINE -> none [no class constraint]',
            '  Th.hs th6: INLINE -> none [no class constraint]',
            '  Th.hs th7: INLINE -> none [no class constraint]',
            '  Th.hs th8: INLINE -> none [no class constraint]',
            '  Th.hs th9: INLINE -> none [no class constraint]',
            '  Th.hs th10: INLINE -> none [no class constraint]',
            '  Th.hs th11: none -> INLINE [thin wrapper]',
            '  Th.hs th12: none -> INLINE [thin wrapper]',
            '  Th.hs th13: none -> INLINE [thin wrapper]',
            '  Th.hs th14: none -> INLINE [thin wrapper]',
            '  Th.hs th15: none -> INLINE [thin wrapper]',
            '  Th.hs th16: none -> INLINE [thin wrapper]',
            '  Th.hs Sz.szz: none -> INLINE [thin wrapper]',
            '  Th.hs Sz.szz: INLINE -> none [no class constraint]',
            '  U.hs u1: none -> INLINE [takes or returns Rt (A3)]',
            '  U.hs u11: none -> INLINE [takes or returns Mb (A3)]',
            '  U.hs u12: none -> INLINE [takes or returns Ml (A3)]',
            '  V.hs v1: none -> INLINABLE [class constraint]',
            '  V.hs Vec2.vs: INLINE -> INLINABLE [class constraint]',
            '  V.hs Vec2.vs: none -> INLINABLE [class constraint]',
            '  V.hs Dc.dc2: none -> INLINABLE'
            ' [class constraint, default method]',
            '  W.hs tot: none -> INLINABLE [class constraint]',
            '  W.hs Ord.compare: none -> INLINE [forwards to W.cmpT]',
            '  W.hs VL.vfl: none -> INLINE [directly fusing (F1)]',
            '  W.hs fl: none -> INLINE [forwards to W.VL.vfl]',
            '== recursive and INLINE: an INLINE wrapper over a recursive'
            ' worker instead (file:line name)',
            '  R.hs f14',
            '== methods of a class whose method types are unknown'
            ' (file:line class.method)',
            '  R.hs Foo.foo',
            '== a comment naming F1 on a binding that hands its list to a'
            ' tree binding, the innermost one being the one to carry it'
            ' (file:line name -> callee)',
            '  Mid.hs mid5 -> Low.rootT',
            '== directly fusing (F1) with no comment giving P\'s reason'
            ' citing F1 (file:line name)',
            '  Low.hs rootU',
            '  W.hs rootX',
            '  W.hs VL.vfl',
            '== takes or returns a sum marked Unmaterialized (A3) with no'
            ' comment giving P\'s reason naming it and citing A3'
            ' (file:line name: sums)',
            '  U.hs u1: Rt',
            '  U.hs u3: Rt',
            '  U.hs u4: Rg, Rt',
            '  U.hs u11: Mb',
            '  U.hs u12: Ml',
            '== a declaration\'s scope holding a binding of another pragma'
            ' that its but does not name (file:line name: has, declared'
            ' pragma at line)',
            '  Dx.hs d4: none, INLINE throughout at 1',
            '== a declaration\'s but naming what it should not'
            ' (file:line word: why)',
            '  Dx.hs d9: carries INLINE',
            '  Dx.hs h0: names no binding there',
            '  Dx.hs no name: not a name',
            '  N.hs n6: carries none']
    # A declaration naming its exceptions: d2 named and carrying another
    # pragma, as it should; d4 carrying another unnamed; d9 named but carrying
    # the declared one; h0 naming nothing, and two words no name. Its text
    # cites a GHC version with a date and F1, so it excuses d5, departing
    # from the rule, and df, directly fusing, both named.
    declx = ('-- INLINE throughout but d2, d5, d9, df, h0 and no name: on GHC\n'
             '-- HEAD (2026-10-18), measured; df, F1.\n'
             'module Dx where\n'
             '{-# INLINE d1 #-}\n'
             'd1 :: Num a => a -> a\n'
             'd1 x = x + x * x\n'
             '{-# INLINABLE d2 #-}\n'
             'd2 :: Num a => a -> a\n'
             'd2 x = x + x * x\n'
             'd4 :: Num a => a -> a\n'
             'd4 x = x + x * x\n'
             'd5 :: Num a => a -> a\n'
             'd5 x = x + x * x\n'
             '{-# INLINE d9 #-}\n'
             'd9 :: Num a => a -> a\n'
             'd9 x = x + x * x\n'
             'df :: a -> [a]\n'
             'df n = build (\\c z -> c n (c n z))\n')
    bad = []
    with tempfile.TemporaryDirectory() as td:
        for name, text in (('R.hs', src), ('L.hs', layer), ('Low.hs', low),
                           ('Mid.hs', mid), ('Api.hs', api), ('Fac.hs', fac),
                           ('N.hs', nopr), ('V.hs', decl), ('W.hs', fusw),
                           ('U.hs', unbuilt), ('Th.hs', thinw), ('Dx.hs', declx),
                           ('Bk.hs', 'module Bk where\n{- commented out\n'
                                     'bk :: Num a => a -> a\nbk x = x\n-}\n')):
            with open(os.path.join(td, name), 'w') as fh:
                fh.write(text)
        got, nbad, _ = report_rule(td)
        got = [re.sub(r'^(  \S+\.hs):\d+', r'\1', x) for x in got]
        if got != want or nbad != 82:
            bad.append(f'--rule ({nbad}):\n  ' + '\n  '.join(got))
        if main(['--rule', td]) != 1:
            bad.append('--rule with findings did not exit 1')
        global SKIP
        in_u = sum(1 for x in got if x.startswith('  U.hs'))
        SKIP = frozenset(['U.hs'])
        got, nbad, _ = report_rule(td)
        SKIP = frozenset()
        if in_u == 0 or any('U.hs' in x for x in got) or nbad != 82 - in_u:
            bad.append(f'--skip U.hs left it in ({nbad}): '
                       + '; '.join(x for x in got if 'U.hs' in x))
        if main(['--rule', '--skip', 'Nope.hs', td]) != 2:
            bad.append('--skip naming no file did not exit 2')
    return bad


def self_test_write():
    """--write over a module of one case per edit and refusal, by default
    and with --release and a keep file, the written text compared whole;
    the pragma k, removed above the insertions, checks their order."""
    import contextlib
    import io
    import tempfile
    src = ('module W where\n'
           '{-# INLINE k #-}\n'
           'class Fm f where\n'
           '  fm :: (a -> b) -> f a -> f b\n'
           'instance Fm T where\n'
           '  {-# INLINABLE fm #-}\n'
           '  fm g (T x) = T (g x)\n'
           'f :: (a -> b) -> [a] -> [b]\n'
           'f = map\n'
           '(<+>) :: (a -> b) -> T a -> T b\n'
           '(<+>) = fm\n'
           '{-# INLINE g #-}\n'
           'g :: Num a => a -> a\n'
           'g = id . id\n'
           'k :: Int -> Int\n'
           'k = id . id\n'
           '{-# SPECIALISE s :: (Int -> Int) -> Int -> Int #-}\n'
           's :: Num a => (a -> a) -> a -> a\n'
           's h = h\n'
           '{-# NOINLINE n #-}\n'
           'n :: (a -> a) -> a -> a\n'
           'n h = h\n'
           '-- INLINE: I3, GHC 9.14.1, 2026-10-12: measured.\n'
           '{-# INLINE q #-}\n'
           'q :: Int -> Int\n'
           'q x = x + 1\n'
           'p :: Int -> Int\n'
           'p x = q x\n')
    up = (src.replace('{-# INLINABLE fm', '{-# INLINE fm')
          .replace('f :: ', '{-# INLINE f #-}\nf :: ')
          .replace('(<+>) :: ', '{-# INLINE (<+>) #-}\n(<+>) :: ')
          .replace('p :: ', '{-# INLINE p #-}\np :: '))
    cases = (([], up, ['  W.hs:7 Fm.fm: INLINABLE -> INLINE',
                       '  W.hs:8 f: none -> INLINE',
                       '  W.hs:10 <+>: none -> INLINE',
                       '  W.hs:27 p: none -> INLINE'], []),
             (['--release', '--keep'],
              up.replace('{-# INLINE k #-}\n', '', 1),
              ['  W.hs:7 Fm.fm: INLINABLE -> INLINE',
               '  W.hs:8 f: none -> INLINE',
               '  W.hs:10 <+>: none -> INLINE',
               '  W.hs:15 k: INLINE -> none',
               '  W.hs:27 p: none -> INLINE'], ['  W.hs nosuch']))
    bad = []
    with tempfile.TemporaryDirectory() as td:
        path, keep = os.path.join(td, 'W.hs'), os.path.join(td, 'keep')
        with open(keep, 'w') as fh:
            fh.write('  W.hs:13 g: INLINE -> INLINABLE [class constraint]\n'
                     '# a comment\nW.hs nosuch\n')
        for flags, text, wrote, stale in cases:
            with open(path, 'w') as fh:
                fh.write(src)
            argv = ['--write'] + flags + ([keep] if flags else []) + [td]
            with contextlib.redirect_stdout(io.StringIO()) as so:
                code = main(argv)
            got = so.getvalue().split('\n')
            with open(path) as fh:
                if fh.read() != text:
                    bad.append(f'--write {flags} wrote another text')
            r1 = [re.sub(r' \[.*', '', x)
                  for x in got[1:got.index('== not written (file:line name:'
                                           ' has -> wants: why)')]]
            k = got.index('== keep lines matching no finding (file name)')
            if code != 1 or r1 != wrote or got[k + 1:k + 1 + len(stale)] \
                    != stale or not got[k + 1 + len(stale)].startswith('=='):
                bad.append(f'--write {flags} ({code}):\n  ' + '\n  '.join(got))
            with contextlib.redirect_stdout(io.StringIO()) as so:
                main(argv)
            if so.getvalue().startswith('== round'):
                bad.append(f'--write {flags} wrote again over its own text')
        with open(keep, 'w') as fh:
            fh.write('garbage\n')
        with contextlib.redirect_stderr(io.StringIO()):
            if main(['--write', '--keep', keep, td]) != 2:
                bad.append("a keep line not in a finding's form did not"
                           ' exit 2')
    return bad


def main(argv):
    global SKIP
    if argv == ['--self-test']:
        return self_test()
    skip = []
    while '--skip' in argv:
        i = argv.index('--skip')
        if i + 1 >= len(argv):
            print('--skip names no file', file=sys.stderr)
            return 2
        skip.append(os.path.normpath(argv[i + 1]))
        argv = argv[:i] + argv[i + 2:]
    write = argv[:1] == ['--write']
    rule = write or argv[:1] == ['--rule']
    if rule:
        argv = argv[1:]
    release, keep = False, frozenset()
    while write and argv[:1] in (['--release'], ['--keep']):
        if argv[0] == '--release':
            release, argv = True, argv[1:]
            continue
        if len(argv) < 2 or not os.path.isfile(argv[1]):
            argv = []
            break
        keep, argv = read_keep(argv[1]), argv[2:]
        if keep is None:
            print("a --keep line not in a finding's form", file=sys.stderr)
            return 2
    if len(argv) != 1 or argv[0].startswith('--'):
        print(__doc__.split('\n\n')[1], file=sys.stderr)
        return 2
    for f in skip:
        if not f.endswith('.hs') or not os.path.isfile(os.path.join(argv[0], f)):
            print(f'--skip {f}: no .hs file of that path under {argv[0]}',
                  file=sys.stderr)
            return 2
    SKIP = frozenset(skip)
    if skip:
        print('== left out by --skip (file)')
        print('\n'.join(f'  {f}' for f in sorted(SKIP)))
    if not hs_files(argv[0]):
        print(f'no .hs file under {argv[0]}', file=sys.stderr)
        return 2
    if write:
        done, took = write_rule(argv[0], release, keep)
        print('\n'.join(done))
        if not took:
            return 2
    lines, nbad, _ = (report_rule if rule else report)(argv[0])
    print('\n'.join(lines))
    return 1 if nbad else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
