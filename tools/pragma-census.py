#!/usr/bin/env python3
"""List the overloaded bindings of a source tree that carry no pragma.

Usage: python3 tools/pragma-census.py SRC
       python3 tools/pragma-census.py --rule SRC
       python3 tools/pragma-census.py --self-test

For every `.hs` file under SRC, the top-level functions whose signature has
a context and the methods of the instances that have one, which carry
no `INLINE`, `INLINABLE`, `NOINLINE` or `SPECIALISE` pragma of their name:
what docs/perf-checklist.md's P asks a pragma, or a comment above the
haddock, of where their callers' speed is protected. A context counts only where it
holds a class constraint. `HasCallStack`, an equality
`a ~ b`, a `TypeError` and a type-level `<=` give a caller nothing
to specialise, so a signature or an instance with only those is passed over,
as are a `TypeError` instance, whose methods cannot be called, and a method
defined as `undefined`.

A signature may span lines, its context running to the first `=>` outside
parentheses, a rank-2 argument's context being its own; a method may be
defined prefix, as an operator section, `(<*>) = ...`, or infix, `x == y` or
`` a@(T x) `compare` b ``, and on the instance's own line after its `where`;
an instance head may span lines too, and only the lines at the body's own
indentation define a method, the deeper ones continuing it. A method's pragma
is looked for in its instance, a top-level function's anywhere in its module,
and a line `m :: ...` in an instance is its signature while a definition
holding `(Proxy :: Proxy n)` is not. A class's own signatures and default
methods, indented under it, are no instance's. It is a reader of lines and
not a parser: a top-level binding without a signature, a local function and a
pragma naming a binding of another module are not seen, and its verdict is a
list of candidates for P's rule, which only the callers decide.

`--rule` checks every top-level function with a signature and every
instance method against the pragma P's rule gives it by its own type: INLINE
where the type takes an argument of function type; otherwise INLINABLE
where it is overloaded, a class constraint in the signature, in the instance's
context or in the class method's own type; otherwise none. A method's type
is its class's, read from the tree's class declarations or from a table of
the standard classes. SPECIALISE counts as INLINABLE. A top-level binding
also wants INLINE where it forwards to one needing it: its body calls that
binding, by its name in its own module, in one it imports unqualified
or through a qualified alias, a module defining no such name followed
through its unqualified imports as a facade re-exports them, and its type
shares a list type with it. The
INLINE bindings a comment above them explains need it, which is how a
directly fusing one is told, and so, to a fixed point, does each forwarder.
A binding whose comment names F1 but whose body hands a list of its type
to a tree binding is listed too: the innermost binding should carry it. It lists each binding whose pragma differs,
unless a plain comment directly above its haddock, or for a method above
the method or its instance, names a pragma (INLINE, INLINABLE, NOINLINE or
"pragma"), a module comment saying INLINE throughout covers its top-level
INLINEs, or the pragma has a phase; the recursive bindings the rule makes
INLINE that carry INLINE, which want a wrapper over a worker instead, a body
naming its own name outside string literals being recursive; and the
methods of classes whose method types it does not know. A method defined
as `undefined` or `error ...` is passed over.

Exit 0 when every overloaded binding carries a pragma, or with `--rule`
when nothing differs, 1 when one does not, 2 when SRC holds no `.hs` file.
"""

import os
import re
import sys

PRAGMA = re.compile(r'\{-#\s*(?:INLINE|INLINABLE|INLINEABLE|NOINLINE'
                    r'|SPECIALI[SZ]E)\s*(?:\[~?\d+\]\s*)?\(?([^\s)#,]+)')
TOP_SIG = re.compile(r"^([a-z_][\w']*(?:\s*,\s*[a-z_][\w']*)*"
                     r"|\([!#$%&*+./<=>?@\\^|~:-]+\))\s*::(.*)")
OP = r"[!#$%&*+./<=>?@\\^|~:-]+"
SECTION = re.compile(r'^\((' + OP + r')\)')
INFIX_OP = re.compile(r"\s+(`[\w']+`|" + OP + r")(?=\s)")
SIGNATURE = re.compile(r"^(?:[\w']+|\(" + OP + r"\))(?:\s*,\s*[\w']+)*\s+::")


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


def pattern_end(s):
    """Where the first pattern of a definition ends: a variable or constructor,
    or a parenthesised pattern, either behind an as-pattern's `x@`."""
    m = re.match(r"[\w']+@", s)
    i = m.end() if m else 0
    if s[i:i + 1] == '(':
        depth = 0
        for j in range(i, len(s)):
            depth += s[j] == '('
            depth -= s[j] == ')'
            if depth == 0:
                return j + 1
        return None
    m = re.match(r"[\w'.]+", s[i:])
    return i + m.end() if m else None


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


def signature_at(lines, i, m):
    """The signature TOP_SIG matched as m at line i, its lines joined, and
    the line after it."""
    sig, j = m.group(2), i + 1
    while (j < len(lines) and lines[j][:1] in (' ', '\t')
           and not lines[j].strip().startswith('--')):
        sig += ' ' + lines[j]
        j += 1
    return sig, j


def instance_at(lines, i):
    """(head, its last line, the line after the body, the head's match) of the
    instance whose head starts at line i."""
    head, j = lines[i], i
    while not re.search(r'\bwhere\b', head) and j + 1 < len(lines) \
            and lines[j + 1][:1] in (' ', '\t'):
        j += 1
        head += ' ' + lines[j].strip()
    hm = re.match(r'^instance\b(.*?)(?:\bwhere\b(.*))?$', head)
    k = j + 1
    while k < len(lines) and (lines[k][:1] in (' ', '\t')
                              or not lines[k].strip()):
        if not lines[k].strip() and k + 1 < len(lines) \
                and lines[k + 1][:1] not in (' ', '\t'):
            break
        k += 1
    return head, j, k, hm


def instance_body(lines, j, k, hm):
    """[(line, text)] of an instance's lines that can define a method: what
    follows its where on the head's last line, and the lines at the body's
    own indentation."""
    rest = [(n, lines[n]) for n in range(j + 1, k) if lines[n].strip()]
    base = min((indent(b) for _, b in rest), default=0)
    return [(j, hm.group(2) or '')] + [
        (n, b) for n, b in rest if indent(b) == base]


def census(text):
    """([(line, name, constraints)] of the top-level functions and
    [(line, class, method)] of the instance methods carrying no pragma."""
    lines = text.split('\n')
    module_pragmas = {m.group(1) for line in lines
                      for m in PRAGMA.finditer(line)}
    funs, meths = [], []
    i = 0
    while i < len(lines):
        line = lines[i]
        m = TOP_SIG.match(line)
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
        if line.startswith('instance'):
            head, j, k, hm = instance_at(lines, i)
            if hm and '=>' in hm.group(1):
                ctx, cls_head = hm.group(1).split('=>', 1)
                cs = constraints(ctx)
                if cs:
                    cls = cls_head.split()[0]
                    body = instance_body(lines, j, k, hm)
                    pragmas = {p.group(1) for b in [head] + lines[j + 1:k]
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
    return funs, meths


KINDS = re.compile(r'\{-#\s*(INLINE|INLINABLE|INLINEABLE|NOINLINE|SPECIALI[SZ]E)'
                   r'\s*(\[~?\d+\]\s*)?\(?([^\s)#,]+)')
NOTE = re.compile(r'\b(?:INLINE|INLINABLE|NOINLINE)\b|\bpragma\b')
F1NOTE = re.compile(r'\bF1\b')
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


def noted(lines, i, pat=NOTE):
    """Whether plain comment lines directly above line i, above the pragmas
    and the haddock directly above it, name a pragma, or match pat."""
    k = i - 1
    while k >= 0 and (lines[k].lstrip().startswith('{-#')
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
    return any(pat.search(x) for x in plain)


def class_methods(text):
    """{class: {method: type}} of the classes a module declares."""
    lines, out = text.split('\n'), {}
    for i, line in enumerate(lines):
        m = re.match(r'^class\b(.*?)\bwhere\b', line)
        if not m:
            continue
        head = m.group(1)
        head = head.split('=>', 1)[1] if '=>' in head else head
        words = re.findall(r"[A-Za-z_][\w']*", head.split('|')[0])
        if not words:
            continue
        cls = words[0]
        meths, j = {}, i + 1
        while j < len(lines) and (lines[j][:1] in (' ', '\t')
                                  or not lines[j].strip()):
            sm = re.match(r"^\s+((?:[a-z_][\w']*|\(" + OP + r"\))"
                          r"(?:\s*,\s*(?:[a-z_][\w']*|\(" + OP + r"\)))*)"
                          r"\s*::(.*)", lines[j])
            if sm:
                ty, k = sm.group(2), j + 1
                while k < len(lines) and indent(lines[k]) > indent(lines[j]) \
                        and lines[k].strip():
                    ty += ' ' + lines[k].strip()
                    k += 1
                for n in re.split(r'\s*,\s*', sm.group(1)):
                    meths[n.strip('() ')] = ty
            j += 1
        out[cls] = meths
    return out


def definition(lines, start, name):
    """The equations of name from line start, joined, their string literals
    and comments blanked and each one's leading name dropped."""
    body, j = [], start
    pat = re.compile(r"(?<![\w.'])" + re.escape(name) + r"(?![\w'])")
    while j < len(lines):
        line = lines[j]
        if line[:1] not in (' ', '\t') and line.strip() and \
                not pat.match(line) and not line.startswith(name):
            break
        line = re.sub(r'"(?:[^"\\]|\\.)*"', '""', line)
        line = re.sub(r'(^|\s)--(\s.*)?$', '', line)
        body.append(pat.sub('', line, count=1) if line.startswith(name)
                    else line)
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


def forwarding(texts):
    """({(module, name): callee} of the top-level bindings that forward to one
    needing INLINE: their body calls it, by its name in their module or one
    they import unqualified or through a qualified alias, and their type
    shares a list type with its. The INLINE bindings a comment above them
    explains need it, and so, to a fixed point, does each forwarder;
    [(path, line, name, callee)] of the bindings whose comment names F1 but
    which hand a list of their type to a tree binding). texts maps each
    path to its text."""
    table, info, where = {}, {}, {}
    for path, text in texts.items():
        lines = text.split('\n')
        mod, aliases, opens = module_info(text)
        info[mod] = (aliases, opens)
        kinds = {m.group(3): m.group(1) for x in lines if x[:1] not in ' \t'
                 for m in KINDS.finditer(x)}
        for i, line in enumerate(lines):
            m = TOP_SIG.match(line)
            if not m:
                continue
            sig, j = signature_at(lines, i, m)
            for name in re.split(r'\s*,\s*', m.group(1).strip()):
                name = name.strip('()')
                table[(mod, name)] = (
                    lists_of(body_type(sig)),
                    kinds.get(name) == 'INLINE' and noted(lines, i),
                    definition(lines, j, name))
                where[(mod, name)] = (path, i, noted(lines, i, F1NOTE))

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

    need = {k for k, (_, seed, _) in table.items() if seed}
    fwd, grew = {}, True
    while grew:
        grew = False
        for k, (lists, _, body) in table.items():
            if k in need:
                continue
            for qual, name in REF.findall(body):
                c = resolve(k[0], qual, name)
                if c and c != k and c in need and lists & table[c][0]:
                    need.add(k)
                    fwd[k] = f'{c[0]}.{c[1]}'
                    grew = True
                    break
    shallow = []
    for k, (path, n, f1) in where.items():
        if not f1:
            continue
        for qual, name in REF.findall(table[k][2]):
            c = resolve(k[0], qual, name)
            if c and c != k and table[k][0] & table[c][0]:
                shallow.append((path, n + 1, k[1], f'{c[0]}.{c[1]}'))
                break
    return fwd, shallow


def rule_check(text, classes, fwd=None):
    """The bindings of a module whose pragma differs from what the rule gives
    with no comment naming a pragma above them: [(line, name, has, wants,
    reasons)]; the recursive ones the rule makes INLINE: [(line, name, has)];
    and the instance methods of unknown classes: [(line, class, method)].
    fwd is forwarding()'s map, its top-level forwarders wanting INLINE."""
    lines, fwd, mod = text.split('\n'), fwd or {}, module_info(text)[0]
    kinds = {}
    for line in lines:
        for m in KINDS.finditer(line):
            if line[:1] not in (' ', '\t'):
                kinds[m.group(3)] = (m.group(1), bool(m.group(2)))
    layer = any(re.search(r'INLINE throughout', x) for x in lines
                if x.lstrip().startswith('--'))
    off, rec, unknown = [], [], []

    def judge(n, name, has, phased, ty, over, note):
        if phased:
            return
        has = {'INLINEABLE': 'INLINABLE', 'SPECIALISE': 'INLINABLE',
               'SPECIALIZE': 'INLINABLE'}.get(has, has)
        w, why = want(ty, over)
        if w != 'INLINE' and (mod, name) in fwd:
            w, why = 'INLINE', [f'forwards to {fwd[(mod, name)]}']
        if w == 'INLINE' and recursive_here.get(name):
            if has == 'INLINE':
                rec.append((n + 1, name, has))
            return
        if has != w and not note and not (layer and has == 'INLINE'
                                          and n in toplevel):
            off.append((n + 1, name, has, w, why))

    recursive_here, toplevel = {}, set()
    i = 0
    while i < len(lines):
        line = lines[i]
        m = TOP_SIG.match(line)
        if m:
            sig, j = signature_at(lines, i, m)
            for name in re.split(r'\s*,\s*', m.group(1).strip()):
                name = name.strip('()')
                recursive_here[name] = recursive(lines, j, name)
                toplevel.add(i)
                has, phased = kinds.get(name, ('none', False))
                judge(i, name, has, phased, sig, False, noted(lines, i))
            i = j
            continue
        if line.startswith('instance'):
            head, j, k, hm = instance_at(lines, i)
            if hm and 'TypeError' not in hm.group(1):
                ctx, cls_head = (hm.group(1).split('=>', 1)
                                 if '=>' in hm.group(1) else ('', hm.group(1)))
                cls = re.sub(r'^.*\.', '', cls_head.split()[0])
                over = bool(constraints(ctx)) if ctx else False
                body = instance_body(lines, j, k, hm)
                pk = {}
                for b in [head] + lines[j + 1:k]:
                    for p in KINDS.finditer(b):
                        pk[p.group(3)] = (p.group(1), bool(p.group(2)))
                head_note = noted(lines, i)
                seen = set()
                for n, b in body:
                    name = method_name(b)
                    if not name or name in seen or \
                            re.match(r'\s*(type|data)\b', b):
                        continue
                    seen.add(name)
                    rhs = b.split('=', 1)[1].strip() if '=' in b else ''
                    if rhs == 'undefined' or rhs.startswith('error '):
                        continue
                    ty = classes.get(cls, {}).get(name)
                    if ty is None:
                        unknown.append((n + 1, cls, name))
                        continue
                    has, phased = pk.get(name, ('none', False))
                    judge(n, f'{cls}.{name}', has, phased, ty, over,
                          head_note or noted(lines, n))
            i = k
            continue
        i += 1
    return off, rec, unknown


def hs_files(src):
    files = []
    for d, dirs, names in os.walk(src):
        dirs[:] = sorted(x for x in dirs if not x.startswith(('.', 'dist')))
        files += [os.path.join(d, x) for x in sorted(names)
                  if x.endswith('.hs')]
    return files


def report_rule(src):
    """(lines, number of findings, number of .hs files read) of --rule."""
    files, texts, classes = hs_files(src), {}, dict(STD)
    for path in files:
        with open(path) as fh:
            texts[path] = fh.read()
        classes.update(class_methods(texts[path]))
    fwd, shallow = forwarding(texts)
    off, rec, unknown = [], [], []
    for path in files:
        rel = os.path.relpath(path, src)
        o, r, u = rule_check(texts[path], classes, fwd)
        off += [(rel, *x) for x in o]
        rec += [(rel, *x) for x in r]
        unknown += [(rel, *x) for x in u]
    out = ['== pragma unlike the rule and no comment above naming one'
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
    return out, len(off) + len(rec) + len(unknown) + len(shallow), len(files)


def report(src):
    """(lines, number of bindings listed, number of .hs files read)."""
    files = hs_files(src)
    funs, meths = [], []
    for path in files:
        with open(path) as fh:
            f, m = census(fh.read())
        rel = os.path.relpath(path, src)
        funs += [(rel, n, name, cs) for n, name, cs in f]
        meths += [(cls, rel, n, name) for n, cls, name in m]
    out = ['== overloaded functions without a pragma'
           ' (file:line name [context])']
    out += [f'  {rel}:{n} {name} [{", ".join(cs)}]'
            for rel, n, name, cs in funs]
    out.append('== overloaded instance methods without a pragma'
               ' (class: file:line method)')
    out += [f'  {cls}: {rel}:{n} {name}'
            for cls, rel, n, name in sorted(meths)]
    return out, len(funs) + len(meths), len(files)


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
           'hr = undefined\n')
    want = ['== overloaded functions without a pragma'
            ' (file:line name [context])',
            '  M.hs:4 g [Num a]',
            '  M.hs:8 k [Show a]',
            '  M.hs:53 q1 [Num a]',
            '  M.hs:53 q2 [Num a]',
            '  M.hs:77 hr [Num a]',
            '== overloaded instance methods without a pragma'
            ' (class: file:line method)',
            '  Arbitrary: M.hs:72 arbitrary',
            '  E: M.hs:36 e',
            '  Eq: M.hs:24 /=',
            '  F: M.hs:39 f1',
            '  F: M.hs:41 f2',
            '  K: M.hs:51 kk',
            '  Num: M.hs:26 +',
            '  Show: M.hs:20 show',
            '  Show: M.hs:63 showsPrec',
            '  Show: M.hs:65 show']
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
        if got != want or (nbad, nfiles) != (15, 1):
            bad.append(f'report ({nbad}, {nfiles}):\n  ' + '\n  '.join(got))
        for d, code, why in (('S', 1, 'bindings without a pragma'),
                             ('E', 2, 'a tree without .hs files'),
                             ('C', 0, 'a tree whose bindings all carry one')):
            if main([os.path.join(td, d)]) != code:
                bad.append(f'{why} did not exit {code}')
    bad += self_test_rule()
    for b in bad:
        print('FAIL', b)
    print('self-test', 'FAILED' if bad else 'passed')
    return 1 if bad else 0


def self_test_rule():
    """--rule over a module of one case per mechanism and a module covered
    by a layer comment, the findings compared without their line numbers."""
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
           'f3 = toListT\n'
           'f4 :: Num a => T a -> a\n'
           'f4 = sumT\n'
           '{-# INLINE f5 #-}\n'
           'f5 :: Num a => T a -> a\n'
           'f5 = sumT\n'
           '-- INLINE: measured faster.\n'
           '-- | Doc.\n'
           '{-# INLINE f6 #-}\n'
           'f6 :: Num a => T a -> a\n'
           'f6 = sumT\n'
           '-- | Doc,\n'
           '-- its second line saying INLINE.\n'
           '{-# INLINE f7 #-}\n'
           'f7 :: Num a => T a -> a\n'
           'f7 = sumT\n'
           '{-# INLINABLE f8 #-}\n'
           'f8 :: HasCallStack => T a -> T a\n'
           'f8 = id\n'
           '{-# INLINE f9 #-}\n'
           'f9 :: (a ~ b) => T a -> T b\n'
           'f9 = id\n'
           'f10 :: T a -> Int\n'
           'f10 = lenT\n'
           '{-# INLINE [1] f11 #-}\n'
           'f11 :: Num a => T a -> a\n'
           'f11 = sumT\n'
           '{-# SPECIALISE f12 :: T Int -> Int #-}\n'
           'f12 :: Num a => T a -> a\n'
           'f12 = sumT\n'
           '{-# INLINE f14 #-}\n'
           'f14 :: (a -> a) -> [a] -> [a]\n'
           'f14 g (x : xs) = g x : f14 g xs\n'
           'f14 _ [] = []\n'
           '{-# INLINE f15 #-}\n'
           'f15 :: (a -> a) -> T a -> T a\n'
           'f15 g t | otherwise = error "f15: no"  -- f15 is not recursive\n'
           'f17 :: [Int] -> T a -> T a\n'
           'f17 = permT\n'
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
           '  vlen = lenT\n'
           'instance Show (T a) where\n'
           '  showsPrec _ _ = id\n'
           '-- No pragma: reference semantics.\n'
           'instance Functor U where\n'
           '  fmap = mapU\n'
           'instance Foo T where\n'
           '  foo = id\n'
           'instance Show a => Show (U a) where\n'
           '  show _ = ""\n'
           'instance (a ~ b) => Conv (T a) (U b) where\n'
           '  conv (T x) = U x\n'
           '  {-# INLINE conv #-}\n')
    layer = ('-- These are INLINE throughout, their callers being INLINABLE.\n'
             'module L where\n'
             '{-# INLINE g1 #-}\n'
             'g1 :: Num a => T a -> a\n'
             'g1 = sumT\n'
             'g2 :: Num a => T a -> a\n'
             'g2 = sumT\n')
    low = ('module Low where\n'
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
           'mid6 = L.rootT . unA\n')
    fac = ('module Fac(module L) where\n'
           'import Low as L\n')
    api = ('module Api where\n'
           'import Mid\n'
           'top :: B a -> [a]\n'
           'top = mid . unB\n')
    want = ['== pragma unlike the rule and no comment above naming one'
            ' (file:line name: has -> wants [why])',
            '  Api.hs top: none -> INLINE [forwards to Mid.mid]',
            '  L.hs g2: none -> INLINABLE [class constraint]',
            '  Mid.hs mid2: INLINABLE -> INLINE [forwards to Low.rootT]',
            '  Mid.hs mid4: INLINABLE -> INLINE [forwards to Low.rootT]',
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
            '  R.hs Show.show: none -> INLINABLE [class constraint]',
            '  R.hs Conv.conv: INLINE -> none [no class constraint]',
            '== recursive and INLINE: an INLINE wrapper over a recursive'
            ' worker instead (file:line name)',
            '  R.hs f14',
            '== methods of a class whose method types are unknown'
            ' (file:line class.method)',
            '  R.hs Foo.foo',
            '== a comment naming F1 on a binding that hands its list to a'
            ' tree binding, the innermost one being the one to carry it'
            ' (file:line name -> callee)',
            '  Mid.hs mid5 -> Low.rootT']
    bad = []
    with tempfile.TemporaryDirectory() as td:
        for name, text in (('R.hs', src), ('L.hs', layer), ('Low.hs', low),
                           ('Mid.hs', mid), ('Api.hs', api), ('Fac.hs', fac)):
            with open(os.path.join(td, name), 'w') as fh:
                fh.write(text)
        got, nbad, _ = report_rule(td)
        got = [re.sub(r'^(  \S+\.hs):\d+', r'\1', x) for x in got]
        if got != want or nbad != 20:
            bad.append(f'--rule ({nbad}):\n  ' + '\n  '.join(got))
        if main(['--rule', td]) != 1:
            bad.append('--rule with findings did not exit 1')
    return bad


def main(argv):
    if argv == ['--self-test']:
        return self_test()
    rule = argv[:1] == ['--rule']
    if rule:
        argv = argv[1:]
    if len(argv) != 1 or argv[0].startswith('--'):
        print(__doc__.split('\n\n')[1], file=sys.stderr)
        return 2
    lines, nbad, nfiles = (report_rule if rule else report)(argv[0])
    if not nfiles:
        print(f'no .hs file under {argv[0]}', file=sys.stderr)
        return 2
    print('\n'.join(lines))
    return 1 if nbad else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
