#!/usr/bin/env python3
"""Flag arguments banged on some equations but not forced on every path.

Usage:
  python3 tools/bang-lazy-check.py ROOT... [--dumps GLOB]...
  python3 tools/bang-lazy-check.py --selftest

A bang on one equation of a multi-equation definition signals intent to be
strict, but GHC keeps one demand per argument for the whole function,
joined lazily across paths -- one path that skips forcing makes the
argument lazy and its worker argument boxed, however many bangs the other
equations carry. This tool finds that shape.

Pass 1 (syntactic): flag every argument position of a multi-equation
definition that is banged in >=1 equation while another equation leaves it
unforced. Guard-form single-equation definitions cannot have the shape and
are never flagged. Three body-aware rules refine the per-path judgment on
guard-free equations whose body sits on the definition line: a body that
is exactly the argument returns it purely, which forces (marker pret); a
body headed by return/pure wraps without forcing (marker mret -- a
definite leak, whatever the other equations do); and a body headed by
error/undefined diverges, and a diverging path is strict (marker botm). A
candidate all of whose non-bang paths force is dropped rather than
printed. The rules are deliberately conservative: they fire only on
single-line guard-free bodies, the bottom rule tolerates no bare infix
operator other than $ and $!, the return rule none but $, and
project-specific bottom helpers (a cannotHappen) are not recognized --
such paths stay flagged for the reader. Remaining flags: a wildcard,
~-pattern or mret path is STRONG, a bare variable WEAK. Two markers
annotate variable paths without changing any verdict: rec (the body is
headed by the function's own name -- apply the fixpoint rule by hand) and
gvar (the variable occurs in the equation's same-line guard text -- the
guard probably forces it, though occurrence is not proof: a guard
@const True m@ scrutinizes nothing). The fixpoint is deliberately NOT
mechanized into an auto-clear: "recursive head plus forcing exits" is
unsound -- @f 0 !acc = acc; f k acc = f (k - 1) 0@ has both and is lazy
in acc, the recursion dropping the argument -- and the sound refinement,
that the call passes the variable in a position that forces it, is
type-dependent (@acc + r@ forces at Int, not at a lazy Num; @Just acc@
never does), hence out of reach syntactically. rec stays a marker.

Pass 2 (--dumps, exact for top-level bindings): cross-check candidates
against GHC's demand signatures. Produce them with an optimized build --
demand analysis does not run at -O0 -- e.g.

  cabal build --ghc-options='-ddump-dmd-signatures -ddump-to-file'
  python3 tools/bang-lazy-check.py SRC \\
    --dumps 'dist-newstyle/**/*.dump-dmd-signatures'

A strict demand at the flagged position CLEARS the candidate (GHC found
forcing on every path); a lazy demand CONFIRMS it. The verdict prints the
whole signature, not just the one argument's demand, so that a
dictionary-argument miscount in the trailing-slot position mapping is
visible to the reader. An UNVERIFIED verdict names its cause: local
definitions never appear in dumps; a module with no dump file was built
without the flags or came from the store; a dumped module lacking the
name usually means INLINE dissolved the binding, so its strictness lives
at the call sites. The unverified residue needs a reader or an extracted
probe module. The reader's rules, each measured in the selftest: a
literal or constructor pattern forces; a bang forces only the paths on
which it is reached (earlier pattern failure in the same equation skips
it); guards force their scrutinees on every guard path; a plain return of
the argument forces it, a monadic `return arg` does not; a diverging body
is a strict path; and strictness can arrive with no bang at all, via a
strict callee or the recursive fixpoint.

Known limitations: equations whose argument list continues on the next
source line are skipped (counted per file, and the count also includes
do-block call lines the line parser cannot tell from equations, so it
overstates); infix and operator definitions are skipped; block comments
are tracked only crudely.

Non-vacuity: --selftest writes probe modules to a temp directory, compiles
them with ghc -O, and asserts the exact verdict for every case above in
both directions -- lazy cases must come back CONFIRMED (the monadic-return
probe as STRONG), strict-without-enough-bangs cases CLEARED, the
pure-return and bottom-body probes absent entirely, and the FastReshape-
shaped local loops flagged UNVERIFIED with their bottom-body catch-all
dropped. The selftest was itself proven non-vacuous by deliberately
breaking the checker (2026-08-09): inverting the strictness-letter test
in verdict() failed it with five named mismatches (every CONFIRMED read
CLEARED and vice versa); removing 'wild' from the flag condition failed
it with all local flags missing and the wildcard-path top-level
candidates demoted to WEAK; after the body-aware rules were added,
disabling the bottom-head rule failed it with loopE and the flatten
locals reappearing as unexpected candidates, and disabling the
monadic-return upgrade demoted the mret probe to WEAK; after the markers
were added, disabling gvar misread gv's path list as var,bang and
disabling rec misread loopW2's and loopT's as ending in var.

Exit codes: 0 for a run over a tree, whatever it printed --- the
candidates are input for the reader, not findings --- and for a passing
selftest, 1 selftest failure, 2 blocked: no ghc on PATH, or a
--dumps glob matching no file, which until 2026-08-28 was accepted in
silence and reported every candidate UNVERIFIED blaming the build; the
selftest asserts the stop, and went red with it reverted in a copy.
A quiet run over a tree proves nothing until
--selftest has passed on the same machine, so run that first; and
candidates a run does print are untriaged input for the reader's rules
above, not confirmed defects.
"""

import contextlib
import glob
import io
import os
import re
import shutil
import subprocess
import sys
import tempfile
from collections import defaultdict

KEYWORDS = {
    'let', 'in', 'where', 'do', 'case', 'of', 'if', 'then', 'else',
    'data', 'type', 'newtype', 'class', 'instance', 'module', 'import',
    'deriving', 'infix', 'infixl', 'infixr', 'foreign', 'default',
}

PRUNE_DIRS = {'.git', 'dist', 'dist-newstyle'}
BOTTOM_HEADS = {'error', 'errorWithoutStackTrace', 'undefined'}
MONADIC_HEADS = {'return', 'pure'}

LINE_RE = re.compile(r"^(\s*)(let\s+)?([a-z_][A-Za-z0-9_']*)\s+(\S.*)$")
DUMP_RE = re.compile(r"^\s*([A-Za-z0-9_.'$]+):\s*(<.*)$")
COMMENT_RE = re.compile(r"(^|\s)--(\s|$|[^!#$%&*+./<=>?@\\^|~-])")
OPERATOR_RE = re.compile(r"[!#$%&*+./<=>?@\\^|~:-]+")


def strip_line_comment(line):
    m = COMMENT_RE.search(line)
    return line[:m.start()] if m else line


def split_top(rest):
    """Split into whitespace-separated tokens at paren/bracket depth 0.

    String literals are kept whole, so an operator inside an error message
    ("N == 0") cannot masquerade as a bare infix operator.
    """
    toks, buf, depth, in_str, prev = [], '', 0, False, ''
    for ch in rest:
        if ch == '"' and prev != '\\':
            in_str = not in_str
        elif not in_str:
            if ch in '([':
                depth += 1
            elif ch in ')]':
                depth -= 1
        if ch.isspace() and depth == 0 and not in_str:
            if buf:
                toks.append(buf)
            buf = ''
        else:
            buf += ch
        prev = ch
    if buf:
        toks.append(buf)
    return toks


def classify(tok):
    m = re.match(r"^[a-z_][A-Za-z0-9_']*@(.+)$", tok)  # as-pattern
    if m:
        tok = m.group(1)
    while tok.startswith('(') and tok.endswith(')') and len(tok) > 2:
        inner = tok[1:-1].strip()
        if not inner:
            return 'force'
        tok = inner
    if tok.startswith('!'):
        return 'bang'
    if tok == '_':
        return 'wild'
    if tok.startswith('~'):
        return 'lazy'
    if re.fullmatch(r"[a-z_][A-Za-z0-9_']*", tok):
        return 'var'
    # literals, constructor patterns, tuples, cons cells: matching forces
    return 'force'


def occurs_in(name, toks):
    """Delimited occurrence of an identifier among tokens."""
    return re.search(r"(?<![A-Za-z0-9_'])%s(?![A-Za-z0-9_'])" % re.escape(name),
                     ' '.join(toks)) is not None


def path_status(cls, argtok, rhs_toks, guard_toks, fname):
    """('force'|'nonforce'|'unknown', display marker) for one equation."""
    if cls in ('bang', 'force'):
        return 'force', cls
    if rhs_toks:
        bare_ops = [t for t in rhs_toks[1:] if OPERATOR_RE.fullmatch(t)]
        if (rhs_toks[0] in BOTTOM_HEADS
                and all(t in ('$', '$!') for t in bare_ops)):
            return 'force', 'botm'
        if cls == 'var' and rhs_toks == [argtok]:
            return 'force', 'pret'
        if (rhs_toks[0] in MONADIC_HEADS
                and all(t == '$' for t in bare_ops)):
            return 'nonforce', 'mret'
    if cls == 'wild':
        return 'nonforce', 'wild'
    if cls == 'lazy':
        return 'unknown', 'lazy'
    if guard_toks and occurs_in(argtok, guard_toks):
        return 'unknown', 'gvar'
    if rhs_toks and rhs_toks[0] == fname:
        return 'unknown', 'rec'
    return 'unknown', 'var'


def parse_equations(path):
    """Per equation: (line, col, name, classes, argc, arg tokens, rhs toks).

    rhs toks is None when the equation has guards or a body continuing on
    later lines -- the body-aware path rules then stay out of it.
    """
    with open(path, encoding='utf-8', errors='replace') as fh:
        lines = fh.readlines()
    eqs, unparsed, in_block = [], 0, 0
    for idx, raw in enumerate(lines):
        line = raw.rstrip('\n')
        if in_block:
            if '-}' in line:
                in_block = 0
                line = line.split('-}', 1)[1]
            else:
                continue
        if '{-' in line and '-}' not in line:
            line = line.split('{-', 1)[0]
            in_block = 1
        line = strip_line_comment(line)
        if not line.strip():
            continue
        m = LINE_RE.match(line)
        if not m:
            continue
        name = m.group(3)
        if name in KEYWORDS:
            continue
        rest = m.group(4)
        if '`' in rest:
            continue
        toks = split_top(rest)
        args, rhs_toks, guard_toks, ok = [], None, None, False
        for j, t in enumerate(toks):
            if t == '=':
                ok = True
                rhs_toks = toks[j + 1:] or None
                break
            if t == '|':
                ok = True
                gts = toks[j + 1:]
                if '=' in gts:
                    gts = gts[:gts.index('=')]
                guard_toks = gts or None
                break
            if t == '::' or t.startswith('::'):
                args = None
                break
            if (t.startswith('=') and t != '==') or t in ('==', '<-', '->'):
                args = None
                break
            args.append(t)
        if args is None or not args:
            continue
        if not ok:
            # no '=' or '|' on this line: accept only if the next
            # non-blank line opens with a guard (multi-line guard style)
            nxt = ''
            for j in range(idx + 1, min(idx + 3, len(lines))):
                s = strip_line_comment(lines[j]).strip()
                if s:
                    nxt = s
                    break
            if not nxt.startswith('|'):
                unparsed += 1
                continue
        eqs.append((idx + 1, m.start(3), name, [classify(t) for t in args],
                    len(args), args, rhs_toks, guard_toks))
    return eqs, unparsed


def group_equations(eqs):
    """Group equations by (name, column, arity).

    Equations of one definition may be separated by nested definitions from
    an earlier equation's body (a where/let block), which sit at a deeper
    column -- so a group stays open across deeper-column equations and
    closes when a different definition appears at its own column or
    shallower.
    """
    groups, open_groups = [], {}
    for eq in eqs:
        col = eq[1]
        for c in [c for c in open_groups if c > col]:
            grp = open_groups.pop(c)
            if len(grp) >= 2:
                groups.append(grp)
        cur = open_groups.get(col)
        if cur and (cur[-1][2], cur[-1][4]) == (eq[2], eq[4]):
            cur.append(eq)
        else:
            if cur and len(cur) >= 2:
                groups.append(cur)
            open_groups[col] = [eq]
    groups.extend(g for g in open_groups.values() if len(g) >= 2)
    return groups


def find_candidates(path):
    eqs, unparsed = parse_equations(path)
    out = []
    for grp in group_equations(eqs):
        argc = grp[0][4]
        for i in range(argc):
            if not any(eq[3][i] == 'bang' for eq in grp):
                continue
            statuses, markers = [], []
            for eq in grp:
                s, mk = path_status(eq[3][i], eq[5][i], eq[6], eq[7],
                                    grp[0][2])
                statuses.append(s)
                markers.append(mk)
            if all(s == 'force' for s in statuses):
                continue  # every path forces: auto-cleared, not printed
            strength = ('STRONG' if any(s == 'nonforce' for s in statuses)
                        else 'WEAK')
            out.append({
                'file': path, 'line': grp[0][0], 'name': grp[0][2],
                'local': grp[0][1] > 0, 'arg': i + 1, 'argc': argc,
                'classes': markers, 'strength': strength,
            })
    return out, unparsed


def load_dumps(patterns):
    """(name -> {qualified: signature}, set of dumped module stems)."""
    sigs, stems = defaultdict(dict), set()
    for pat in patterns:
        for path in glob.glob(pat, recursive=True):
            stems.add(os.path.basename(path).split('.')[0])
            with open(path, encoding='utf-8', errors='replace') as fh:
                for line in fh:
                    m = DUMP_RE.match(line)
                    if not m:
                        continue
                    qual, sig = m.groups()
                    base = qual.rsplit('.', 1)[-1]
                    if not base.startswith('$'):
                        sigs[base][qual] = sig
    return sigs, stems


def verdict(cand, sigs, dumped_stems):
    if cand['local']:
        return 'UNVERIFIED (local definition; not in dump)'
    stem = os.path.splitext(os.path.basename(cand['file']))[0]
    entry = sigs.get(cand['name'])
    if not entry:
        if stem in dumped_stems:
            return ('UNVERIFIED (module dumped but name absent -- inlined '
                    'away? check for an INLINE pragma, or read call sites)')
        return ('UNVERIFIED (no dump for this module -- built without the '
                'dump flags, or from the store)')
    quals = [q for q in entry if q.rsplit('.', 2)[-2:-1] == [stem]] or list(entry)
    sig = entry[quals[0]]
    brackets = re.findall(r'<([^<>]*)>', sig)
    n = cand['argc']
    if len(brackets) < n:
        return 'UNVERIFIED (signature arity %d < %d: %s)' % (
            len(brackets), n, sig)
    b = brackets[len(brackets) - n + cand['arg'] - 1]
    if b and b[0] in '1SB':
        return 'CLEARED: strict per GHC, arg demand <%s> in %s' % (b, sig)
    return 'CONFIRMED: lazy per GHC, arg demand <%s> in %s' % (b, sig)


def collect_files(roots):
    files = []
    for r in roots:
        if os.path.isdir(r):
            for dirpath, dirnames, filenames in os.walk(r):
                dirnames[:] = [d for d in dirnames if d not in PRUNE_DIRS]
                files += [os.path.join(dirpath, f) for f in filenames
                          if f.endswith('.hs')]
        else:
            files.append(r)
    return sorted(files)


def run(roots, dump_pats):
    sigs, stems = load_dumps(dump_pats) if dump_pats else ({}, set())
    if dump_pats and not stems:
        print('BLOCKED: no file matches --dumps %s; every verdict would'
              ' read UNVERIFIED' % ' '.join(dump_pats))
        return 2
    total = unparsed_total = 0
    for path in collect_files(roots):
        cands, unparsed = find_candidates(path)
        unparsed_total += unparsed
        for c in cands:
            total += 1
            v = (verdict(c, sigs, stems) if dump_pats
                 else 'unchecked (no --dumps)')
            print('%s:%d %s%s arg %d/%d [%s] %s\n    %s' % (
                c['file'], c['line'], c['name'],
                ' (local)' if c['local'] else '',
                c['arg'], c['argc'], ','.join(c['classes']),
                c['strength'], v))
    print('\n%d candidate(s); %d unparsed line(s) skipped (includes '
          'do-block call lines)' % (total, unparsed_total))
    return 0


SELFTEST_TOP = '''\
{-# LANGUAGE BangPatterns #-}
module SelfTest (loopW, loopW1, loopW2, loopT, loopE, loopG, cnt,
                 benchGo, mret, gv) where

-- Wildcard base case: lazy join; the bangs bind only their own equation.
loopW :: Int -> Int -> Int
loopW 0 _ = 0
loopW 1 acc = acc
loopW !k !acc = loopW (k - 1) (acc + k)

-- Banged wildcard closes the leak, and the var equation returns purely:
-- every path forces syntactically, so this candidate must be absent.
loopW1 :: Int -> Int -> Int
loopW1 0 !_ = 0
loopW1 1 acc = acc
loopW1 !k !acc = loopW1 (k - 1) (acc + k)

-- Same with no other bang anywhere: strictness from the fixpoint alone.
loopW2 :: Int -> Int -> Int
loopW2 0 !_ = 0
loopW2 1 acc = acc
loopW2 k acc = loopW2 (k - 1) (acc + k)

-- Banged first equation, leaking second: the bang covers only its path.
loopT :: Int -> Int -> Int
loopT 0 !_ = 0
loopT 1 _ = 1
loopT 2 acc = acc
loopT k acc = loopT (k - 1) (acc + k)

-- Wildcard base case whose body is bottom: a diverging path is strict,
-- so the bottom-head rule must drop this candidate before any dump.
loopE :: Int -> Int -> Int
loopE 0 _ = error "impossible"
loopE 1 acc = acc
loopE !k !acc = loopE (k - 1) (acc + k)

-- Guard form banged on every path: not a candidate at all.
loopG :: Int -> Int -> Int
loopG !k !acc
  | k <= 0 = 0
  | k == 1 = acc
  | otherwise = loopG (k - 1) (acc + k)

-- No bangs anywhere: not a candidate.
cnt :: Int -> Int -> Int
cnt k acc
  | k <= 0 = acc
  | otherwise = cnt (k - 1) (acc + k)

-- Pure return of the accumulator on the base path: forcing, so the
-- pure-return rule must drop this candidate before any dump.
benchGo :: [Int] -> Int -> Int
benchGo [] p = p
benchGo (x : xs) !p = benchGo xs (p + x)

-- Monadic return does not force (Just's field is lazy): the leak the
-- return-head rule must upgrade to STRONG, and the dump must confirm.
mret :: Int -> Int -> Maybe Int
mret 0 acc = return acc
mret !k !acc = mret (k - 1) (acc + k)

-- The guard scrutinizes arg 1 on its var equation (marker gvar), and the
-- same equation returns arg 2 purely; the dump clears both.
gv :: Int -> Int -> Int
gv n acc | n == 0 = acc
gv !n !acc = gv (n - 1) (acc + n)
'''

# Scanner-shape control mirroring FastReshape.hs: let-bound equations, one
# definition's equations separated by a nested definition, a bottom-body
# catch-all that the bottom-head rule must recognize as a strict path.
# Scanned only, never compiled.
SELFTEST_LOCAL = '''\
module SelfTestLocal (flattenVector) where
flattenVector :: [Int] -> [Int] -> Int -> [Int]
flattenVector sh ist oo =
  let flatten [d] (is:_) _ !ioffs !ooffs =
        copyLoop is d ioffs ooffs
      flatten (d:ds) (ais:iss) (aos:oss) !aioffs !aooffs =
        let recLoop 0 _ _ = []
            recLoop !k !ioffs !ooffs =
              flatten ds iss oss ioffs ooffs ++ recLoop (k - 1) ioffs ooffs
        in recLoop d aioffs aooffs
      flatten _ _ _ _ _ = error "impossible: d == 0"
      copyLoop _ 0 _ _ = []
      copyLoop !is !d !i !o = i : copyLoop is (d - 1) (i + is) (o + 1)
  in flatten sh ist ist oo oo
'''

EXPECT_TOP = {
    ('loopW', 2): ('STRONG', 'CONFIRMED'),
    ('loopW2', 2): ('WEAK', 'CLEARED'),
    ('loopT', 2): ('STRONG', 'CONFIRMED'),
    ('mret', 2): ('STRONG', 'CONFIRMED'),
    ('gv', 1): ('WEAK', 'CLEARED'),
    ('gv', 2): ('WEAK', 'CLEARED'),
}
# loopE (bottom body), loopW1 (banged wildcard plus pure return), benchGo
# (pure return), cnt and loopG must be absent.
EXPECT_MARKERS = {
    ('loopW2', 2): 'bang,pret,rec',
    ('loopT', 2): 'bang,wild,pret,rec',
    ('mret', 2): 'mret,bang',
    ('gv', 1): 'gvar,bang',
    ('gv', 2): 'var,bang',
}
EXPECT_LOCAL = {('recLoop', 2), ('recLoop', 3), ('copyLoop', 1),
                ('copyLoop', 3), ('copyLoop', 4)}
# flatten's positions must be absent: its catch-all body is bottom.


def selftest():
    if not shutil.which('ghc'):
        print('BLOCKED: no ghc on PATH, selftest did not run')
        return 2
    bad = []
    with tempfile.TemporaryDirectory() as td:
        top = os.path.join(td, 'SelfTest.hs')
        loc = os.path.join(td, 'SelfTestLocal.hs')
        with open(top, 'w') as fh:
            fh.write(SELFTEST_TOP)
        with open(loc, 'w') as fh:
            fh.write(SELFTEST_LOCAL)
        r = subprocess.run(['ghc', '-O', '-c', '-fforce-recomp', '-w',
                            '-ddump-to-file', '-ddump-dmd-signatures',
                            'SelfTest.hs'], cwd=td, capture_output=True)
        if r.returncode != 0:
            print('BLOCKED: probe compilation failed:\n%s'
                  % r.stderr.decode())
            return 2
        sigs, stems = load_dumps([os.path.join(td, '*.dump-dmd-signatures')])
        cands, _ = find_candidates(top)
        got = {(c['name'], c['arg']):
               (c['strength'], verdict(c, sigs, stems).split(':')[0].split()[0])
               for c in cands}
        for key, want in EXPECT_TOP.items():
            if key not in got:
                bad.append('missing candidate %s arg %d' % key)
            elif got[key] != want:
                bad.append('%s arg %d: expected %s, got %s'
                           % (key + (want, got[key])))
        for key in set(got) - set(EXPECT_TOP):
            bad.append('unexpected candidate %s arg %d' % key)
        gotm = {(c['name'], c['arg']): ','.join(c['classes']) for c in cands}
        for key, want in EXPECT_MARKERS.items():
            if gotm.get(key) != want:
                bad.append('%s arg %d: expected markers [%s], got [%s]'
                           % (key + (want, gotm.get(key))))
        lcands, _ = find_candidates(loc)
        lgot = {(c['name'], c['arg']) for c in lcands
                if c['local'] and c['strength'] == 'STRONG'}
        for key in EXPECT_LOCAL - lgot:
            bad.append('missing local candidate %s arg %d' % key)
        for key in lgot - EXPECT_LOCAL:
            bad.append('unexpected local candidate %s arg %d' % key)
        with contextlib.redirect_stdout(io.StringIO()) as buf:
            code = run([top], [os.path.join(td, 'no-such-*.dump')])
        if code != 2 or 'BLOCKED' not in buf.getvalue():
            bad.append('a --dumps glob matching nothing did not block')
    if bad:
        for b in bad:
            print('FAIL: %s' % b)
        return 1
    print('ok:   all %d dump-checked verdicts, %d marker lines and %d local'
          ' flags as expected'
          % (len(EXPECT_TOP), len(EXPECT_MARKERS), len(EXPECT_LOCAL)))
    return 0


def main():
    args = sys.argv[1:]
    if args == ['--selftest']:
        sys.exit(selftest())
    dump_pats = []
    while '--dumps' in args:
        i = args.index('--dumps')
        if i + 1 >= len(args):
            print('--dumps needs a glob argument', file=sys.stderr)
            sys.exit(2)
        dump_pats.append(args[i + 1])
        del args[i:i + 2]
    if not args:
        print(__doc__.split('\n\n')[0])
        print('\nUsage: bang-lazy-check.py ROOT... [--dumps GLOB]... '
              '| --selftest')
        sys.exit(2)
    sys.exit(run(args, dump_pats))


if __name__ == '__main__':
    main()
