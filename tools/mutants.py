"""The mutants of tools/: each checker broken on purpose, and its self-test red.

Read by `selftest-mutants.py tools`, which makes a shared clone of this
repository, applies each mutant to the clone and requires the judge -- the
tool's own self-test -- to FAIL on it; a mutant whose anchor has moved is
LOST, not caught. Each was watched failing before it was written down here;
the comment above each names the defect record it replays. These are the
mutants of the two tools that stayed when the rest left for ~/slop/tools,
whose mutants are in ~/slop/tools/mutants.py, and of the criterion reader
check-conv-bench-props.py keeps a copy of.
"""

COPY = 'clone'
SIBLINGS = []
TIMEOUT = 600

ST = ['python3', '{file}', '--self-test']

MUTANTS = [
    # check-conv-bench-props: "Reverting the zero guard ... turned it red"
    ('check-conv-bench-props zero slope divided by in le()', 'check-conv-bench-props.py',
     '        ratio = f"{a / b:.2f}" if b else "n/a, zero"\n', '        ratio = f"{a / b:.2f}"\n', ST),
    # check-conv-bench-props: "disarming the gate" -- the sample-count arm
    ('check-conv-bench-props sample-count arm of the slope gate disarmed', 'check-conv-bench-props.py',
     "MIN_SAMPLES = 10\n", "MIN_SAMPLES = 0\n", ST),
    # check-conv-bench-props: "disarming the gate" -- the allocation-R2 arm
    ('check-conv-bench-props allocation-R2 arm of the slope gate disarmed', 'check-conv-bench-props.py',
     "MIN_ALLOC_R2 = 0.999\n", "MIN_ALLOC_R2 = 0.0\n", ST),
    # check-conv-bench-props: the time-R2 arm of the gate
    ('check-conv-bench-props time-R2 arm of the slope gate disarmed', 'check-conv-bench-props.py',
     "MIN_R2 = 0.95\n", "MIN_R2 = 0.0\n", ST),
    # check-fresh-draws (2026-10-02): mutants for each rule and for each
    # blanking branch the rules rely on, each watched turning the self-test red
    # before it was written here.
    ('check-fresh-draws rule 1 disarmed', 'check-fresh-draws.py',
     '        if DUPABLE in toks and (d.module, d.name) not in ALLOW:\n',
     '        if DUPABLE in toks and False:\n', ST),
    ('check-fresh-draws forbidden primitives unchecked', 'check-fresh-draws.py',
     '        for bad in FORBIDDEN:\n',
     '        for bad in ():\n', ST),
    ('check-fresh-draws rule 2 boundary at unsafePerformIO removed', 'check-fresh-draws.py',
     '                if PLAIN not in toks and toks & draw:\n',
     '                if toks & draw:\n', ST),
    ('check-fresh-draws rule 2 seeded with nothing', 'check-fresh-draws.py',
     '    draw = {name for module, name in COUNTERS}\n',
     '    draw = set()\n', ST),
    ('check-fresh-draws stale entry unchecked', 'check-fresh-draws.py',
     '        if DUPABLE not in toks:\n',
     '        if False:\n', ST),
    ('check-fresh-draws vanished entry unchecked', 'check-fresh-draws.py',
     '            if key[0] in modules:\n',
     '            if False:\n', ST),
    ('check-fresh-draws vanished counter unchecked', 'check-fresh-draws.py',
     '        if key[0] in modules and key not in present:\n',
     '        if False:\n', ST),
    ('check-fresh-draws operators no tokens (check-fresh-draws-02)',
     'check-fresh-draws.py',
     'TOKEN = re.compile(r"(?:[A-Z][\\w\']*\\.)*([A-Za-z_][\\w\']*#?|%s)" % OP)\n',
     'TOKEN = re.compile(r"[A-Za-z_][\\w\']*#?")\n', ST),
    ('check-fresh-draws an infix equation filed under its left argument',
     'check-fresh-draws.py',
     '    if m and m.group(2) not in RESERVED:\n',
     '    if False:\n', ST),
    ('check-fresh-draws line comments not blanked', 'check-fresh-draws.py',
     "        elif text.startswith('--', i) and (i == 0 or text[i - 1] not in SYMBOL):\n",
     '        elif False:\n', ST),
    ('check-fresh-draws dashes after a symbol taken for a comment', 'check-fresh-draws.py',
     "        elif text.startswith('--', i) and (i == 0 or text[i - 1] not in SYMBOL):\n",
     "        elif text.startswith('--', i):\n", ST),
    ('check-fresh-draws dashes before a symbol taken for a comment', 'check-fresh-draws.py',
     '            if j < n and text[j] in SYMBOL:  # an operator such as -->\n',
     '            if False:  # an operator such as -->\n', ST),
    ('check-fresh-draws block comments not blanked', 'check-fresh-draws.py',
     "        elif text.startswith('{-', i):\n",
     '        elif False:\n', ST),
    ('check-fresh-draws block comments not nested', 'check-fresh-draws.py',
     '                depth += 1\n',
     '                depth += 0\n', ST),
    ('check-fresh-draws strings not blanked', 'check-fresh-draws.py',
     '        elif c == \'"\':\n',
     '        elif False:\n', ST),
    ('check-fresh-draws character literals not recognised', 'check-fresh-draws.py',
     '            m = CHAR_LIT.match(text, i)\n',
     '            m = None\n', ST),
    ('check-fresh-draws module named by nothing', 'check-fresh-draws.py',
     "    module = m.group(1) if m else 'Main'\n",
     "    module = 'Main'\n", ST),
    ('check-fresh-draws a name split from its signature', 'check-fresh-draws.py',
     '                cur = named.get(word)\n',
     '                cur = None\n', ST),
    ('check-fresh-draws an unreadable file not exit 2', 'check-fresh-draws.py',
     "            print('cannot read %s: %s; nothing checked' % (p, e),\n                  file=sys.stderr)\n            return 2\n",
     "            print('cannot read %s: %s; nothing checked' % (p, e),\n                  file=sys.stderr)\n            return 0\n", ST),
    # check-conv-bench-props: a missing benchmark exits 1 again
    # (check-conv-bench-props-03)
    ('check-conv-bench-props missing benchmark exits 1', 'check-conv-bench-props.py',
     '            usage_error(f"benchmark missing from the JSON (not a full run?): {k}")\n',
     '            sys.exit(f"benchmark missing from the JSON (not a full run?): {k}")\n', ST),
    # The criterion reader's copy, whose original's mutants are in
    # ~/slop/tools/mutants.py. An unreadable collection tracebacks at 1 again
    # (check-conv-bench-props-02)
    ('check-conv-bench-props unreadable collection tracebacks instead of exit 2', 'check-conv-bench-props.py',
     '    except (OSError, ValueError, LookupError, TypeError) as e:\n',
     '    except (OSError, ValueError, LookupError, TypeError) as e:\n        raise\n', ST),
    # A regression missing a field tracebacks at 1 again
    # (check-conv-bench-props-04)
    ('check-conv-bench-props malformed regression tracebacks instead of exit 2', 'check-conv-bench-props.py',
     '        raise CriterionError(f"{path}: the regressions of {name} lack {e}")\n', "        raise\n", ST),
    ('check-conv-bench-props estimate() returns what it finds unchecked', 'check-conv-bench-props.py',
     '    if not finite(v):\n', '    if False:\n', ST),
]
