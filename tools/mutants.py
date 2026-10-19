"""The mutants of tools/: each checker broken on purpose, and its self-test red.

Read by `selftest-mutants.py tools`, which makes a shared clone of this
repository (and of the sibling checkouts beside it, where mounted), applies
each mutant to the clone and requires the judge -- the tool's own self-test
-- to FAIL on it; a mutant whose anchor has moved is LOST, not caught. These
replace the proofs that were dated sentences in each tool's docstring, "proved
non-vacuous by breaking the checker in a copy (2026-08-14)", which expire the
moment the code under them moves, with nothing to say so. Each was watched
failing before it was written down here; the comment above each names the
docstring proof or the defect record it replays.

The clone is what lets the judges run: every tool finds the repository from
its own path and asks git about it, and check-doc-refs' self-test wants the
two sibling checkouts as real directories. With a sibling unmounted that
tool's judge is BLOCKED at 2 in the clone and its mutants are LOST, which is
the honest reading.
"""

COPY = 'clone'
SIBLINGS = ['../ox-arrays', '../orthotope', '../LambdaHack']
# bang-lazy-check's self-test compiles probe modules.
TIMEOUT = 600

ST = ['python3', '{file}', '--self-test']
SELFTEST = ['python3', '{file}', '--selftest']

# loop-offsets.py has no self-test, so its judges replant a case's fixture
# from defects.json and ask the mutated program the case's own question,
# requiring what the fixed program prints; the first plants the site below,
# saved for its mutant and no case.
OFFSETS = r'''
import json, os, shutil, subprocess, sys, tempfile
prog, how, what, want, *absent = sys.argv[1:]
t = tempfile.mkdtemp()
try:
    if how == '--record':
        recs = json.load(open(os.path.join(os.path.dirname(prog),
                                           'defects.json')))['RECORDS']
        r = [x for x in recs if x['id'] == what]
        if len(r) != 1 or subprocess.run(['bash', '-c', r[0]['plant_cmd']],
                                         cwd=t).returncode:
            sys.exit(2)
        argv = [a.replace('{tmp}', t) for a in r[0]['invoke']]
    else:
        name, text = what.split('\n', 1)
        open(os.path.join(t, name), 'w').write(text)
        argv = ['--survey', os.path.join(t, name)]
    p = subprocess.run([sys.executable, prog] + argv, cwd=t,
                       capture_output=True, text=True)
    sys.exit(0 if want in p.stdout and not any(a in p.stdout for a in absent)
             else 1)
finally:
    shutil.rmtree(t, ignore_errors=True)
'''


def offsets(case, want, *absent):
    return lambda path: ['python3', '-c', OFFSETS, path, '--record', case,
                         want, *absent]


def offsets_listing(name, text, want):
    return lambda path: ['python3', '-c', OFFSETS, path, '--listing',
                         name + '\n' + text, want]


# The ninth saved site, `run33-gheadexit` from 0x4a52b6 to 0x4a52ff: a `jmp
# stg_gc_noregs`, the `nopl` pad after it and the table word `78 f4`, a `js
# -12` back to the jmp itself, which the flow test alone refuses.
PHANTOM8_LISTING = """\

run33-gheadexit:     file format elf64-x86-64


Disassembly of section .text:

00000000004a52b6 <microzm0zi1zminplacezmmicro_Main_zdfNFDataTzuzdcrnf_info+0x9732e>:
  4a52b6:\t48 c7 45 e8 40 52 4a \tmovq   $0x4a5240,-0x18(%rbp)
  4a52bd:\t00 
  4a52be:\t4c 89 75 f0          \tmov    %r14,-0x10(%rbp)
  4a52c2:\t48 89 5d f8          \tmov    %rbx,-0x8(%rbp)
  4a52c6:\t48 89 75 00          \tmov    %rsi,0x0(%rbp)
  4a52ca:\t48 83 c5 e8          \tadd    $0xffffffffffffffe8,%rbp
  4a52ce:\te9 8d 5b 33 01       \tjmp    17dae60 <stg_gc_noregs>
  4a52d3:\t0f 1f 44 00 00       \tnopl   0x0(%rax,%rax,1)
  4a52d8:\t78 f4                \tjs     4a52ce <microzm0zi1zminplacezmmicro_Main_zdfNFDataTzuzdcrnf_info+0x97346>
  4a52da:\tff                   \t(bad)
  4a52db:\tff                   \t(bad)
  4a52dc:\tff                   \t(bad)
  4a52dd:\tff                   \t(bad)
  4a52de:\tff                   \t(bad)
  4a52df:\tff 06                \tincl   (%rsi)
  4a52e1:\t07                   \t(bad)
  4a52ea:\t00 00                \tadd    %al,(%rax)
  4a52ec:\t06                   \t(bad)
  4a52ed:\t00 00                \tadd    %al,(%rax)
  4a52ef:\t00 02                \tadd    %al,(%rdx)
  4a52f1:\t00 00                \tadd    %al,(%rax)
  4a52f3:\t00 00                \tadd    %al,(%rax)
  4a52f5:\t00 00                \tadd    %al,(%rax)
  4a52f7:\t00 0e                \tadd    %cl,(%rsi)
  4a52f9:\t00 00                \tadd    %al,(%rax)
  4a52fb:\t00 00                \tadd    %al,(%rax)
  4a52fd:\t00 00                \tadd    %al,(%rax)
  4a52ff:\t00 48 8d             \tadd    %cl,-0x73(%rax)
"""


MUTANTS = [
    # bang-lazy-check: "inverting the strictness-letter test in verdict()" (2026-08-09)
    ('bang-lazy-check strictness-letter test in verdict() inverted', 'bang-lazy-check.py',
     "    if b and b[0] in '1SB':\n", "    if not (b and b[0] in '1SB'):\n", SELFTEST),
    # bang-lazy-check: "removing 'wild' from the flag condition" -- no 'wild' literal
    # remains in find_candidates; the nearest live branch is path_status's wildcard
    # arm, and it fails the same rows (local flags missing)
    ('bang-lazy-check wildcard path no longer a non-forcing path', 'bang-lazy-check.py',
     "    if cls == 'wild':\n        return 'nonforce', 'wild'\n",
     "    if cls == 'wild':\n        return 'force', 'wild'\n", SELFTEST),
    # bang-lazy-check: "disabling the bottom-head rule failed it with loopE ... reappearing"
    ('bang-lazy-check bottom-head rule disabled', 'bang-lazy-check.py',
     "            return 'force', 'botm'\n", "            return 'unknown', 'botm'\n", SELFTEST),
    # bang-lazy-check: "disabling the monadic-return upgrade demoted the mret probe to WEAK"
    ('bang-lazy-check monadic-return upgrade disabled', 'bang-lazy-check.py',
     "            return 'nonforce', 'mret'\n", "            return 'unknown', 'mret'\n", SELFTEST),
    # bang-lazy-check: "disabling gvar misread gv's path list as var,bang"
    ('bang-lazy-check gvar marker disabled', 'bang-lazy-check.py',
     "        return 'unknown', 'gvar'\n", "        return 'unknown', 'var'\n", SELFTEST),
    # bang-lazy-check: "disabling rec misread loopW2's and loopT's as ending in var"
    ('bang-lazy-check rec marker disabled', 'bang-lazy-check.py',
     "        return 'unknown', 'rec'\n", "        return 'unknown', 'var'\n", SELFTEST),
    # bang-lazy-check: "--dumps glob matching no file ... went red with it reverted"
    ('bang-lazy-check --dumps glob matching nothing accepted silently', 'bang-lazy-check.py',
     "    if dump_pats and not stems:\n", "    if dump_pats and not stems and False:\n", SELFTEST),
    # bang-lazy-check: --allow no longer fails on an unlisted or stale candidate,
    # so the one-listed and stale verdicts of the selftest read 0 (2026-09-13)
    ('bang-lazy-check --allow gate disarmed', 'bang-lazy-check.py',
     "    if allow is not None and (unlisted or stale):\n        return 1\n",
     "    if allow is not None and (unlisted or stale):\n        return 0\n", SELFTEST),
    # bench-baseline: "a baseline slope of 0 reports movement instead of dividing by it"
    ('bench-baseline zero baseline slope divided by', 'bench-baseline.py',
     "    if old == 0:\n", "    if old == 0 and False:\n", ST),
    # bench-baseline: "a flag missing its value exit 2 rather than 1 or a traceback"
    ('bench-baseline flag missing its value tracebacks instead of exit 2', 'bench-baseline.py',
     "            if i + 1 >= len(args):\n", "            if i + 1 > len(args):\n", ST),
    # bench-baseline: "--emit used to write allocation slopes as integers"
    ('bench-baseline --emit writes allocation slopes as integers', 'bench-baseline.py',
     '            print(f"{name}\\t{t:.9g}\\t{a:.9g}")\n',
     '            print(f"{name}\\t{t:.9g}\\t{a:.0f}")\n', ST),
    # bench-baseline: "no argument ... exit 2"
    ('bench-baseline no argument no longer exits 2', 'bench-baseline.py',
     "    if not rest:\n        usage_error(__doc__.split(\"\\n\\n\")[1])\n",
     "    if not rest:\n        pass\n", ST),
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
    # check-doc-examples: "blanking the name pattern ... 0/1 findings"
    ('check-doc-examples name pattern blanked', 'check-doc-examples.py',
     'NAME_RE = re.compile(r"\\b([A-Z][A-Za-z0-9_]{3,})\\b")\n', 'NAME_RE = re.compile(r"(?!x)x")\n', ST),
    # check-doc-examples: "disabling the output comparison ... 1/0"
    ('check-doc-examples output comparison disabled', 'check-doc-examples.py',
     "        if len(body) > 40 and body not in normsrc:\n", "        if False:\n", ST),
    # check-doc-examples: "dropping the doc-local exclusion ... 2/1"
    ('check-doc-examples doc-local exclusion dropped', 'check-doc-examples.py',
     '        if n in loc or re.search(r"\\b" + n + r"\\b", src):\n',
     '        if re.search(r"\\b" + n + r"\\b", src):\n', ST),
    # check-doc-examples: "removing the skip in a copy turned it red"
    ('check-doc-examples module skip removed', 'check-doc-examples.py',
     '    bodies = [b for b in own if not re.search(r"^module\\s+[\\w.]+", b, re.M)]\n',
     '    bodies = own\n', ST),
    # check-doc-examples: the skip narrowed back to `module Main`, as it was
    # until 2026-10-15, checks the self-test's other module block
    ('check-doc-examples module skip narrowed to Main', 'check-doc-examples.py',
     '    bodies = [b for b in own if not re.search(r"^module\\s+[\\w.]+", b, re.M)]\n',
     '    bodies = [b for b in own if not re.search(r"^module\\s+Main\\b", b, re.M)]\n', ST),
    # check-doc-examples: the doc-local names taken from the checked blocks
    # alone failed two issue documents on types a module block declares
    # (2026-10-15, before the skip was committed)
    ('check-doc-examples skipped module blocks declaring nothing', 'check-doc-examples.py',
     '    loc = local_names(strip_comments("".join(own)))\n',
     '    loc = local_names(code)\n', ST),
    # check-doc-examples: "a source list naming nothing reads as none rather than as an
    # empty corpus" (2026-08-28)
    ('check-doc-examples empty source list read as an empty corpus', 'check-doc-examples.py',
     "    if p.returncode != 0 or not paths:\n        return None\n",
     "    if p.returncode != 0 or not paths:\n        return \"\"\n", ST),
    # check-doc-refs: "a dead cabal-target loop" (2026-08-14)
    ('check-doc-refs cabal-target loop dead', 'check-doc-refs.py',
     "    for name in sorted(set(CABAL_RE.findall(commands))):\n", "    for name in []:\n", ST),
    # check-doc-refs: "a dead sibling resolution"
    ('check-doc-refs sibling resolution dead', 'check-doc-refs.py',
     "    roots = [r for r in SIBLING_ROOTS if os.path.isdir(r)]\n    if not roots:\n        return []\n",
     "    return []\n", ST),
    # check-doc-refs: "dropping the path-shape gate off the sibling arm ... on exactly
    # the `tests` rubber-stamp row"
    ('check-doc-refs path-shape gate dropped off the sibling arm', 'check-doc-refs.py',
     "        elif path_shaped(token, top_level) and sibling_hit(token, siblings):\n",
     "        elif sibling_hit(token, siblings):\n", ST),
    # check-doc-refs: "a CITE_RE blind to the range citation ... on exactly the
    # skipped-citation guard"
    ('check-doc-refs CITE_RE misses the range citation', 'check-doc-refs.py',
     'CITE_RE = re.compile(r":\\d+(?:-\\d+)?(?:,\\d+(?:-\\d+)?)*$")\n',
     'CITE_RE = re.compile(r":\\d+(?:,\\d+)*$")\n', ST),
    # check-doc-refs: ".../ghc-9.12/... was read as a sibling path until the ../ test
    # was made to require the slash"
    ('check-doc-refs sibling-path test no longer requires the slash', 'check-doc-refs.py',
     '        elif token.startswith("../"):\n', '        elif token.startswith(".."):\n', ST),
    # check-doc-wrap: "disabling the fake-enumerator branch" (2026-08-14)
    ('check-doc-wrap fake-enumerator branch disabled', 'check-doc-wrap.py',
     "    fake = fake_markers(have)\n", "    fake = []\n", ST),
    # check-doc-wrap: "counting every differing paragraph as mid-edit"
    ('check-doc-wrap every differing paragraph counted as mid-edit', 'check-doc-wrap.py',
     '            if all(l in ok for l in h.split("\\n")):\n                loose += 1\n',
     '            if True:\n                loose += 1\n', ST),
    # check-doc-wrap: "folding BLOCKED back into exit 1"
    ('check-doc-wrap BLOCKED folded back into exit 1', 'check-doc-wrap.py',
     "    return 1 if bad else (2 if blocked else 0)\n", "    return 1 if bad or blocked else 0\n", ST),
    # check-doc-wrap: a document git does not have yet is judged by its own form.
    ('check-doc-wrap a new document at neither fixed point passed', 'check-doc-wrap.py',
     '                  f" --unwrap -i over it, whichever form it is to keep")\n            return 1\n',
     '                  f" --unwrap -i over it, whichever form it is to keep")\n            return 0\n', ST),
    ('check-doc-wrap a new document at a fixed point refused', 'check-doc-wrap.py',
     '              if t == have]\n',
     '              if False]\n', ST),
    # check-doc-wrap: a fence closed by one of another kind (check-doc-wrap-06)
    ('check-doc-wrap closes a block with a fence of any kind', 'common.py',
     '        elif (m and m.group(2)[0] == fence[0]\n',
     '        elif (m and True\n', 'cd {dir} && python3 check-doc-wrap.py --self-test'),
    # check-doc-wrap: "a repository tracking no Markdown reports BLOCKED rather than
    # 0 of 0 failed" (2026-08-28)
    ('check-doc-wrap repository tracking no Markdown reported as 0 of 0 failed', 'check-doc-wrap.py',
     '        print("BLOCKED: git tracks no Markdown file here, nothing checked")\n        return 2\n',
     '        pass\n', ST),
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
    # check-plan-citations: "disabling the PROSE-LINE refusal" (2026-08-14)
    ('check-plan-citations PROSE-LINE refusal disabled', 'check-plan-citations.py',
     '        if name.endswith(".md"):\n', '        if False:\n', ST),
    # check-plan-citations: "short-circuiting the publication test"
    ('check-plan-citations publication test short-circuited', 'check-plan-citations.py',
     "    return reachable_from(sha, PUBLISHED_REF)\n", "    return True\n", ST),
    # check-plan-citations: a stamp the formatter wrapped inside a blockquote
    # read as no stamp at all -- --restamp refused it and its orphan and
    # publication checks passed in silence (2026-09-04)
    ('check-plan-citations stamp regex misses a wrapped line', 'check-plan-citations.py',
     '    r"((?:`|\\*\\*)[\\s>]*\\()(\\d{4}-\\d{2}-\\d{2})(\\))")\n',
     '    r"((?:`|\\*\\*)\\s*\\()(\\d{4}-\\d{2}-\\d{2})(\\))")\n', ST),
    # check-plan-citations: "disabling the dirty-cited-file refusal"
    ('check-plan-citations dirty-cited-file refusal disabled', 'check-plan-citations.py',
     "        if dirty:\n", "        if False:\n", ST),
    # check-plan-citations: a failed git status read as clean (check-plan-citations-05)
    ('check-plan-citations reads a failed git status as clean', 'check-plan-citations.py',
     "        if p.returncode != 0:\n            print(f\"\\nnot restamping {doc}: git status could not be read\"\n",
     "        if False:\n            print(f\"\\nnot restamping {doc}: git status could not be read\"\n", ST),
    # check-plan-citations: "line-zero, backwards-range ... rows" (2026-08-28); the bare
    # condition occurs twice, so the anchor carries the print line
    ('check-plan-citations line zero and backwards range accepted', 'check-plan-citations.py',
     '        if lo < 1 or lo > hi or hi > len(lines):\n            print(f"FAIL {name}:{lo}-{hi} --- OUT-OF-RANGE "\n',
     '        if hi > len(lines):\n            print(f"FAIL {name}:{lo}-{hi} --- OUT-OF-RANGE "\n', ST),
    # check-plan-citations: "second-document row" -- until 2026-08-28 only the first
    # document was checked
    ('check-plan-citations only the first document checked', 'check-plan-citations.py',
     "    for doc in docs:\n        if len(docs) > 1:\n", "    for doc in docs[:1]:\n        if len(docs) > 1:\n", ST),
    # check-plan-citations: the foreign-permalink rows of 2026-10-19, one mutant a
    # verdict: no foreign URL checked, every commit taken for published, and each
    # of the link checks switched off
    ('check-plan-citations foreign permalinks unchecked', 'check-plan-citations.py',
     "    for clone, sha, path, lo, hi in foreign:\n",
     "    for clone, sha, path, lo, hi in []:\n", ST),
    ('check-plan-citations foreign publication short-circuited', 'check-plan-citations.py',
     "    return p.returncode == 0 and bool(p.stdout.strip())\n", "    return True\n", ST),
    ('check-plan-citations undefined label passes', 'check-plan-citations.py',
     "                if url is None:\n                    print(f\"FAIL [{shown}][{m.group(2)}] --- no definition\"\n",
     "                if False:\n                    print(f\"FAIL [{shown}][{m.group(2)}] --- no definition\"\n", ST),
    ('check-plan-citations link text never compared with its URL', 'check-plan-citations.py',
     "                if not url.endswith(shown) or not (\n", "                if False and not (\n", ST),
    ('check-plan-citations continuation never compared', 'check-plan-citations.py',
     "                    if last is not None and path != last:\n", "                    if False:\n", ST),
    ('check-plan-citations names beside a link never checked', 'check-plan-citations.py',
     "            if not names:\n                continue\n", "            if True:\n                continue\n", ST),
    # check-plan-citations-15: the cited file's own path read as a name of its lines
    ("check-plan-citations file's own name read as a name of the lines", 'check-plan-citations.py',
     '    return bool(code) and ("/" + path).endswith("/" + code)\n',
     '    return False\n', ST),
    ('check-plan-citations enclosing definitions and Notes ignored', 'check-plan-citations.py',
     "                             + enclosing(lines, lo))\n", "                             + [])\n", ST),
    # check-twin-sync: "a comparable() that returns the empty string for every script"
    # (2026-08-14)
    ('check-twin-sync comparable() returns the empty string for every script', 'check-twin-sync.py',
     '    return "\\n".join(l for l in out if l.strip())\n', '    return ""\n', ST),
    # check-twin-sync: "a shared shell script is compared whole" (2026-08-28 row)
    ('check-twin-sync non-Python file no longer compared whole', 'check-twin-sync.py',
     "    except SyntaxError:\n        return text\n", "    except SyntaxError:\n        return \"\"\n", ST),
    # check-twin-sync: the code case's mutation of comparable() writes nothing
    ('check-twin-sync code case mutates nothing', 'check-twin-sync.py',
     '            lines[at] += "  # mutated"\n', '            lines[at] += ""\n', ST),
    # check-twin-sync: "a TWIN_SKIP file is not" compared
    ('check-twin-sync TWIN_SKIP allowlist ignored', 'check-twin-sync.py',
     "                if os.path.isfile(p) and os.path.basename(p) not in TWIN_SKIP}\n",
     "                if os.path.isfile(p)}\n", ST),
    # heading-outline: "a closing fence is not a heading's text ... reported '## ```'"
    # (2026-08-28)
    ('heading-outline closing fence read as a Setext heading text', 'heading-outline.py',
     "            prev = ''      # neither a fence nor its contents underlines\n", "            prev = line\n", ST),
    # heading-outline: "the list item the same day, reported as '## - item'"
    ('heading-outline list item read as a Setext heading text', 'heading-outline.py',
     "                     and not LIST_ITEM.match(prev))\n", "                     and True)\n", ST),
    # heading-outline: the original fenced-`#`/`===` branch of the hand recipe
    ('heading-outline fenced lines read as headings', 'heading-outline.py',
     '        if kind:\n',
     '        if False:\n', ST),
    # heading-outline: a fence closed by one of another kind (heading-outline-03)
    ('heading-outline closes a block with a fence of any kind', 'common.py',
     '        elif (m and m.group(2)[0] == fence[0]\n',
     '        elif (m and True\n', 'cd {dir} && python3 heading-outline.py --self-test'),
    # heading-outline: any leading rule taken for frontmatter (heading-outline-04)
    ('heading-outline any leading rule read as frontmatter', 'heading-outline.py',
     "        if lines[i].strip() and not YAML_LINE.match(lines[i]):\n            return 0\n",
     "        if False:\n            return 0\n", ST),
    # check-doc-refs: a fence closed by one of another kind (check-doc-refs-05)
    ('check-doc-refs closes a block with a fence of any kind', 'common.py',
     '        elif (m and m.group(2)[0] == fence[0]\n',
     '        elif (m and True\n', 'cd {dir} && python3 check-doc-refs.py --self-test'),
    # check-doc-refs: SIBLING_ROOTS = [] degrades local drift to SKIP (check-doc-refs-06)
    ('check-doc-refs no sibling configured degrades local drift', 'check-doc-refs.py',
     "            if sib_active or not SIBLING_ROOTS:\n", "            if sib_active:\n", ST),
    # check-doc-refs: the self-test dispatched before the move to the root
    # (check-doc-refs-07); judged from the tool's own directory, where the
    # root's judge cannot tell. That defect's symptom IS exit 2, BLOCKED for
    # want of the siblings, which the runner reads as a judge that did not
    # run, so the judge says 2 is its catch
    ('check-doc-refs self-test dispatched before chdir_root', 'check-doc-refs.py',
     '    docs = common.chdir_root(args)\n    if "--self-test" in sys.argv[1:]:\n        return self_test()\n',
     '    if "--self-test" in sys.argv[1:]:\n        return self_test()\n    docs = common.chdir_root(args)\n', 'cd {dir} && python3 {file} --self-test; rc=$?; [ $rc -eq 2 ] && exit 1; exit $rc'),
    # check-doc-examples: the same (check-doc-examples-04)
    ('check-doc-examples self-test dispatched before chdir_root', 'check-doc-examples.py',
     '    docs = common.chdir_root(args)\n    if "--self-test" in sys.argv[1:]:\n        return self_test()\n',
     '    if "--self-test" in sys.argv[1:]:\n        return self_test()\n    docs = common.chdir_root(args)\n', 'cd {dir} && python3 {file} --self-test'),
    # check-plan-citations: CITE_RE misses json and sh (check-plan-citations-07)
    ('check-plan-citations CITE_RE misses json and sh', 'check-plan-citations.py',
     '    r"\\.(?:hs|ts|py|c|h|cabal|mjs|html|md|txt|yaml|yml|json|sh)|Makefile)"\n',
     '    r"\\.(?:hs|ts|py|c|h|cabal|mjs|html|md|txt|yaml|yml)|Makefile)"\n', ST),
    # bench-baseline: an unreadable baseline tracebacks at exit 1 again (bench-baseline-03)
    ('bench-baseline unreadable baseline tracebacks instead of exit 2', 'bench-baseline.py',
     '    except OSError as e:\n        usage_error(f"{baseline_path}: cannot be read ({e.strerror})")\n',
     '    except OSError as e:\n        raise\n', ST),
    # check-conv-bench-props: an unreadable collection tracebacks at exit 1 again
    # (check-conv-bench-props-02)
    # (the reader is common.py's since 2026-10-02, the judge still this tool)
    ('check-conv-bench-props unreadable collection tracebacks instead of exit 2', 'common.py',
     '    except (OSError, ValueError, LookupError, TypeError) as e:\n',
     '    except (OSError, ValueError, LookupError, TypeError) as e:\n        raise\n',
     'cd {dir} && python3 check-conv-bench-props.py --self-test'),
    # check-doc-wrap: indented code no longer exempt (check-doc-wrap-07)
    ('check-doc-wrap indented code block read as prose', 'check-doc-wrap.py',
     '        elif indented and (starts or code):\n',
     '        elif False:\n', ST),
    # check-doc-wrap: a fence line at any indentation opens or closes a block again
    # (check-doc-wrap-08)
    ('check-doc-wrap indented fence line read as a fence', 'common.py',
     'FENCE = re.compile(r"^( {0,3})(`{3,}|~{3,})(.*)$")\n',
     'FENCE = re.compile(r"^(\\s*)(`{3,}|~{3,})(.*)$")\n', 'cd {dir} && python3 check-doc-wrap.py --self-test'),
    # bang-lazy-check: a same-named binding in another module's dump stands in
    # for the candidate's own (bang-lazy-check-02)
    ('bang-lazy-check verdict from a foreign module of the same name', 'bang-lazy-check.py',
     "    quals = [q for q in entry if q.rsplit('.', 2)[-2:-1] == [stem]]\n    if not quals:\n",
     "    quals = [q for q in entry if q.rsplit('.', 2)[-2:-1] == [stem]] or list(entry)\n    if not entry:\n", SELFTEST),
    # bang-lazy-check: a ROOT that is not there is opened as a file, a traceback
    # at 1 (bang-lazy-check-03)
    ('bang-lazy-check missing ROOT no longer blocks', 'bang-lazy-check.py',
     "    if missing:\n        # Opened as a file later", "    if False:\n        # Opened as a file later", SELFTEST),
    # bang-lazy-check: an unrecognised flag read as a ROOT (bang-lazy-check-03)
    ('bang-lazy-check unrecognised flag read as a ROOT', 'bang-lazy-check.py',
     "    if not args or unknown:\n", "    if not args:\n", SELFTEST),
    # bench-baseline: a regression missing a field tracebacks at 1 again
    # (bench-baseline-04)
    ('bench-baseline malformed regression tracebacks instead of exit 2', 'common.py',
     '        raise CriterionError(f"{path}: the regressions of {name} lack {e}")\n', "        raise\n",
     'cd {dir} && python3 bench-baseline.py --self-test'),
    # check-conv-bench-props: a missing benchmark exits 1 again
    # (check-conv-bench-props-03)
    ('check-conv-bench-props missing benchmark exits 1', 'check-conv-bench-props.py',
     '            usage_error(f"benchmark missing from the JSON (not a full run?): {k}")\n',
     '            sys.exit(f"benchmark missing from the JSON (not a full run?): {k}")\n', ST),
    # check-conv-bench-props: a regression missing a field tracebacks at 1 again
    # (check-conv-bench-props-04)
    ('check-conv-bench-props malformed regression tracebacks instead of exit 2', 'common.py',
     '        raise CriterionError(f"{path}: the regressions of {name} lack {e}")\n', "        raise\n",
     'cd {dir} && python3 check-conv-bench-props.py --self-test'),
    # check-doc-refs: a fence line at any indentation opens a block again
    # (check-doc-refs-08)
    ('check-doc-refs indented fence line read as a fence', 'common.py',
     'FENCE = re.compile(r"^( {0,3})(`{3,}|~{3,})(.*)$")\n',
     'FENCE = re.compile(r"^(\\s*)(`{3,}|~{3,})(.*)$")\n', 'cd {dir} && python3 check-doc-refs.py --self-test'),
    # check-doc-refs: a ../ path into an unconfigured checkout resolved against
    # the mount again (check-doc-refs-09)
    ('check-doc-refs unconfigured checkout resolved against the mount', 'check-doc-refs.py',
     '            if "/".join(token.split("/")[:2]) not in SIBLING_ROOTS:\n                out["external"].append(token)\n            elif not sib_active:\n',
     '            if not sib_active:\n', ST),
    # check-plan-citations: the PUBLISHED_REF stop exits from inside check()
    # again (check-plan-citations-09)
    ('check-plan-citations PUBLISHED_REF stop exits the whole run', 'check-plan-citations.py',
     "            blocked = True\n            continue\n", "            sys.exit(2)\n", ST),
    # heading-outline: a fence line at any indentation opens a block again
    # (heading-outline-05)
    ('heading-outline indented fence line read as a fence', 'common.py',
     'FENCE = re.compile(r"^( {0,3})(`{3,}|~{3,})(.*)$")\n',
     'FENCE = re.compile(r"^(\\s*)(`{3,}|~{3,})(.*)$")\n', 'cd {dir} && python3 heading-outline.py --self-test'),
    # check-doc-examples: the from-the-root control may agree at exit 2 again
    # (check-doc-examples-05). Judged with README.md aside, where the self-test
    # must FAIL: the judge is that failure, so it passes on the guarded checker
    # and fails on the mutant, which reports PASS over two runs that did not
    # happen. A judge whose setup fails exits 0 and the mutant survives, loudly.
    ('check-doc-examples control passes over two runs that did not happen', 'check-doc-examples.py',
     "    if here.returncode == 2:\n        ok = False\n", "    if False:\n        ok = False\n",
     'cd {dir} && mv ../README.md ../README.md.aside || exit 0; python3 {file} --self-test; rc=$?; '
     'mv ../README.md.aside ../README.md; test $rc -ne 0'),
    # ab-time, cachegrind-per-call, core-diff and ticky-diff (2026-09-29):
    # each watched failing its self-test before it was written down here.
    ('ticky-diff local closure unique no longer normalised', 'ticky-diff.py',
     "    name = re.sub(r'_sat_s[0-9A-Za-z]+', '_sat', name)\n", '', ST),
    ('ticky-diff file without the table read as an empty table', 'ticky-diff.py',
     '    return out if seen else None\n', '    return out\n', ST),
    # ticky-diff-01 (2026-10-02): a row with no non-void argument has no kinds word.
    ('ticky-diff kinds word dropped from a row that has none', 'ticky-diff.py',
     '            if int(m.group(4)) > 0:\n', '            if True:\n', ST),
    # ticky-diff-02 (2026-10-07): an exported closure's unique, `{(x) v rW}`.
    ('ticky-diff exported closure unique kept', 'ticky-diff.py',
     "    name = re.sub(r'\\{(?:\\([^)]*\\) )?v\\b[^}]*\\}', '', name).strip()\n",
     "    name = re.sub(r'\\{v[^}]*\\}', '', name).strip()\n", ST),
    ('core-diff numeric suffix of a binding kept', 'core-diff.py',
     '    return re.sub(r"([A-Za-z_$\'])[0-9]+\\b", r\'\\1\', tok)\n', '    return tok\n', ST),
    ('core-diff directory without dumps accepted', 'core-diff.py',
     '        if not t:\n', '        if not t and False:\n', ST),
    ('cachegrind-per-call last-level misses weighted as L1', 'cachegrind-per-call.py',
     "           'ILmr': 100, 'DLmr': 100, 'DLmw': 100}\n", "           'ILmr': 10, 'DLmr': 100, 'DLmw': 100}\n", ST),
    ('cachegrind-per-call summary shorter than its events accepted', 'cachegrind-per-call.py',
     '    if events is None or summary is None or len(events) != len(summary):\n', '    if events is None or summary is None:\n', ST),
    ('ab-time mean in place of the median', 'ab-time.py',
     '        out.append((statistics.median(ratios), min(ratios), max(ratios),\n',
     '        out.append((statistics.mean(ratios), min(ratios), max(ratios),\n', ST),
    # ab-time's rotation, pinning and allocation, and perf-per-call
    # (2026-10-06): each watched failing its self-test before it was
    # written down here.
    ('ab-time order not rotated', 'ab-time.py',
     '            j = (i + r) % len(bins)\n',
     '            j = i\n', ST),
    ('ab-time allocation not asked for', 'ab-time.py',
     "            + [binary, '-m', 'glob', name, '--regress', 'allocated:iters',\n",
     "            + [binary, '-m', 'glob', name,\n", ST),
    ('ab-time --cpu not pinned', 'ab-time.py',
     "    return ((['taskset', '-c', cpu] if cpu is not None else [])\n",
     '    return (([] if cpu is not None else [])\n', ST),
    ('perf-per-call setup not cancelled', 'perf-per-call.py',
     '    return {e: (c2[e] - c1[e]) / n for e in EVENTS}\n',
     '    return {e: c2[e] / n for e in EVENTS}\n', ST),
    ('perf-per-call missing count accepted', 'perf-per-call.py',
     '    if missing:\n',
     '    if False:\n', ST),
    ('perf-per-call builds not rotated', 'perf-per-call.py',
     '            j = (i + r) % len(bins)\n',
     '            j = i\n', ST),
    ('perf-per-call counts not swapped', 'perf-per-call.py',
     '            for k in ((1, 2) if r % 2 == 0 else (2, 1)):\n',
     '            for k in (1, 2):\n', ST),
    ('perf-per-call --cpu not pinned', 'perf-per-call.py',
     "    return ((['taskset', '-c', cpu] if cpu is not None else []) + PERF\n",
     '    return (([] if cpu is not None else []) + PERF\n', ST),
    ('perf-per-call mean in place of the median', 'perf-per-call.py',
     '            mid = statistics.median(xs)\n',
     '            mid = statistics.mean(xs)\n', ST),
    # perf-per-call-01 (2026-10-11): a fixed amount some processes add
    # lifted the instructions' median.
    ('perf-per-call instructions from the median', 'perf-per-call.py',
     "        if e == 'instructions':\n",
     '        if False:\n', ST),
    # perf-per-call-02 (2026-10-11): every run at one count carrying it,
    # the amount lifted the lowest count, and the spread went unreported.
    ('perf-per-call spread of the differences unreported', 'perf-per-call.py',
     '        if hi - lo > SPAN * abs(mid):\n',
     '        if False:\n', ST),
    # GHCRTS=-V0 on every measured run (2026-10-11), the caller's GHCRTS
    # kept ahead of it.
    ('perf-per-call run without GHCRTS=-V0', 'perf-per-call.py',
     '                       text=True, env=measured_env())\n',
     '                       text=True)\n', ST),
    ('perf-per-call -V0 ahead of the caller\'s GHCRTS', 'perf-per-call.py',
     "                GHCRTS=(os.environ.get('GHCRTS', '') + ' -V0').strip())\n",
     "                GHCRTS=('-V0 ' + os.environ.get('GHCRTS', '')).strip())\n", ST),
    ('ab-time run without GHCRTS=-V0', 'ab-time.py',
     '                           env=measured_env())\n',
     '                           )\n', ST),
    ('ab-time -V0 ahead of the caller\'s GHCRTS', 'ab-time.py',
     "                GHCRTS=(os.environ.get('GHCRTS', '') + ' -V0').strip())\n",
     "                GHCRTS=('-V0 ' + os.environ.get('GHCRTS', '')).strip())\n", ST),
    ('cachegrind-per-call run without GHCRTS=-V0', 'cachegrind-per-call.py',
     '                       text=True, env=measured_env())\n',
     '                       text=True)\n', ST),
    ('cachegrind-per-call -V0 ahead of the caller\'s GHCRTS', 'cachegrind-per-call.py',
     "                GHCRTS=(os.environ.get('GHCRTS', '') + ' -V0').strip())\n",
     "                GHCRTS=('-V0 ' + os.environ.get('GHCRTS', '')).strip())\n", ST),
    # check-plan-citations-10 (2026-10-02): a link into another repository
    # resolved here and failed.
    ('check-plan-citations foreign permalink checked as this repository\'s', 'check-plan-citations.py',
     '        if own is not None and slug != own:\n', '        if False:\n', ST),
    # check-doc-refs-10 (2026-10-02): cabal's own `all` read as a stanza.
    ('check-doc-refs cabal all read as a stanza name', 'check-doc-refs.py',
     '        if name in stanzas or name == "all":\n', '        if name in stanzas:\n', ST),
    # check-doc-refs: the link and Contents rows of 2026-10-19, each mutant
    # breaking one verdict of anchors_self_test
    ('check-doc-refs line anchor compared with the headings', 'check-doc-refs.py',
     '    line = anchor is not None and re.fullmatch(r"L\\d+(?:-L?\\d+)?", anchor)\n',
     '    line = False\n', ST),
    ('check-doc-refs missing file passes', 'check-doc-refs.py',
     '            if anchors is None:\n',
     '            if False:\n', ST),
    ('check-doc-refs anchor never compared with the headings', 'check-doc-refs.py',
     '                    and anchor not in anchors:\n',
     '                    and False:\n', ST),
    ('check-doc-refs repeated anchor not numbered', 'check-doc-refs.py',
     '        while anchor in seen:\n',
     '        while False:\n', ST),
    ('check-doc-refs link read inside a code span', 'check-doc-refs.py',
     '        for m in LINK_RE.finditer(CODE_SPAN_RE.sub("", line)):\n',
     '        for m in LINK_RE.finditer(line):\n', ST),
    ('check-doc-refs link read inside fenced code', 'check-doc-refs.py',
     '        if kind is not None:\n            continue\n',
     '        if False:\n            continue\n', ST),
    ('check-doc-refs Contents order unchecked', 'check-doc-refs.py',
     '            if k < last:\n',
     '            if False:\n', ST),
    ('check-doc-refs heading missing from Contents passes', 'check-doc-refs.py',
     '            if line >= end and lvl in levels and k not in listed:\n',
     '            if False:\n', ST),
    ('check-doc-refs pinned link read in the working tree', 'check-doc-refs.py',
     '            return ref, "/".join(parts), anchor\n',
     '            return None, "/".join(parts), anchor\n', ST),
    ('check-doc-refs closing hashes kept in a heading', 'check-doc-refs.py',
     'HEADING_RE = re.compile(r" {0,3}(#{1,6})(?:[ \\t]+(.*?))?(?:[ \\t]+#+)?[ \\t]*$")\n',
     'HEADING_RE = re.compile(r" {0,3}(#{1,6})(?:[ \\t]+(.*?))?[ \\t]*$")\n', ST),
    ('check-doc-refs footnote read as a link definition', 'check-doc-refs.py',
     'LINK_RE = re.compile(r"\\]\\(\\s*<?([^\\s)>]+)|^ {0,3}\\[(?!\\^)[^\\]]+\\]:\\s*<?([^\\s>]+)")\n',
     'LINK_RE = re.compile(r"\\]\\(\\s*<?([^\\s)>]+)|^ {0,3}\\[[^\\]]+\\]:\\s*<?([^\\s>]+)")\n', ST),
    ("check-doc-refs another repository's GitHub link read as this one's", 'check-doc-refs.py',
     '        if anchor is None or line or m.group(1).lower() != own:\n',
     '        if anchor is None or line:\n', ST),
    # check-doc-wrap-09 (2026-10-02): a continuation line read for an
    # enumerator.
    ('check-doc-wrap continuation line read for an enumerator', 'check-doc-wrap.py',
     '        elif starts and FAKE_MARKER.match(l) and not REAL_MARKER.match(l):\n',
     '        elif FAKE_MARKER.match(l) and not REAL_MARKER.match(l):\n', ST),
    # check-twin-sync-04 (2026-10-02): a twin sharing no tool passed.
    ('check-twin-sync twin sharing no tool passes', 'check-twin-sync.py',
     '    if not drifted and not same:\n', '    if False:\n', ST),
    # bench-baseline-05, -06, check-conv-bench-props-05 and ab-time-01
    # (2026-10-02): a null estimate or a NaN tolerance taken as a number.
    ('common finite() accepts a null', 'common.py',
     '    return (isinstance(v, (int, float)) and not isinstance(v, bool)\n'
     '            and math.isfinite(v))\n', '    return True\n',
     'cd {dir} && python3 bench-baseline.py --self-test'),
    ('common estimate() returns what it finds unchecked', 'common.py',
     '    if not finite(v):\n', '    if False:\n',
     'cd {dir} && python3 check-conv-bench-props.py --self-test'),
    ('ab-time slope read past the shared reader', 'ab-time.py',
     "    t = common.slope(path, name, regs['time'])\n",
     "    t = regs['time']['regCoeffs']['iters']['estPoint']\n", ST),
    ('bench-baseline tolerance range unchecked', 'bench-baseline.py',
     '    if not common.finite(v) or v < 0:\n', '    if False:\n', ST),
    # core-diff-01 (2026-10-02): a --module matching nothing passed.
    ('core-diff --module matching no module accepted', 'core-diff.py',
     '    if sub is not None and not any(sub in k for t in trees for k in t):\n',
     '    if False:\n', ST),
    # check-doc-examples-07 (2026-10-02): a quotation of another repository's
    # code read as this one's, by each path a permalink reaches it.
    ('check-doc-examples quotation never detected', 'check-doc-examples.py',
     '                cur, src = [], quoted_from(prev, defs)\n',
     '                cur, src = [], None\n', ST),
    ('check-doc-examples permalink into this repository taken for a quotation', 'check-doc-examples.py',
     '                                capture_output=True).returncode != 0:\n',
     '                                capture_output=True).returncode != 0 or True:\n', ST),
    ('check-doc-examples permalink through a reference definition missed', 'check-doc-examples.py',
     '             if k in defs]\n', '             if False]\n', ST),
    ('check-doc-examples inline permalink missed', 'check-doc-examples.py',
     '    urls = [m.group(0) for m in PERMALINK_RE.finditer(line)]\n', '    urls = []\n', ST),
    # pragma-calls (2026-09-30): each watched failing its self-test before
    # it was written down here.
    ('pragma-calls specialisation prefix no longer normalised', 'pragma-calls.py',
     "    return re.sub(r'[0-9]+$', '', tok[m.end():]) if m else tok\n",
     '    return tok\n', ST),
    ('pragma-calls tree without dumps accepted', 'pragma-calls.py',
     '        if not t:\n', '        if not t and False:\n', ST),
    # pragma-calls-01 and -02 (2026-10-02): a cache returned without its
    # signature checked, and an operator counted in its pragma's parentheses.
    ('pragma-calls cache returned without its signature checked', 'pragma-calls.py',
     '        if isinstance(got, tuple) and len(got) == 2 and got[0] == key:\n',
     '        if isinstance(got, tuple) and len(got) == 2:\n', ST),
    ('pragma-calls operator target kept in its parentheses', 'pragma-calls.py',
     "    return n[1:-1] if n.startswith('(') and n.endswith(')') else n\n",
     "    return n\n", ST),
    # pragma-calls-09 (2026-10-14): --inline reading a calling module's
    # aliases.
    ('pragma-calls --inline blind to an alias', 'pragma-calls.py',
     "                if m and t not in foreign and refers(km, m.group(1)[:-1]):\n",
     "                if m and t not in foreign and m.group(1)[:-1] == mod:\n", ST),
    # core-diff-02, -03 and pragma-calls-03, -04 (2026-10-05): the dump
    # keying and selection now shared in dumps.py, judged by the self-tests
    # of the tools importing it, and the identity verdict's two digests.
    ('core-diff size comments ignored', 'core-diff.py',
     '    if any(RHS.match(line) for line in lines):\n', '    if False:\n', ST),
    ('dumps whole path kept as the key', 'dumps.py',
     "    rel = os.path.relpath(path, root).replace(os.sep, '/')\n", '    rel = path\n',
     'cd {dir} && python3 core-diff.py --self-test'),
    ('dumps literal-blind digest the exact one', 'dumps.py',
     "    blind = LITERAL.sub('N#', exact)\n", '    blind = exact\n',
     'cd {dir} && python3 core-diff.py --self-test'),
    ('dumps timestamps kept in the digests', 'dumps.py',
     "    exact = TIMESTAMP.sub('', text)\n", '    exact = text\n',
     'cd {dir} && python3 core-diff.py --self-test'),
    ('dumps stats file read as a dump', 'dumps.py',
     "            if f.endswith(suffix) or f.endswith(suffix + '.gz'):\n",
     '            if suffix in f:\n', 'cd {dir} && python3 pragma-calls.py --self-test'),
    ('pragma-calls cache keying left out of its signature', 'pragma-calls.py',
     '    return TOK.pattern, KEYS, NORMALISED, files\n',
     '    return TOK.pattern, NORMALISED, files\n', ST),
    ('pragma-calls cache normalisation left out of its signature',
     'pragma-calls.py',
     '    return TOK.pattern, KEYS, NORMALISED, files\n',
     '    return TOK.pattern, KEYS, files\n', ST),
    # rules-diff, ctime-diff, one-shot, rewrite-check and src-attrib
    # (2026-10-05): each watched failing its self-test before it was written
    # down here.
    ('rules-diff entry name cut at its first space', 'rules-diff.py',
     "ENTRY = re.compile(r'^\\s+(\\d+) (\\S.*?)\\s*$')\n",
     "ENTRY = re.compile(r'^\\s+(\\d+) (\\S+)')\n", ST),
    ('rules-diff FloatOut statistics read as ticks', 'rules-diff.py',
     "    start = txt.find('= ' + GRAND + ' =')\n",
     "    start = 0 if GRAND in txt else -1\n", ST),
    ('rules-diff same-named entries not summed', 'rules-diff.py',
     '            out[kind][m.group(2)] += int(m.group(1))\n',
     '            out[kind][m.group(2)] = int(m.group(1))\n', ST),
    ('rules-diff tree without stats dumps accepted', 'rules-diff.py',
     '        if not t:\n', '        if not t and False:\n', ST),
    ('rules-diff fusion rules unmarked', 'rules-diff.py',
     '    return rule in FUSION_NAMES or bool(VECTOR_FUSION.match(rule))\n',
     '    return False\n', ST),
    ('rules-diff any vector rule read as fusion', 'rules-diff.py',
     "VECTOR_FUSION = re.compile(r'^\\S+/\\S+ \\[(?:Vector|New)\\]$')\n",
     "VECTOR_FUSION = re.compile(r'\\[(?:Vector|New)\\]')\n", ST),
    ('rules-diff --unfolding matching nothing accepted', 'rules-diff.py',
     '        if not any(n in x for t in trees for k in keys\n',
     '        if False and not any(n in x for t in trees for k in keys\n', ST),
    ('ctime-diff .dyn timings kept apart', 'ctime-diff.py',
     "        if key.endswith('.dyn'):\n", '        if False:\n', ST),
    ('ctime-diff a module whose Core differs taken for a control', 'ctime-diff.py',
     "        group = ('controls' if v in ('same', 'literals')\n",
     "        group = ('controls' if v in ('same', 'literals', 'differs')\n", ST),
    ('ctime-diff tree without Core dumps accepted', 'ctime-diff.py',
     '        if not c:\n', '        if not c and False:\n', ST),
    ('ctime-diff range read over every control', 'ctime-diff.py',
     "        if group == 'controls' and ma >= min_ms:\n",
     "        if group == 'controls':\n", ST),
    ('ctime-diff a module with no pass timed left out unnamed', 'ctime-diff.py',
     '        out[key]  # a module with no pass timed stays, [0.0, 0]\n',
     '        pass\n', ST),
    ('one-shot link invocation not told from the compile', 'one-shot.py',
     "        if '--make' in args and '-o' not in args and module in names:\n",
     "        if '--make' in args and module in names:\n", ST),
    ("one-shot module's own outputs mirrored", 'one-shot.py',
     '            if r not in own:\n', '            if True:\n', ST),
    ('one-shot dump directory not redirected', 'one-shot.py',
     "        args[args.index('-dumpdir') + 1] = dump\n", '        pass\n', ST),
    ('one-shot OUTDIR another program made emptied', 'one-shot.py',
     '        if not os.path.exists(os.path.join(outdir, MARKER)):\n',
     '        if False:\n', ST),
    ('one-shot flag value taken for a target', 'one-shot.py',
     "        if a.startswith('-') or (i and args[i - 1] in ARG_FLAGS):\n",
     "        if a.startswith('-'):\n", ST),
    ('rewrite-check every changed patch read as context-only', 'rewrite-check.py',
     '        elif lo == ln:\n', '        elif True:\n', ST),
    ('rewrite-check dropped commit not judged', 'rewrite-check.py',
     '        if oi[o][0].startswith(FOLDED) or o in exp:\n',
     '        if True:\n', ST),
    ('rewrite-check tree difference not checked', 'rewrite-check.py',
     "            find(f'tree differs: {p}')\n", '            pass\n', ST),
    ('rewrite-check expectation that missed accepted', 'rewrite-check.py',
     '            if po == pn and lo == ln and mo == mn:\n',
     '            if False:\n', ST),
    # The move pairing (2026-10-06, rewrite-check-01), written down before
    # its replay watched the self-test's reorder scenario catch it.
    ('rewrite-check moved commit not paired', 'rewrite-check.py',
     '        if same:\n', '        if False:\n', ST),
    ('rewrite-check message change not reported', 'rewrite-check.py',
     '        if mo != mn and so == sn:\n', '        if False:\n', ST),
    # rewrite-check-02: an --expect may name either commit of a pair.
    ('rewrite-check an --expect naming the new commit not taken for its pair',
     'rewrite-check.py',
     '        if o in exp or n in exp:\n', '        if o in exp:\n', ST),
    # rewrite-check-03: a change of whitespace alone is a changed patch. The
    # changed lines decide it, patch-id deciding only unchanged against
    # context-only.
    ('rewrite-check whitespace stripped before the changed lines are compared',
     'rewrite-check.py',
     "                                         and prev[:1] in ('+', '-')):\n"
     "            lines[(cur, line)] += 1\n",
     "                                         and prev[:1] in ('+', '-')):\n"
     "            lines[(cur, ''.join(line.split()))] += 1\n", ST),
    # rewrite-fold-01: the self-test folds two substitutions of one file.
    ('rewrite-fold a second substitution of a file restarts from the old text', 'rewrite-fold.py',
     '                s = s.replace(o, n)\n',
     '                s = old.replace(o, n)\n', ST),
    ('rewrite-fold an OLD found no times applied anyway', 'rewrite-fold.py',
     '                if k != 1:\n',
     '                if k > 1:\n', ST),
    ('rewrite-fold a NEW already present accepted', 'rewrite-fold.py',
     '                if n and n not in o and n in old:\n',
     '                if False:\n', ST),
    ('rewrite-fold a reword ignored', 'rewrite-fold.py',
     '            if c in rw:\n',
     '            if False:\n', ST),
    ('rewrite-fold the author not kept', 'rewrite-fold.py',
     '            parent = git(repo, *args, stdin=msg, env=author).strip()\n',
     '            parent = git(repo, *args, stdin=msg).strip()\n', ST),
    ('rewrite-fold a BASE that is not the fork point accepted', 'rewrite-fold.py',
     "    if resolve(repo, chain[0] + '^') != base:\n",
     '    if False:\n', ST),
    ('rewrite-fold a merge in the range accepted', 'rewrite-fold.py',
     "    if git(repo, 'rev-list', '--merges', base + '..' + tip).strip():\n",
     '    if False:\n', ST),
    ('rewrite-fold a dry run that writes', 'rewrite-fold.py',
     '        if dry:\n',
     '        if False:\n', ST),
    # The END of a substitution (2026-10-13), watched failing its self-test
    # before it was written down here.
    ('rewrite-fold a substitution applied past its END', 'rewrite-fold.py',
     '               if j <= i < e]\n',
     '               if j <= i]\n', ST),
    ('rewrite-fold an END before its COMMIT accepted', 'rewrite-fold.py',
     '            if ce not in pos or pos[ce] <= pos[cc]:\n',
     '            if ce not in pos:\n', ST),
    ('rewrite-fold the printed check omits the commits it changed', 'rewrite-fold.py',
     "            cmd += ['--expect', c]\n",
     '            pass\n', ST),
    ('rewrite-fold the printed check omits the paths changed at the tip', 'rewrite-fold.py',
     "        cmd += ['--allow-tree', p]\n",
     '        pass\n', ST),
    # rewrite-fold-07: a SPEC whose code raises is refused, not a traceback.
    ('rewrite-fold a SPEC whose code raises crashes the fold', 'rewrite-fold.py',
     '    except Exception as e:\n',
     '    except (OSError, SyntaxError, UnicodeDecodeError) as e:\n', ST),
    ('src-attrib note text counted as code', 'src-attrib.py',
     "            body = s.strip() if with_notes else NOTE_TEXT.sub('', s).strip()\n",
     '            body = s.strip()\n', ST),
    ('src-attrib block comment lines taken for definitions', 'src-attrib.py',
     "            depth = max(0, depth + line.count('{-') - line.count('-}'))\n",
     '            depth = 0\n', ST),
    ('src-attrib infix definition credited to its left operand', 'src-attrib.py',
     '                elif infix and infix.group(1) not in RESERVED:\n',
     '                elif False:\n', ST),
    ('src-attrib dump without notes accepted', 'src-attrib.py',
     '    if total is None:\n', '    if False:\n', ST),
    ('src-attrib mid-line note opens a scope', 'src-attrib.py',
     '                if SCOPE.search(before):\n', '                if True:\n', ST),
    # The survey's reachability guard removed: the ninth saved site's table
    # word counts as a self-loop again. Over a site saved for this mutant and
    # no case, the first site's body being one the zero tell refuses too.
    ('loop-offsets survey counts a data word as a loop again', 'loop-offsets.py',
     '        if not reaches(insns, k, n):\n'
     '            continue\n',
     '',
     offsets_listing('run33-gheadexit-0x4a52b6.dis', PHANTOM8_LISTING, '0 self-loops of at most')),
    # Four table tells dropped at once: they coincide on the second site, so
    # none alone is caught there, and the mutants below prove three of them
    # alone.
    ('loop-offsets survey counts a swallowed jump as a loop again', 'loop-offsets.py',
     "        if any(i[3] == '(bad)' for i in insns[k:n + 1]):\n"
     '            continue\n'
     '        # Nor does it carry a run of zero bytes, or an instruction of two:\n'
     '        # such a body IS a table, the third site in `reaches`.\n'
     '        if zero_run(insns, k, n):\n'
     '            continue\n'
     '        # Nor a stray REX prefix, `rex.*` in the mnemonic column: the sweep\n'
     '        # entered an instruction mid-way, a fifth shape, the sixth site in\n'
     '        # defects.py (2026-09-18), which carries the totals it moves.\n'
     "        if any(i[3].startswith('rex.') for i in insns[k:n + 1]):\n"
     '            continue\n'
     "        # Nor an x87 instruction, a mnemonic beginning `f`: GHC's x86-64\n"
     '        # code generator does floating point in SSE2, so the sweep decoded\n'
     "        # one out of step -- Run 41's phantom astride, a `jmp` rel32's own\n"
     '        # bytes `de e9 70 fc` read as `fsubrp` and `jo -4` back to it, the\n'
     '        # thirteenth site in defects.py (2026-09-26).\n'
     "        if any(i[3].startswith('f') for i in insns[k:n + 1]):\n"
     '            continue\n',
     '',
     offsets('survey-counts-a-swallowed-jump-as-a-loop', 'still straddling   : 0')),
    # One tell each, dropped or narrowed, over the site that tell alone
    # refuses.
    ('loop-offsets survey counts a table body as a loop again', 'loop-offsets.py',
     '        if zero_run(insns, k, n):\n'
     '            continue\n',
     '',
     offsets('survey-counts-a-table-body-as-a-loop', 'still straddling   : 0')),
    ('loop-offsets survey counts a nop pad and its table word as a loop again', 'loop-offsets.py',
     "        if PAD.match(insns[k][3] + ' ' + insns[k][4]):\n"
     '            continue\n',
     '',
     offsets('survey-counts-a-nop-pad-table-word-as-a-loop', '0 self-loops of at most')),
    ('loop-offsets survey counts a return-address word as a loop again', 'loop-offsets.py',
     "        if any(i[3].startswith('rex.') for i in insns[k:n + 1]):\n"
     '            continue\n',
     '',
     offsets('survey-counts-a-return-address-word-as-a-loop', '0 self-loops of at most')),
    ('loop-offsets survey counts an x87 decode of a jump as a loop again', 'loop-offsets.py',
     "        if any(i[3].startswith('f') for i in insns[k:n + 1]):\n"
     '            continue\n',
     '',
     offsets('survey-counts-an-x87-decode-of-a-jump-as-a-loop', '0 self-loops of at most')),
    ('loop-offsets survey counts a high-byte register decode as a loop again', 'loop-offsets.py',
     '        if any(HIGHBYTE.search(i[4]) for i in insns[k:n + 1]):\n'
     '            continue\n',
     '',
     offsets('survey-counts-a-high-byte-register-decode-as-a-loop', '0 self-loops of at most')),
    ('loop-offsets survey counts a table word pair as a loop again', 'loop-offsets.py',
     "    return any(i[2] == '0000' for i in insns[k:n + 1])\n",
     '    return False\n',
     offsets('survey-counts-a-table-word-pair-as-a-loop', '0 self-loops of at most')),
    ('loop-offsets survey counts a two-byte pad and its table word as a loop again', 'loop-offsets.py',
     "        if PAD.match(insns[k][3] + ' ' + insns[k][4]):\n"
     '            continue\n',
     "        if insns[k][3].startswith('nop'):\n"
     '            continue\n',
     offsets('survey-counts-a-two-byte-pad-and-its-table-word-as-a-loop', '0 self-loops of at most')),
    # parse's continuation line dropped, the flow test answering yes to
    # everything, and its blanket form of 2026-09-04 back.
    ('loop-offsets the survey drops a body with an eight-byte instruction again', 'loop-offsets.py',
     '            m = CONT.match(line)\n'
     '            if m and insns:\n',
     '            m = None\n'
     '            if m and insns:\n',
     offsets('survey-drops-a-body-with-an-eight-byte-instruction', '1 self-loops of at most')),
    ('loop-offsets the survey counts a branch into an exit block as a loop again', 'loop-offsets.py',
     '    return live[n - k]\n',
     '    return True\n',
     offsets('survey-counts-a-branch-into-an-exit-block-as-a-loop', '0 self-loops of at most')),
    ('loop-offsets the survey refuses a loop closed by a jmp again', 'loop-offsets.py',
     '    return live[n - k]\n',
     '    return live[n - k] and not any(UNCOND.match(i[3]) for i in insns[k:n + 1])\n',
     offsets('survey-keeps-a-loop-closed-by-a-jmp', '1 self-loops of at most')),
    # The exit-span count's two halves, each broken on its own.
    ('loop-offsets the survey reads every exit span as in line', 'loop-offsets.py',
     "                   and f['mod'] + spans[f['start']] > LINE),\n",
     '                   and False),\n',
     offsets('survey-counts-no-exit-span', 'exit spans astride : 1')),
    ('loop-offsets the survey reads an exit span past a jmp back edge', 'loop-offsets.py',
     '        if UNCOND.match(insns[n][3]):\n'
     '            continue\n',
     '',
     offsets('survey-counts-no-exit-span', 'exit spans astride : 1',
             'exit span 57 B')),
    # --delta's three readings, each broken on its own.
    ('loop-offsets --delta reports every offset preserved whatever moved', 'loop-offsets.py',
     '        if oo == nn:\n'
     '            preserved += 1\n',
     '        if True:\n'
     '            preserved += 1\n',
     offsets('delta-reads-moved-offsets-and-displacements', 'offsets MOVED')),
    ('loop-offsets --delta selects on the OLD side alone again', 'loop-offsets.py',
     '    keys = [k for k in og\n'
     '            if len(og[k]) >= min_copies or len(ng.get(k, ())) >= min_copies]\n',
     '    keys = [k for k in og if len(og[k]) >= min_copies]\n',
     offsets('delta-sees-a-group-that-grows-past-the-threshold', '1 -> 2 copies')),
    ('loop-offsets --delta reads the libraries into the tracked groups again', 'loop-offsets.py',
     "            if want in (f['sym'] or ''):\n",
     '            if True:\n',
     offsets('delta-leaves-the-library-groups-to-library', '1 group(s) read')),
    # spec-audit (2026-10-07): each watched failing its self-test before it
    # was written down here.
    ('spec-audit dictionary in head position read as handed over', 'spec-audit.py',
     '    if not names or names[-1] in NOT_CALLEE:\n        return None\n',
     "    if not names:\n        return '?'\n", ST),
    ('spec-audit versioned package qualifier left as the callee', 'spec-audit.py',
     'QUAL = r"(?:[\\w.\'-]+:)?(?:[A-Z][\\w\']*\\.)*"\n',
     'QUAL = r"(?:[\\w\'-]+:)?(?:[A-Z][\\w\']*\\.)*"\n', ST),
    ('spec-audit dictionary opening its line given no callee', 'spec-audit.py',
     '    if not prefix.strip():\n', '    if False:\n', ST),
    ('spec-audit instance method read as a dictionary', 'spec-audit.py',
     "                    or line[m.end():].startswith('$c')):\n",
     '                    or False):\n', ST),
    ('spec-audit --ignore not applied', 'spec-audit.py',
     '            if any(re.search(r, m.group(0)) for r in ignore):\n',
     '            if False:\n', ST),
    ('spec-audit --module matching nothing accepted', 'spec-audit.py',
     '    if not read:\n', '    if False:\n', ST),
    # pragma-calls and core-diff (2026-10-10): the branches of
    # pragma-calls-05 and -06 and core-diff-04, each watched failing its
    # self-test before it was written down here.
    ('pragma-calls rules section counted as code', 'pragma-calls.py',
     '        counts = collections.Counter(TOK.findall(code(txt) if raw else txt))\n',
     '        counts = collections.Counter(TOK.findall(txt))\n', ST),
    ('pragma-calls cache of the whole dumps reused for the code alone', 'pragma-calls.py',
     "    key = sig + ('code',) if raw else sig\n",
     '    key = sig\n', ST),
    ('pragma-calls corrupt cache stops the run', 'pragma-calls.py',
     '    except (OSError, pickle.UnpicklingError, EOFError):\n',
     '    except OSError:\n', ST),
    ('pragma-calls refused cache write stops the run', 'pragma-calls.py',
     '        except OSError as e:\n',
     '        except FileNotFoundError as e:\n', ST),
    # pragma-calls per module (2026-10-12): a name removed in several
    # modules counted towards each by qualifier and scope, each break
    # watched failing its self-test before it was written down here.
    ('pragma-calls per module counts any qualified token', 'pragma-calls.py',
     '        if q == mod:\n', '        if q == mod or q:\n', ST),
    ('pragma-calls per module counts an importer\'s own name', 'pragma-calls.py',
     '            return not defines(srcs[k], n) and any(map(reaches, scopes[k][1]))\n',
     '            return any(map(reaches, scopes[k][1]))\n', ST),
    ('pragma-calls per module takes a binder of its own for a re-exporter', 'pragma-calls.py',
     '        return (t is not None and not defines(t, n)\n',
     '        return (t is not None\n', ST),
    ('pragma-calls uncached run not said', 'pragma-calls.py',
     "            print(f'pragma-calls: could not cache the counts at {cache} '\n",
     "            print(f'pragma-calls: the counts at {cache} '\n", ST),
    ('core-diff static data counted as a copy', 'core-diff.py',
     "        return family(tok) + (' (data)' if data else '')\n",
     '        return family(tok)\n', ST),
    ('core-diff two-line definition unread', 'core-diff.py',
     '        if (line == name and k + 1 < len(block)\n',
     '        if (False and k + 1 < len(block)\n', ST),
    ('core-diff string literal read as code', 'core-diff.py',
     '    return (head.startswith(\'"\')\n',
     '    return (False\n', ST),
    ('core-diff constructor application read as code', 'core-diff.py',
     "            or head[:1].isupper() or head.startswith(':'))\n",
     '            )\n', ST),
    ('core-diff unpacked string read as code', 'core-diff.py',
     "            or head in ('unpackCString#', 'unpackCStringUtf8#')\n",
     '            or head in ()\n', ST),
    # spec-audit (2026-10-10): the branches its defects 01 to 07 brought,
    # each watched failing its self-test before it was written down here.
    ('spec-audit qualified definition line read as a call', 'spec-audit.py',
     '            if (re.fullmatch(QUAL, line[:m.start()])\n',
     '            if (m.start() == 0\n', ST),
    ('spec-audit floated binding read as a dictionary', 'spec-audit.py',
     '            if head is not None and not (head.startswith(m.group(1))\n',
     '            if False and not (head.startswith(m.group(1))\n', ST),
    # spec-audit-08 and -09.
    ('spec-audit class extending a listed one passed over', 'spec-audit.py',
     '            if head is not None and not (head.startswith(m.group(1))\n',
     '            if head is not None and not (head == m.group(1)\n', ST),
    ('spec-audit specialised dictionary read as two', 'spec-audit.py',
     "DICT = re.compile(r\"(?<![\\w$'])\\$f(\" + CLASSES"
     " + r\")[A-Z](?:(?!\\$c)[\\w$'])*\")\n",
     "DICT = re.compile(r\"\\$f(\" + CLASSES + r\")[A-Z][A-Za-z0-9_]*\")\n",
     ST),
    ("spec-audit floated binding in another module's dump unread", 'spec-audit.py',
     '            if ty is None and qual:\n',
     '            if False:\n', ST),
    ('spec-audit floated binding resolved in another component', 'spec-audit.py',
     '        p = max(hits)[1]\n',
     '        p = hits[0][1]\n', ST),
    ('spec-audit signature on the line below its name unread', 'spec-audit.py',
     "        elif i + 1 < len(lines) and lines[i + 1].lstrip().startswith(':: '):\n",
     '        elif False:\n', ST),
    ("spec-audit signature's continuation lines unread", 'spec-audit.py',
     '        while j < len(lines) and lines[j][:1].isspace() and lines[j].strip():\n',
     '        while False:\n', ST),
    ("spec-audit forall kept before a type's head", 'spec-audit.py',
     '    m = FORALL.match(ty)\n    while m:\n',
     '    m = None\n    while m:\n', ST),
    ("spec-audit context read as a type's head", 'spec-audit.py',
     "    m = HEAD.match(ty.rsplit('=>', 1)[-1])\n",
     '    m = HEAD.match(ty)\n', ST),
    ('spec-audit named instance method stripped as a dictionary', 'spec-audit.py',
     'OTHER_DICT = re.compile(QUAL + r"\\$[fd](?:(?!\\$c)[\\w$])*',
     'OTHER_DICT = re.compile(QUAL + r"\\$[fd](?:[\\w$])*', ST),
    ('spec-audit operator instance method split from its name', 'spec-audit.py',
     'C:[\\w\']+|[$\\w][\\w$\']*\\$c" + OPS\n                  + r"|',
     'C:[\\w\']+|" + r"', ST),
    ('spec-audit class constructor split from its C:', 'spec-audit.py',
     "(?:C:[\\w']+|",
     '(?:', ST),
    ('spec-audit trailing # split from a name', 'spec-audit.py',
     "|[$\\w][\\w$']*#*|",
     "|[$\\w][\\w$']*|", ST),
    ('spec-audit constructor read as a callee', 'spec-audit.py',
     '    if re.sub(r"^(?:[A-Z][\\w\']*\\.)*", \'\', names[-1]).startswith((\':\', \'C:\')):\n',
     '    if False:\n', ST),
    ('spec-audit unboxed $d binder listed', 'spec-audit.py',
     "            if ty is not None and (type_head(ty) or '').endswith('#'):\n",
     '            if False:\n', ST),
    ('spec-audit binders on further lines unread', 'spec-audit.py',
     "        while k < len(txt) and txt[k] in ' \\n':\n",
     "        while k < len(txt) and txt[k] == ' ':\n", ST),
    ('spec-audit nested parentheses in a binder type unread', 'spec-audit.py',
     "                depth += 1 if p.group() == '(' else -1\n",
     "                depth = 1 if p.group() == '(' else 0\n", ST),
    # pragma-calls --inline (2026-10-07): each watched failing its self-test
    # before it was written down here.
    ('pragma-calls --inline reads indented pragmas', 'pragma-calls.py',
     "INLINE_SRC = re.compile(r'^\\{-#", "INLINE_SRC = re.compile(r'^\\s*\\{-#", ST),
    ('pragma-calls --inline recursive groups unread', 'pragma-calls.py',
     '        rec = any(n in rec_binders(t) for t in texts)\n',
     '        rec = False\n', ST),
    ('pragma-calls --inline a module copying its own function counted', 'pragma-calls.py',
     "            if any(t.endswith('.' + n) and t[:-len(n) - 1].rsplit('.', 1)[-1]\n"
     "                   == here for t in c):\n                continue\n", '', ST),
    ('pragma-calls --inline a copy qualified by a third module counted', 'pragma-calls.py',
     "                if m and m.group(1).rstrip('.').rsplit('.', 1)[-1] in ('', here):\n",
     '                if m:\n', ST),
    ('pragma-calls --inline build directories read', 'pragma-calls.py',
     "        ds[:] = [d for d in ds if not d.startswith(('.', 'dist'))]\n", '', ST),
    ('pragma-calls --inline the defining module counted', 'pragma-calls.py',
     '            if k in own:\n                continue\n', '', ST),
    # pragma-calls-07 (2026-10-13): watched failing its self-test before it
    # was written down here.
    ('pragma-calls --inline a copy of an imported function counted as a call', 'pragma-calls.py',
     "    return set(RULE_RHS.findall(rules[1])) if len(rules) == 2 else set()\n",
     '    return set()\n', ST),
    # pragma-calls-08 (2026-10-13): watched failing its self-test before it
    # was written down here.
    ('pragma-calls per module a copy of an imported function counted towards the copier', 'pragma-calls.py',
     '                           if refers(km, q) and not copy(km, q, u, cs))\n',
     '                           if refers(km, q))\n', ST),
    # The one-build forms of core-diff, rules-diff and ticky-diff, and
    # bang-drops, lazy-reads and captured-unbox, the 908 detectors moved in
    # from a handoff (2026-10-07): each watched failing its self-test before
    # it was written down here.
    ('core-diff one-build census sorted by name', 'core-diff.py',
     '        for n in sorted(m.names, key=lambda n: (-sizes[n], -m.names[n], n)):\n',
     '        for n in sorted(m.names):\n', ST),
    ('rules-diff one-build listing of every rule', 'rules-diff.py',
     '        rows = sorted(((v, n) for n, v in r.items() if fusion(n)),\n',
     '        rows = sorted(((v, n) for n, v in r.items()),\n', ST),
    ('ticky-diff one-run listing sorted by name', 'ticky-diff.py',
     '    for k in sorted(a, key=lambda k: (-a[k][1], k))[:top]:\n',
     '    for k in sorted(a)[:top]:\n', ST),
    ('bang-drops a <- binding not read as unbanged', 'bang-drops.py',
     '            or re.search(r"(?:^|[\\s(,{;])" + e + r"\\s*<-", ln)]\n',
     '            ]\n', ST),
    ('bang-drops a banged name gone not reported', 'bang-drops.py',
     "                    elif not re.search(r\"(?<![\\w'])\" + e + r\"(?![\\w'])\", nb):\n",
     '                    elif False:\n', ST),
    # bang-drops-01: the word-boundary test, which finds no boundary after
    # a name's prime, so a kept u' read as gone.
    ('bang-drops a kept primed name read as gone', 'bang-drops.py',
     "                    elif not re.search(r\"(?<![\\w'])\" + e + r\"(?![\\w'])\", nb):\n",
     "                    elif not re.search(r\"\\b\" + e + r\"\\b\", nb):\n", ST),
    ('lazy-reads a lambda right-hand side read as a value', 'lazy-reads.py',
     "                    if x == 'in' or not rhs or rhs.lstrip().startswith('\\\\'):\n",
     "                    if x == 'in' or not rhs:\n", ST),
    ('lazy-reads sections unread', 'lazy-reads.py',
     "                            tags.add('section')\n", '                            pass\n', ST),
    ('captured-unbox Int boxes unread', 'captured-unbox.py',
     '                 r"(?:[IW](?:8|16|32|64)?|D|F|C)# ")\n', '                 r"D# ")\n', ST),
    ('captured-unbox qualified boxes unread', 'captured-unbox.py',
     'BOX = re.compile(r"case ([\\w$\']+) of \\{ (?:[\\w.\'-]+:)?(?:[A-Z][\\w\']*\\.)*"\n',
     'BOX = re.compile(r"case ([\\w$\']+) of \\{ "\n', ST),
    ('captured-unbox a loop parameter read as captured', 'captured-unbox.py',
     "            if re.search(r\"(?<![\\w$'])\" + re.escape(x) + r\"(?![\\w$'])\", region):\n",
     '            if False:\n', ST),
    # workaround-cites (2026-10-07): each watched failing its self-test before
    # it was written down here.
    ('workaround-cites "unidentified" not taken for a cause', 'workaround-cites.py',
     "                   r'|\\bunidentified\\b|stands? in for', re.I)\n",
     "                   r'|stands? in for', re.I)\n", ST),
    ('workaround-cites reference-style issue numbers unread', 'workaround-cites.py',
     "ISSUE_LINK = re.compile(r'(?:work_items|issues)/(\\d+)|\\bissue (\\d+)|#(\\d{3,})')\n",
     "ISSUE_LINK = re.compile(r'(?:work_items|issues)/(\\d+)|#(\\d{3,})')\n", ST),
    ('workaround-cites trailing comments unread', 'workaround-cites.py',
     "            if m and '\"' not in line[:m.start()]:\n", '            if False:\n', ST),
    ('workaround-cites block comments unread', 'workaround-cites.py',
     "        if s.startswith('{-') and not s.startswith('{-#'):\n", '        if False:\n', ST),
    # hascallstack (2026-10-08): each watched failing its self-test before
    # it was written down here.
    ('hascallstack contract wording ignored', 'hascallstack.py',
     "         if any(CONTRACT not in msg for _, msg in d['errors'])}\n",
     "         if d['errors']}\n", ST),
    ('hascallstack delegation disabled', 'hascallstack.py',
     "               if g not in v and f in v and f[1] == g[1] and f[0] != g[0]}\n",
     "               if False}\n", ST),
    ('hascallstack delegation under any name', 'hascallstack.py',
     "               if g not in v and f in v and f[1] == g[1] and f[0] != g[0]}\n",
     "               if g not in v and f in v and f[0] != g[0]}\n", ST),
    ('hascallstack unused import kept', 'hascallstack.py',
     "    elif has and not uses:\n", "    elif False:\n", ST),
    ('hascallstack comments counted as uses', 'hascallstack.py',
     "    code = '\\n'.join(l for l in strip_comments(s).split('\\n')\n",
     "    code = '\\n'.join(l for l in s.split('\\n')\n", ST),
    ('hascallstack recursion unreported', 'hascallstack.py',
     "        if k in v and (k, k) in edges:\n", "        if False:\n", ST),
    ('hascallstack internal wording unchecked', 'hascallstack.py',
     "            if UNWORDED.search(line) or (k[0] == cfg['internal']\n"
     "                                         and CONTRACT not in msg):\n",
     "            if UNWORDED.search(line):\n", ST),
    # pragma-census (2026-10-10): each watched failing its self-test before
    # it was written down here.
    ('pragma-census HasCallStack taken for a class', 'pragma-census.py',
     "            if p.strip() and p.strip() != 'HasCallStack' and '~' not in p\n",
     "            if p.strip() and '~' not in p\n", ST),
    ('pragma-census equalities taken for a class', 'pragma-census.py',
     "            if p.strip() and p.strip() != 'HasCallStack' and '~' not in p\n",
     "            if p.strip() and p.strip() != 'HasCallStack'\n", ST),
    # pragma-census-11 (2026-10-12): a list consumed more than once, or
    # taken apart by a pattern, no direct fusion; watched failing its
    # self-test before it was written down here.
    ('pragma-census list consumed more than once read as fusing', 'pragma-census.py',
     '                or (args and (eqs is None or consumed_once(eqs, ty))\n',
     '                or (args and (eqs is None or True)\n', ST),
    ('pragma-census TypeError taken for a class', 'pragma-census.py',
     "            and not p.strip().startswith('TypeError') and '<=' not in p]\n",
     "            and '<=' not in p]\n", ST),
    ('pragma-census type-level <= taken for a class', 'pragma-census.py',
     "            and not p.strip().startswith('TypeError') and '<=' not in p]\n",
     "            and not p.strip().startswith('TypeError')]\n", ST),
    ('pragma-census --skip leaves its file in', 'pragma-census.py',
     '                  and os.path.relpath(os.path.join(d, x), src) not in SKIP]\n',
     '                  and True]\n', ST),
    ('pragma-census multi-line signatures cut at their first line', 'pragma-census.py',
     "    while (j < len(lines) and lines[j][:1] in (' ', '\\t')\n",
     "    while (False and lines[j][:1] in (' ', '\\t')\n", ST),
    ('pragma-census a signature of several names read as one', 'pragma-census.py',
     "                for name in re.split(r'\\s*,\\s*', m.group(1).strip()):\n",
     '                for name in [m.group(1).strip()]:\n', ST),
    ("pragma-census a function's pragma unread", 'pragma-census.py',
     '                    if cs and name not in module_pragmas:\n',
     '                    if cs:\n', ST),
    ('pragma-census a phase-controlled pragma unread', 'pragma-census.py',
     "                    + r'(?:\\[~?\\d+\\]\\s*)?\\(?([^\\s)#,]+)')\n",
     "                    + r'\\(?([^\\s)#,]+)')\n", ST),
    ('pragma-census SPECIALISE not taken for a pragma', 'pragma-census.py',
     "PRAGMA = re.compile(r'\\{-#\\s*(?:' + KIND + ')' + MODIFIERS\n",
     "PRAGMA = re.compile(r'\\{-#\\s*(?:' + KIND.replace('|SPECIALI[SZ]E', '')"
     " + ')' + MODIFIERS\n", ST),
    ('pragma-census multi-line instance heads cut', 'pragma-census.py',
     "    while not re.search(r'\\bwhere\\b', head) and j + 1 < len(lines) \\\n",
     '    while False and j + 1 < len(lines) \\\n', ST),
    ('pragma-census a blank line ends an instance', 'pragma-census.py',
     "            if n == len(lines) or lines[n][:1] not in (' ', '\\t'):\n",
     '            if True:\n', ST),
    # pragma-census-05 (2026-10-11): a comment at column 0 ended a body.
    ('pragma-census a comment at column 0 taken for the body indentation',
     'pragma-census.py',
     '    rest = [(n, lines[n]) for n in range(j + 1, k) if not gap(lines[n])]\n',
     '    rest = [(n, lines[n]) for n in range(j + 1, k) if lines[n].strip()]\n', ST),
    ('pragma-census a comment at column 0 ends a body', 'pragma-census.py',
     "    return not line.strip() or bool(re.match(r'--+(?!' + OP + ')', line))\n",
     '    return not line.strip()\n', ST),
    ("pragma-census a one-line instance's method unread", 'pragma-census.py',
     "    return [(j, hm.group(2) or '')] + [\n",
     '    return [] + [\n', ST),
    ("pragma-census a method's pragma unread", 'pragma-census.py',
     '                        if name and name not in seen and name not in pragmas \\\n',
     '                        if name and name not in seen \\\n', ST),
    ('pragma-census a method listed once an equation', 'pragma-census.py',
     '                        if name and name not in seen and name not in pragmas \\\n',
     '                        if name and name not in pragmas \\\n', ST),
    ('pragma-census undefined methods listed', 'pragma-census.py',
     "                                and not b.rstrip().endswith('= undefined'):\n",
     '                                and True:\n', ST),
    ("pragma-census an instance's signatures read as definitions", 'pragma-census.py',
     "    if not s or s.startswith(('--', '{-', '|')) or SIGNATURE.match(s):\n",
     "    if not s or s.startswith(('--', '{-', '|')):\n", ST),
    ('pragma-census a definition holding :: read as a signature', 'pragma-census.py',
     "    if not s or s.startswith(('--', '{-', '|')) or SIGNATURE.match(s):\n",
     "    if not s or s.startswith(('--', '{-', '|')) or '::' in s:\n", ST),
    ('pragma-census operator sections unread', 'pragma-census.py',
     '    m = SECTION.match(s)\n',
     '    m = None\n', ST),
    ('pragma-census infix definitions named by their left operand', 'pragma-census.py',
     "    if m and m.group(1) not in ('=', '|'):\n",
     '    if False:\n', ST),
    ('pragma-census continuation lines read as methods', 'pragma-census.py',
     '    return [(n, b) for n, b in rest if indent(b) == base]\n',
     '    return [(n, b) for n, b in rest]\n', ST),
    ('pragma-census as-patterns unread', 'pragma-census.py',
     '    m = re.match(r"[\\w\']+@", s)\n',
     '    m = None\n', ST),
    ('pragma-census nested parentheses cut at the first', 'pragma-census.py',
     '        if depth == 0:\n            return j + 1\n',
     "        if s[j] == close:\n            return j + 1\n", ST),
    # pragma-census-01, watched failing its self-test before it was written
    # down here.
    ("pragma-census a rank-2 argument's context taken for the signature's",
     'pragma-census.py',
     "        if depth == 0 and sig.startswith('=>', i):\n",
     "        if sig.startswith('=>', i):\n", ST),
    # pragma-census --rule (2026-10-10): each watched failing its
    # self-test before it was written down here.
    ('pragma-census --rule a function-typed argument unseen', 'pragma-census.py',
     "                len(depth0(a[1:-1], '->')) > 1:\n",
     "                len(depth0(a[1:-1], '->')) > 9:\n", ST),
    ("pragma-census --rule a type's own class constraint unseen", 'pragma-census.py',
     '    if overloaded_too or overloaded(ty):\n',
     '    if overloaded_too:\n', ST),
    ("pragma-census --rule an instance's context unseen", 'pragma-census.py',
     '                over = bool(constraints(ctx)) if ctx else False\n',
     '                over = False\n', ST),
    ('pragma-census --rule a haddock taken for a note', 'pragma-census.py',
     '            inside = True\n',
     '            inside = False\n', ST),
    ('pragma-census --rule a note above a haddock unread', 'pragma-census.py',
     '    return any(pat.search(x) for x in plain)\n',
     '    return False\n', ST),
    ('pragma-census --rule a note above an instance unread', 'pragma-census.py',
     '                          [i, n] + ([isigs[name][1]] if name in isigs\n',
     '                          [n] + ([isigs[name][1]] if name in isigs\n', ST),
    ('pragma-census --rule a module declaration unread', 'pragma-census.py',
     "    mdecl = declared([x for x in lines[:start] if x.lstrip().startswith('--')],\n",
     "    mdecl = None and declared([x for x in lines[:start] if x.lstrip().startswith('--')],\n",
     ST),
    ('pragma-census --rule a phase-controlled pragma judged', 'pragma-census.py',
     '        if phased:\n',
     '        if False:\n', ST),
    ('pragma-census --rule SPECIALISE not taken for INLINABLE', 'pragma-census.py',
     "        has = {'INLINEABLE': 'INLINABLE', 'SPECIALISE': 'INLINABLE',\n",
     "        has = {'INLINEABLE': 'INLINABLE',\n", ST),
    ('pragma-census --rule recursion unseen', 'pragma-census.py',
     '                recursive_here[name] = recursive(lines, k, name)\n',
     '                recursive_here[name] = False\n', ST),
    ('pragma-census --rule a name in a string taken for recursion', 'pragma-census.py',
     '        line = re.sub(r\'"(?:[^"\\\\]|\\\\.)*"\', \'""\', line)\n',
     '', ST),
    ('pragma-census --rule a name in a trailing comment taken for recursion', 'pragma-census.py',
     "        line = re.sub(r'(^|\\s)--(\\s.*)?$', '', line)\n",
     '', ST),
    ('pragma-census --rule an associated type read as a method', 'pragma-census.py',
     "                            re.match(r'\\s*(type|data)\\b', b):\n",
     '                            False:\n', ST),
    ('pragma-census --rule a method defined as error judged', 'pragma-census.py',
     "    return rhs == 'undefined' or rhs.startswith('error ')\n",
     "    return rhs == 'undefined'\n", ST),
    ('pragma-census --rule the standard classes unknown', 'pragma-census.py',
     '    files, texts, classes = hs_files(src), {}, dict(STD)\n',
     '    files, texts, classes = hs_files(src), {}, {}\n', ST),
    ('pragma-census --rule a forwarder of a forwarder missed', 'pragma-census.py',
     '                    grew = True\n',
     '                    grew = False\n', ST),
    ('pragma-census --rule a call through a qualified alias unresolved', 'pragma-census.py',
     '            mods = aliases.get(qual[:-1], ())\n',
     '            mods = ()\n', ST),
    ('pragma-census --rule a call through an unqualified import unresolved', 'pragma-census.py',
     '            mods = opens\n',
     '            mods = []\n', ST),
    ('pragma-census --rule a caller sharing no list taken for a forwarder', 'pragma-census.py',
     "                       and (need[c] != 'A3' and lists & table[c][0]\n",
     "                       and (need[c] != 'A3' and True\n", ST),
    ('pragma-census --rule a commented INLINE not taken for a seed', 'pragma-census.py',
     '    need = {k: seed for k, (_, seed, _) in table.items() if seed}\n',
     '    need = {}\n', ST),
    ('pragma-census --rule a forwarder judged by its type alone', 'pragma-census.py',
     "        if w != 'INLINE' and key in fwd:\n",
     '        if False:\n', ST),
    ('pragma-census --rule a facade not followed to what it re-exports', 'pragma-census.py',
     '        return set().union(*[defining(y, name, seen) for y in info[x][1]])\n',
     '        return set()\n', ST),
    ('pragma-census --rule any note taken for an F1 one', 'pragma-census.py',
     '                where[(mod, name)] = (path, i, noted(lines, i, F1NOTE))\n',
     '                where[(mod, name)] = (path, i, noted(lines, i))\n', ST),
    ('pragma-census --rule a root calling a tree binding of no shared list taken for shallow', 'pragma-census.py',
     '            if c and c != k and elements(table[k][0] & table[c][0]):\n',
     '            if c and c != k:\n', ST),
    ('pragma-census --rule a shape list taken for one handed on', 'pragma-census.py',
     '            if c and c != k and elements(table[k][0] & table[c][0]):\n',
     '            if c and c != k and table[k][0] & table[c][0]:\n', ST),
    ('pragma-census --rule a root handing its list on left unreported', 'pragma-census.py',
     '        if not f1 or not table[k][1]:\n            continue\n',
     '        if True:\n            continue\n', ST),
    ('pragma-census --rule a departure not overriding its body', 'pragma-census.py',
     '    if departs(lines, notes, has):\n        return None\n',
     '    if False:\n        return None\n', ST),
    ('pragma-census --rule a departure kept as a forwarder', 'pragma-census.py',
     '            if k in need or k in over:\n',
     '            if k in need:\n', ST),
    ('pragma-census --rule a note denying fusion held to the hand-off check', 'pragma-census.py',
     '        if not f1 or not table[k][1]:\n            continue\n',
     '        if not f1:\n            continue\n', ST),
    ('pragma-census constructor arguments cut from an infix pattern',
     'pragma-census.py',
     "    while s[i:i + 1].isupper():\n",
     "    while False:\n", ST),
    # pragma-census-03 (2026-10-11): a class head spanning lines, and the
    # class default methods read with it.
    # The throughout declarations (2026-10-11): INLINE, INLINABLE and
    # No pragma, over a module from its header or over an instance or class
    # from directly above it.
    ('pragma-census --rule a declaration read past the module line', 'pragma-census.py',
     "    mdecl = declared([x for x in lines[:start] if x.lstrip().startswith('--')],\n",
     "    mdecl = declared([x for x in lines if x.lstrip().startswith('--')],\n", ST),
    ('pragma-census --rule an instance declaration unread', 'pragma-census.py',
     '                hdecl = declared(plain_lines(lines, i), i + 1)\n',
     '                hdecl = None\n', ST),
    ('pragma-census --rule a class declaration unread', 'pragma-census.py',
     '            cdecl = declared(plain_lines(lines, i), i + 1)\n',
     '            cdecl = None\n', ST),
    # pragma-census-07 and -08 (2026-10-11): a signature whose :: starts the
    # next line, in a class and at top level.
    ('pragma-census a top-level signature split before :: unread', 'pragma-census.py',
     "    if m is None and lines[i][:1] not in (' ', '\\t') \\\n",
     "    if False and lines[i][:1] not in (' ', '\\t') \\\n", ST),
    ("pragma-census a split top-level signature's :: kept in its type", 'pragma-census.py',
     '    return (sig if m.re is TOP_SIG else sig.strip()[2:]), j\n',
     '    return sig, j\n', ST),
    ('pragma-census a class signature split before :: unread', 'pragma-census.py',
     '        split = split_signature(lines, n, k)\n',
     '        split = None\n', ST),
    ("pragma-census a split class signature's :: kept in its type", 'pragma-census.py',
     '            ty = ty.strip()[2:] if split else ty\n',
     '            ty = ty\n', ST),
    ("pragma-census a split signature's name read as a definition", 'pragma-census.py',
     '        if split_signature(lines, n, k) is None]\n',
     '        if True]\n', ST),
    # pragma-census-06 (2026-10-11): a deeper comment above read as a note.
    ('pragma-census --rule a comment ending the body above read as a note', 'pragma-census.py',
     '    while k >= 0 and indent(lines[k]) == indent(lines[i]) and (\n',
     '    while k >= 0 and (\n', ST),
    # P's form for a reason note (2026-10-11): the pragma leading, and
    # a citation.
    ('pragma-census --rule a lead past the first line accepted', 'pragma-census.py',
     '    m = LEAD.match(plain[0]) if plain else None\n',
     '    m = next((LEAD.match(x) for x in plain if LEAD.match(x)), None)\n', ST),
    ('pragma-census --rule a lead naming another pragma accepted', 'pragma-census.py',
     '    return lead == has and bool(cited)\n',
     '    return bool(cited)\n', ST),
    ('pragma-census --rule a note citing nothing accepted', 'pragma-census.py',
     '    return lead == has and bool(cited)\n',
     '    return lead == has\n', ST),
    ('pragma-census --rule a GHC version without a date taken for a citation', 'pragma-census.py',
     '    cited = CITE.search(text) or (VERSION.search(text) and DATE.search(text))\n',
     '    cited = CITE.search(text) or VERSION.search(text)\n', ST),
    ('pragma-census --rule a GHC version with a date not taken for a citation', 'pragma-census.py',
     '    cited = CITE.search(text) or (VERSION.search(text) and DATE.search(text))\n',
     '    cited = CITE.search(text)\n', ST),
    ('pragma-census --rule see not taken for a citation', 'pragma-census.py',
     "CITE = re.compile(r'\\b(?:I[123]|F1|A3|S2|W[34])\\b|\\bsee\\b')\n",
     "CITE = re.compile(r'\\b(?:I[123]|F1|A3|S2|W[34])\\b')\n", ST),
    ('pragma-census --rule a check not taken for a citation', 'pragma-census.py',
     "CITE = re.compile(r'\\b(?:I[123]|F1|A3|S2|W[34])\\b|\\bsee\\b')\n",
     "CITE = re.compile(r'\\bsee\\b')\n", ST),
    ('pragma-census --rule No pragma not taken for a lead', 'pragma-census.py',
     "            'SPECIALIZE': 'INLINABLE', 'No pragma': 'none'}.get(lead, lead)\n",
     "            'SPECIALIZE': 'INLINABLE'}.get(lead, lead)\n", ST),
    ('pragma-census --rule an INLINE citing nothing taken for a seed', 'pragma-census.py',
     "        if has == 'INLINE' and reasoned(lines, x, 'INLINE'):\n",
     "        if has == 'INLINE' and noted(lines, x):\n", ST),
    # Directly fusing bindings found by their bodies, instance methods read
    # as forwarders, and a measured seed's forwarders whatever their type
    # (2026-10-11).
    ('pragma-census --rule a fusing producer unseen', 'pragma-census.py',
     '    return bool((result and PRODUCES.search(body))\n',
     '    return bool((False and PRODUCES.search(body))\n', ST),
    ('pragma-census --rule a fusing consumer unseen', 'pragma-census.py',
     '                    and any(outside(q, n)\n',
     '                    and False and any(outside(q, n)\n', ST),
    ('pragma-census --rule shape lists taken for element lists', 'pragma-census.py',
     "            if set(re.findall(r\"[A-Za-z_][\\w']*\", x)) - {'Int', 'Bool'}}\n",
     "            if x != '[Int]'}\n", ST),
    ('pragma-census --rule a declared binding asked for an F1 note', 'pragma-census.py',
     '        if key in fus and not fun_arg(ty) and not covered and not (\n',
     '        if key in fus and not fun_arg(ty) and not (\n', ST),
    ('pragma-census --rule instance methods unread as forwarders', 'pragma-census.py',
     "            if not line.startswith('instance'):\n",
     '            if True:\n', ST),
    ("pragma-census --rule a measured seed's forwarder held to a shared list", 'pragma-census.py',
     "                            and (qual, name) == head)]\n",
     '                            and False)]\n', ST),
    ("pragma-census --rule a measured seed's caller taken for its wrapper", 'pragma-census.py',
     "                            and (qual, name) == head)]\n",
     '                            )]\n', ST),
    ('pragma-census --rule a call through a class method unresolved', 'pragma-census.py',
     '        return [c] if c else sorted(methods.get(name, ()))\n',
     '        return [c] if c else []\n', ST),
    ('pragma-census --rule a fusing binding without its note unreported', 'pragma-census.py',
     '            unmarked.append((n + 1, name))\n',
     '            pass\n', ST),
    ('pragma-census --rule a function-argument binding asked for an F1 note', 'pragma-census.py',
     '        if key in fus and not fun_arg(ty) and not covered and not (\n',
     '        if key in fus and not covered and not (\n', ST),
    ('pragma-census --rule a fusing binding not wanting INLINE', 'pragma-census.py',
     "        if w != 'INLINE' and key in fus:\n",
     '        if False:\n', ST),
    ("pragma-census --rule an instance declaration not overriding the module's", 'pragma-census.py',
     '                          mdecl if hdecl is None else hdecl,\n',
     '                          mdecl or hdecl,\n', ST),
    ("pragma-census --rule a module declaration not reaching an instance", 'pragma-census.py',
     '                          mdecl if hdecl is None else hdecl,\n',
     '                          hdecl,\n', ST),
    ('pragma-census --rule a binding carrying another pragma covered', 'pragma-census.py',
     '        covered = decl is not None and decl.covers(name, has)\n',
     '        covered = decl is not None\n', ST),
    ('pragma-census --rule No pragma throughout unread', 'pragma-census.py',
     "DECL = re.compile(r'\\b(INLINE|INLINABLE|INLINEABLE|[Nn]o pragma) throughout\\b'\n",
     "DECL = re.compile(r'\\b(INLINE|INLINABLE|INLINEABLE) throughout\\b'\n", ST),
    ('pragma-census --rule INLINEABLE throughout unread', 'pragma-census.py',
     "DECL = re.compile(r'\\b(INLINE|INLINABLE|INLINEABLE|[Nn]o pragma) throughout\\b'\n",
     "DECL = re.compile(r'\\b(INLINE|INLINABLE|[Nn]o pragma) throughout\\b'\n", ST),
    # pragma-census-04 (2026-10-11): `m:: T` read as a definition.
    ('pragma-census a signature without a space before :: read as a definition',
     'pragma-census.py',
     '''                       r"\\s*::(?![!#$%&*+./<=>?@\\\\^|~:-])")\n''',
     '''                       r"\\s+::(?![!#$%&*+./<=>?@\\\\^|~:-])")\n''', ST),
    ('pragma-census a comment line inside a head read as part of it',
     'pragma-census.py',
     "        if not lines[j].lstrip().startswith('--'):\n",
     '        if True:\n', ST),
    ("pragma-census a class head's context taken for its name",
     'pragma-census.py',
     '    h = h[len(ctx) + 2:] if ctx is not None else h\n',
     '    h = h\n', ST),
    ('pragma-census class signatures cut at their first line',
     'pragma-census.py',
     '            while c < k and indent(lines[c]) > indent(b) and lines[c].strip():\n',
     '            while False:\n', ST),
    ('pragma-census class default methods unlisted', 'pragma-census.py',
     '            dms += [(n + 1, cls, name) for n, name, _, p in dm if p is None]\n',
     '            dms += []\n', ST),
    ("pragma-census a default method's pragma unread", 'pragma-census.py',
     '            dms += [(n + 1, cls, name) for n, name, _, p in dm if p is None]\n',
     '            dms += [(n + 1, cls, name) for n, name, _, p in dm]\n', ST),
    ('pragma-census a default method defined as undefined listed',
     'pragma-census.py',
     '        if name in sigs and name not in seen and not stub(b):\n',
     '        if name in sigs and name not in seen:\n', ST),
    ('pragma-census a default method listed once an equation',
     'pragma-census.py',
     '        if name in sigs and name not in seen and not stub(b):\n',
     '        if name in sigs and not stub(b):\n', ST),
    ('pragma-census --rule class default methods unjudged', 'pragma-census.py',
     '            for n, name, sn, p in dm:\n',
     '            for n, name, sn, p in []:\n', ST),
    ('pragma-census --rule a note above a class unread', 'pragma-census.py',
     '                      [i, n, sn],\n',
     '                      [n, sn],\n', ST),
    ("pragma-census --rule a note above a default method's signature unread",
     'pragma-census.py',
     '                      [i, n, sn],\n',
     '                      [i, n],\n', ST),
    ("pragma-census --rule a note above a default method's definition unread",
     'pragma-census.py',
     '                      [i, n, sn],\n',
     '                      [i, sn],\n', ST),
    # Types marked as never to be built and the bindings that take or return
    # them (A3), 2026-10-12.
    ('pragma-census --rule a marked type unread', 'pragma-census.py',
     '            if plain and UNMAT.match(plain[0]) and is_sum(lines, i):\n',
     '            if False:\n', ST),
    ('pragma-census --rule a mark below a comment\'s first line read',
     'pragma-census.py',
     '            if plain and UNMAT.match(plain[0]) and is_sum(lines, i):\n',
     '            if plain and any(UNMAT.match(x) for x in plain)'
     ' and is_sum(lines, i):\n', ST),
    ('pragma-census --rule a marked product taken for a sum', 'pragma-census.py',
     "    return len(depth0(rhs, '|')) > 1\n",
     '    return True\n', ST),
    ('pragma-census --rule a marked synonym taken for a product',
     'pragma-census.py',
     "    if lines[i].startswith('type'):\n",
     '    if False:\n', ST),
    ("pragma-census --rule a bar in a declaration's comment taken for a sum",
     'pragma-census.py',
     "    text = ' '.join(re.sub(r'--.*$', '', x) for x in decl)\n",
     "    text = ' '.join(decl)\n", ST),
    ("pragma-census --rule a declaration's later lines unread", 'pragma-census.py',
     "    while j < len(lines) and (not lines[j].strip() or lines[j][:1] in ' \\t'):\n",
     '    while False:\n', ST),
    ('pragma-census --rule an A3 binding not wanting INLINE', 'pragma-census.py',
     "        if w != 'INLINE' and types:\n",
     '        if False:\n', ST),
    ('pragma-census --rule an A3 binding without its note unreported',
     'pragma-census.py',
     '            unbuilt.append((n + 1, name, types))\n',
     '            pass\n', ST),
    ('pragma-census --rule an A3 note not asked to name its types',
     'pragma-census.py',
     '                        and all(noted(lines, x, re.compile(\n',
     '                        and all(True or noted(lines, x, re.compile(\n', ST),
    ('pragma-census --rule an A3 departure asked for an A3 note',
     'pragma-census.py',
     '        if types and not departs(lines, notes, has) and \\\n',
     '        if types and \\\n', ST),
    ("pragma-census --rule an A3 seed's caller taken for its wrapper",
     'pragma-census.py',
     "                    else 'A3' if noted(lines, x, A3NOTE) else 'measured')\n",
     "                    else 'measured')\n", ST),
    ('pragma-census --rule A3 not taken for a citation', 'pragma-census.py',
     "CITE = re.compile(r'\\b(?:I[123]|F1|A3|S2|W[34])\\b|\\bsee\\b')\n",
     "CITE = re.compile(r'\\b(?:I[123]|F1|S2|W[34])\\b|\\bsee\\b')\n", ST),
    # pragma-census --write (2026-10-13): each watched failing its
    # self-test before it was written down here.
    ('pragma-census --write releases without --release', 'pragma-census.py',
     "            elif has == 'NOINLINE' or release or RANK[w] > RANK[has]:\n",
     '            elif True:\n', ST),
    ('pragma-census --write keep lines unread', 'pragma-census.py',
     '            if (rel, name) in keep:\n',
     '            if False:\n', ST),
    ('pragma-census --write over a SPECIALISE', 'pragma-census.py',
     "    if kind.startswith('SPECIALI'):\n",
     '    if False:\n', ST),
    ('pragma-census --write edits top-down', 'pragma-census.py',
     '            for e in sorted(edits, key=lambda e: e[1], reverse=True):\n',
     '            for e in sorted(edits, key=lambda e: e[1]):\n', ST),
    # pragma-census --rule thin wrappers (2026-10-13): each caught by its
    # self-test when added.
    ('pragma-census --rule a thin wrapper not wanting INLINE', 'pragma-census.py',
     "        if w != 'INLINE' and thin(eqs, fields):\n",
     '        if False:\n', ST),
    ('pragma-census --rule a newtype field counted as a call', 'pragma-census.py',
     '                              or name in bound or name in fields\n',
     '                              or name in bound\n', ST),
    ('pragma-census --rule an operator not counted as a call', 'pragma-census.py',
     "                calls += t[0] != ':'\n",
     '                calls += 0\n', ST),
    ("pragma-census --rule a method's later equations unread", 'pragma-census.py',
     '    while j < k and (not lines[j].strip() or indent(lines[j]) >= ind):\n',
     '    while j < k and (j == n or indent(lines[j]) > ind):\n', ST),
    ('pragma-census --rule a type annotation read as calls', 'pragma-census.py',
     "        if skip is None and s.startswith('::', i):\n",
     '        if False:\n', ST),
    ("pragma-census --rule a lambda's binders read as calls", 'pragma-census.py',
     '                lam = True\n',
     '                lam = False\n', ST),
    # pragma-census-12 (2026-10-13): each caught by its self-test when added.
    ("pragma-census --rule equations after another name's unread",
     'pragma-census.py',
     '                k = own_start(lines, j, name, names)\n'
     '                recursive_here[name] = recursive(lines, k, name)\n',
     '                k = j\n'
     '                recursive_here[name] = recursive(lines, k, name)\n', ST),
    ("pragma-census --rule equations after another name's unread to forward",
     'pragma-census.py',
     '                k = own_start(lines, j, name, names)\n'
     '                body = definition(lines, k, name)\n',
     '                k = j\n'
     '                body = definition(lines, k, name)\n', ST),
    # pragma-census-13 (2026-10-13): caught by its self-test when added.
    ("pragma-census --rule an instance method's signature's note unread",
     'pragma-census.py',
     '                          [i, n] + ([isigs[name][1]] if name in isigs\n'
     '                                    else []), (),\n',
     '                          [i, n], (),\n', ST),
    # pragma-census-21 to -23 (2026-10-17): each watched failing its
    # self-test before it was written down here.
    ('pragma-census block comments read as code by the census',
     'pragma-census.py',
     "    lines = blank_blocks(text).split('\\n')\n",
     "    lines = text.split('\\n')\n", ST),
    ('pragma-census --rule block comments read as code', 'pragma-census.py',
     '            texts[path] = blank_blocks(fh.read())\n',
     '            texts[path] = fh.read()\n', ST),
    # A declaration naming its exceptions (2026-10-18): each watched failing
    # its self-test before it was written down here.
    ('pragma-census declaration claiming more than its scope bears',
     'pragma-census.py',
     '                if has != d.pragma and not d.names(name)]\n',
     '                if False]\n', ST),
    ('pragma-census declaration naming a binding of its own pragma',
     'pragma-census.py',
     '            elif all(has == d.pragma for has in hits):\n',
     '            elif False:\n', ST),
    ('pragma-census cited declaration excusing none of its exceptions',
     'pragma-census.py',
     '                decl is not None and decl.names(name) and decl.cited):\n',
     '                False):\n', ST),
    ('pragma-census declaration citing F1 excusing no fusing exception',
     'pragma-census.py',
     '                decl is not None and decl.names(name) and decl.f1)'
     ' and not any(\n',
     '                False) and not any(\n', ST),
    ('pragma-census declaration covering its exceptions too',
     'pragma-census.py',
     '        return has == self.pragma and not self.names(name)\n',
     '        return has == self.pragma\n', ST),
    ('pragma-census coerce counted as a call of a thin wrapper',
     'pragma-census.py',
     "                              or name in bound or name in fields\n"
     "                              or name == 'coerce')\n",
     "                              or name in bound or name in fields)\n", ST),
    # hssource-03 (2026-10-17): the block comment scanner pragma-census
    # shares, judged by its self-test, which caught it.
    ('hssource a pragma inside a block comment closing it', 'hssource.py',
     'INSIDE = re.compile(r"\\{-|-\\}")\n',
     'INSIDE = re.compile(r"-\\}")\n',
     'cd {dir} && python3 pragma-census.py --self-test'),
    # hpc-untaken (2026-10-13): each watched failing its self-test before
    # it was written down here.
    ('hpc-untaken error calls listed', 'hpc-untaken.py',
     '            if ERR.match(e) or TRIV.fullmatch(e) or e in trivial:\n',
     '            if TRIV.fullmatch(e) or e in trivial:\n', ST),
    ('hpc-untaken --trivial unread', 'hpc-untaken.py',
     '            if ERR.match(e) or TRIV.fullmatch(e) or e in trivial:\n',
     '            if ERR.match(e) or TRIV.fullmatch(e):\n', ST),
    ('hpc-untaken a binding never left', 'hpc-untaken.py',
     '                inside.pop()\n',
     '                pass\n', ST),
    ('hpc-untaken the source line after the tick', 'hpc-untaken.py',
     "                row += ' | ' + (text[ln - 1].strip() if ln <= len(text)\n",
     "                row += ' | ' + (text[ln].strip() if ln <= len(text)\n", ST),
    # cg-read-01 and -02 (2026-10-17): a sweep through an info table falls out
    # of step with the code after it; restarted at every executed address
    # it missed. Each mutant below was watched failing its self-test
    # before it was written down here.
    ('cg-read sweep not restarted at a missed address', 'cg-read.py',
     '            todo.difference_update(text)\n',
     '            todo.clear()\n', ST),
    ("cg-read a call's inclusive cost counted as its own", 'cg-read.py',
     '                skip = True\n',
     '                skip = False\n', ST),
    ('cg-read unit prefix not stripped', 'cg-read.py',
     "    return UNIT.sub('', name)\n",
     '    return name\n', ST),
    ("cg-read a library's cost lines counted as the binary's", 'cg-read.py',
     '                if obs.get(cur):\n',
     '                if True:\n', ST),
    ('cg-read addresses outside the text section attributed', 'cg-read.py',
     '        return self.lo <= a < self.hi\n',
     '        return True\n', ST),
    ('cg-read give-back read unsigned', 'cg-read.py',
     '            if x >= 1 << 63:\n',
     '            if False:\n', ST),
    ('cg-read sweep misses unreported', 'cg-read.py',
     '    return hot, {a: c for a, c in hot.items() if a not in starts}\n',
     '    return hot, {}\n', ST),
    ('cg-read relative positions accepted', 'cg-read.py',
     "            elif line[:1] in ('+', '-', '*'):\n",
     '            elif False:\n', ST),
    # cachegrind-per-call-01 (2026-10-17): cg-percall.sh's shell division
    # truncated; the cells mode that replaces it, each watched failing its
    # self-test before it was written down here.
    ("cachegrind-per-call cells' quotient truncated", 'cachegrind-per-call.py',
     "    return ((c2['Ir'] - c1['Ir']) / n,\n",
     "    return ((c2['Ir'] - c1['Ir']) // n,\n", ST),
    ('cachegrind-per-call summed cells run without --summed', 'cachegrind-per-call.py',
     "MODES = {'forced': [], 'summed': ['--summed']}\n",
     "MODES = {'forced': [], 'summed': []}\n", ST),
    ("cachegrind-per-call a cell's failure ends the run", 'cachegrind-per-call.py',
     '                    continue\n',
     '                    return 2\n', ST),
    ('cachegrind-per-call --cpu not pinned', 'cachegrind-per-call.py',
     "    return ((['taskset', '-c', cpu] if cpu is not None else []) + VALGRIND\n",
     '    return (([] if cpu is not None else []) + VALGRIND\n', ST),
    ('cachegrind-per-call benchmark arguments after --iters', 'cachegrind-per-call.py',
     "               f'--cachegrind-out-file={out}', binary] + list(args)\n            + ['--iters', str(iters), '-m', 'glob', name])\n",
     "               f'--cachegrind-out-file={out}', binary]\n            + ['--iters', str(iters), '-m', 'glob', name] + list(args))\n", ST),
    ('cachegrind-per-call --arg dropped', 'cachegrind-per-call.py',
     '            args.append(argv[1])\n',
     '            pass\n', ST),
    # row-core-01 and -02 (2026-10-17): a wrapped size comment ending the
    # binding above, and binder names cached across modules; each mutant
    # below was watched failing its self-test before it was written here.
    ('row-core wrapped size comments left in', 'row-core.py',
     "        t = re.sub(r'^-- RHS size: \\{[^}]*\\}$', '', t, flags=re.M)\n",
     '', ST),
    ("row-core one module's binders read for another's", 'row-core.py',
     '        owner, cache = collections.defaultdict(list), {}\n',
     "        owner, cache = collections.defaultdict(list), rows.__dict__.setdefault('names', {})\n", ST),
    ("row-core the library read as the benchmark's own code", 'row-core.py',
     '    return mods, scopes, {m for m in mods if dirs[m] in calls}\n',
     '    return mods, scopes, set(mods)\n', ST),
    ("row-core a module's own qualifier kept", 'row-core.py',
     "        t = re.sub(r'(?<![\\w.:])' + re.escape(m) + r'\\.(?=[a-z_$])', '', t)\n",
     '', ST),
    ('row-core literals verdict lost', 'row-core.py',
     "                'literals' if lit[0] == lit[1] else 'differs'\n",
     "                'differs'\n", ST),
    ('row-core casts kept by tokens', 'row-core.py',
     "        t = drop_groups(t, ' `cast` (', '')\n",
     '', ST),
    ('row-core unit qualifiers kept by tokens', 'row-core.py',
     "        t = UNITQ.sub('', t)\n",
     '', ST),
    # row-core-03 (2026-10-17): local names renamed by binding site; each
    # watched failing its self-test before it was written down here.
    ('row-core binding sites not used', 'row-core.py',
     '            s = sites.get(mt.start())\n',
     '            s = None\n', ST),
    ("row-core a type binder ends a lambda's binders", 'row-core.py',
     'BINDER = re.compile(r"\\((?:@\\()?@?([a-z_$][\\w$\'#]*) ::")\n',
     'BINDER = re.compile(r"\\(@?([a-z_$][\\w$\'#]*) ::")\n', ST),
    ("row-core a letrec's items open only from their own site", 'row-core.py',
     '            sites.append((toks[q], q, g if rec else q, outer))\n',
     '            sites.append((toks[q], q, q, outer))\n', ST),
    # row-core-04 (2026-10-18): string literals blanked before names are
    # matched; each watched failing its self-test before it was written here.
    ("row-core a string's words reached from a row", 'row-core.py',
     '    names = set(NAME.findall(mask(text)))\n',
     '    names = set(NAME.findall(text))\n', ST),
    ("row-core a string's words reached from a binder", 'row-core.py',
     '            cache[n] = set(NAME.findall(mask(body(binds, n))))\n',
     '            cache[n] = set(NAME.findall(body(binds, n)))\n', ST),
    ("row-core a string's words renamed", 'row-core.py',
     '    for mt in NAME.finditer(mask(text)):\n',
     '    for mt in NAME.finditer(text):\n', ST),
    # census (2026-10-17): the census scripts ported; each watched failing
    # its self-test before it was written down here.
    ('census large rows timed a call, not an element', 'census.py',
     "    ns = float(tab[row][k]) * (LARGE if row.split('/')[2] == 'large' else 1)\n",
     '    ns = float(tab[row][k])\n', ST),
    ('census a ratio at 0.2% not moving', 'census.py',
     'MOVE = 0.002 - 1e-12\n',
     'MOVE = 0.002 + 1e-12\n', ST),
    ('census a fully moving group counted again', 'census.py',
     '    return g, n, [r for k in sorted(g) if len(g[k]) < n[k]\n',
     '    return g, n, [r for k in sorted(g) if True\n', ST),
    ('census a resumed count counting again', 'census.py',
     '    todo = [mc for mc in want if mc not in done]\n',
     '    todo = list(want)\n', ST),
    ('census summed cells run without --summed', 'census.py',
     '                     \' --summed "$@"\\n\')\n',
     '                     \' "$@"\\n\')\n', ST),
    ('census lanes not pinned', 'census.py',
     "    cmd = ([sys.executable, PER_CALL] + (['--cpu', cpu] if cpu else [])\n",
     "    cmd = ([sys.executable, PER_CALL] + (['--cpu', cpu] if False else [])\n", ST),
    ('census noise counted at N, not ten times N', 'census.py',
     '            rc, text, fig = per_call(run[r[0]], r[1], 10 * int(r[2]), cpu,\n',
     '            rc, text, fig = per_call(run[r[0]], r[1], int(r[2]), cpu,\n', ST),
    ('census tables of different rows compared', 'census.py',
     '        if set(x) != set(y):\n',
     '        if False:\n', ST),
    ('census a raising cell ends its lane', 'census.py',
     '                ok.append(False)\n',
     '                raise\n', ST),
    # pragma-map-01 (2026-10-17), and the rest of pragma-map; each watched
    # failing its self-test before it was written down here.
    ('pragma-map INLINEABLE read as INLINE of ABLE', 'pragma-map.py',
     "PRAGMA = re.compile(r'\\{-#\\s*(INLINEABLE|INLINABLE|NOINLINE|INLINE)\\b\\s*'\n",
     "PRAGMA = re.compile(r'\\{-#\\s*(INLINE|INLINABLE|INLINEABLE|NOINLINE)\\s*'\n", ST),
    ('pragma-map pragmas in comments read', 'pragma-map.py',
     "                lines = hssource.strip_comments(fh.read()).split('\\n')\n",
     "                lines = fh.read().split('\\n')\n", ST),
    ('pragma-map an instance keyed with its context', 'pragma-map.py',
     "    return word + ' ' + k[len(word):].split('=>')[-1].strip()\n",
     '    return k\n', ST),
    ('pragma-map build directories read', 'pragma-map.py',
     "        ds[:] = sorted(d for d in ds if not d.startswith(('.', 'dist')))\n",
     '        ds[:] = sorted(ds)\n', ST),
]
