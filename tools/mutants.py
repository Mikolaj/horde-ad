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
    # check-doc-examples: "dropping the doc-local exclusion ... 2/1" (3/1 today, the
    # module-name control having been added since)
    ('check-doc-examples doc-local exclusion dropped', 'check-doc-examples.py',
     '        if n in loc or re.search(r"\\b" + n + r"\\b", src):\n',
     '        if re.search(r"\\b" + n + r"\\b", src):\n', ST),
    # check-doc-examples: "removing the skip in a copy turned it red" (module Main)
    ('check-doc-examples module Main skip removed', 'check-doc-examples.py',
     '              if not re.search(r"^module\\s+Main\\b", b, re.M)]\n', '              if True]\n', ST),
    # check-doc-examples: "removing that line from a copy reported the module's name"
    ('check-doc-examples module header no longer a doc-local name', 'check-doc-examples.py',
     '    for m in re.finditer(r"^module\\s+([\\w.]+)", code, re.M):\n        out |= set(m.group(1).split("."))\n',
     '    pass\n', ST),
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
    ('check-doc-refs CITE_RE blind to the range citation', 'check-doc-refs.py',
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
    # check-doc-wrap: a fence closed by one of another kind (check-doc-wrap-06)
    ('check-doc-wrap closes a block with a fence of any kind', 'check-doc-wrap.py',
     "        elif m and m.group(1)[0] == fence[0] and len(m.group(1)) >= len(fence):\n",
     "        elif m:\n", ST),
    # check-doc-wrap: "a repository tracking no Markdown reports BLOCKED rather than
    # 0 of 0 failed" (2026-08-28)
    ('check-doc-wrap repository tracking no Markdown reported as 0 of 0 failed', 'check-doc-wrap.py',
     '        print("BLOCKED: git tracks no Markdown file here, nothing checked")\n        return 2\n',
     '        pass\n', ST),
    # check-plan-citations: "disabling the PROSE-LINE refusal" (2026-08-14)
    ('check-plan-citations PROSE-LINE refusal disabled', 'check-plan-citations.py',
     '        if name.endswith(".md"):\n', '        if False:\n', ST),
    # check-plan-citations: "short-circuiting the publication test"
    ('check-plan-citations publication test short-circuited', 'check-plan-citations.py',
     "    return reachable_from(sha, PUBLISHED_REF)\n", "    return True\n", ST),
    # check-plan-citations: a stamp the formatter wrapped inside a blockquote
    # read as no stamp at all -- --restamp refused it and its orphan and
    # publication checks passed in silence (2026-09-04)
    ('check-plan-citations stamp regex blind to a wrapped line', 'check-plan-citations.py',
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
     "        if m or fence:\n", "        if False:\n", ST),
    # heading-outline: a fence closed by one of another kind (heading-outline-03)
    ('heading-outline closes a block with a fence of any kind', 'heading-outline.py',
     "        elif m and m.group(1)[0] == fence[0] and len(m.group(1)) >= len(fence):\n",
     "        elif m:\n", ST),
    # heading-outline: any leading rule taken for frontmatter (heading-outline-04)
    ('heading-outline any leading rule read as frontmatter', 'heading-outline.py',
     "        if lines[i].strip() and not YAML_LINE.match(lines[i]):\n            return 0\n",
     "        if False:\n            return 0\n", ST),
    # check-doc-refs: a fence closed by one of another kind (check-doc-refs-05)
    ('check-doc-refs closes a block with a fence of any kind', 'check-doc-refs.py',
     "        elif m and m.group(1)[0] == fence[0] and len(m.group(1)) >= len(fence):\n",
     "        elif m:\n", ST),
    # check-doc-refs: SIBLING_ROOTS = [] degrades local drift to SKIP (check-doc-refs-06)
    ('check-doc-refs no sibling configured degrades local drift', 'check-doc-refs.py',
     "            if sib_active or not SIBLING_ROOTS:\n", "            if sib_active:\n", ST),
    # check-doc-refs: the self-test dispatched before the move to the root
    # (check-doc-refs-07); judged from the tool's own directory, where the
    # root's judge cannot tell. That defect's symptom IS exit 2, BLOCKED for
    # want of the siblings, which the runner reads as a judge that did not
    # run, so the judge says 2 is its catch
    ('check-doc-refs self-test dispatched before chdir_root', 'check-doc-refs.py',
     '    docs = chdir_root(args)\n    if "--self-test" in sys.argv[1:]:\n        return self_test()\n',
     '    if "--self-test" in sys.argv[1:]:\n        return self_test()\n    docs = chdir_root(args)\n',
     'cd {dir} && python3 {file} --self-test; rc=$?; [ $rc -eq 2 ] && exit 1; exit $rc'),
    # check-doc-examples: the same (check-doc-examples-04)
    ('check-doc-examples self-test dispatched before chdir_root', 'check-doc-examples.py',
     '    docs = chdir_root(args)\n    if "--self-test" in sys.argv[1:]:\n        return self_test()\n',
     '    if "--self-test" in sys.argv[1:]:\n        return self_test()\n    docs = chdir_root(args)\n',
     'cd {dir} && python3 {file} --self-test'),
    # check-plan-citations: CITE_RE blind to json and sh (check-plan-citations-07)
    ('check-plan-citations CITE_RE blind to json and sh', 'check-plan-citations.py',
     '    r"\\.(?:hs|ts|py|c|h|cabal|mjs|html|md|txt|yaml|yml|json|sh)|Makefile)"\n',
     '    r"\\.(?:hs|ts|py|c|h|cabal|mjs|html|md|txt|yaml|yml)|Makefile)"\n', ST),
    # bench-baseline: an unreadable baseline tracebacks at exit 1 again (bench-baseline-03)
    ('bench-baseline unreadable baseline tracebacks instead of exit 2', 'bench-baseline.py',
     '    except OSError as e:\n        usage_error(f"{baseline_path}: cannot be read ({e.strerror})")\n',
     '    except OSError as e:\n        raise\n', ST),
    # check-conv-bench-props: an unreadable collection tracebacks at exit 1 again
    # (check-conv-bench-props-02)
    ('check-conv-bench-props unreadable collection tracebacks instead of exit 2', 'check-conv-bench-props.py',
     '        except (OSError, ValueError, LookupError, TypeError) as e:\n            usage_error(f"{path}: not a readable criterion --json collection"\n                        f" ({type(e).__name__}: {e})")\n',
     '        except (OSError, ValueError, LookupError, TypeError) as e:\n            raise\n', ST),
    # check-doc-wrap: indented code no longer exempt (check-doc-wrap-07)
    ('check-doc-wrap indented code block read as prose', 'check-doc-wrap.py',
     "        elif fence is None and indented and (blank or code):\n", "        elif False:\n", ST),
    # check-doc-wrap: a fence line at any indentation opens or closes a block again
    # (check-doc-wrap-08)
    ('check-doc-wrap indented fence line read as a fence', 'check-doc-wrap.py',
     'FENCE = re.compile(r"^ {0,3}(`{3,}|~{3,})")\n', 'FENCE = re.compile(r"^\\s*(`{3,}|~{3,})")\n', ST),
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
    ('bench-baseline malformed regression tracebacks instead of exit 2', 'bench-baseline.py',
     '                usage_error(f"{p}: the regressions of {name} lack {e}")\n', "                raise\n", ST),
    # check-conv-bench-props: a missing benchmark exits 1 again
    # (check-conv-bench-props-03)
    ('check-conv-bench-props missing benchmark exits 1', 'check-conv-bench-props.py',
     '            usage_error(f"benchmark missing from the JSON (not a full run?): {k}")\n',
     '            sys.exit(f"benchmark missing from the JSON (not a full run?): {k}")\n', ST),
    # check-conv-bench-props: a regression missing a field tracebacks at 1 again
    # (check-conv-bench-props-04)
    ('check-conv-bench-props malformed regression tracebacks instead of exit 2', 'check-conv-bench-props.py',
     '                usage_error(f"{path}: the regressions of {name} lack {e}")\n', "                raise\n", ST),
    # check-doc-refs: a fence line at any indentation opens a block again
    # (check-doc-refs-08)
    ('check-doc-refs indented fence line read as a fence', 'check-doc-refs.py',
     'FENCE_RE = re.compile(r"^ {0,3}(`{3,}|~{3,})")\n', 'FENCE_RE = re.compile(r"^\\s*(`{3,}|~{3,})")\n', ST),
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
    ('heading-outline indented fence line read as a fence', 'heading-outline.py',
     "FENCE = re.compile(r'^ {0,3}(`{3,}|~{3,})')\n", "FENCE = re.compile(r'^\\s*(`{3,}|~{3,})')\n", ST),
    # check-doc-examples: the from-the-root control may agree at exit 2 again
    # (check-doc-examples-05). Judged with README.md aside, where the self-test
    # must FAIL: the judge is that failure, so it passes on the guarded checker
    # and fails on the mutant, which reports PASS over two runs that did not
    # happen. A judge whose setup fails exits 0 and the mutant survives, loudly.
    ('check-doc-examples control passes over two runs that did not happen', 'check-doc-examples.py',
     "    if here.returncode == 2:\n        ok = False\n", "    if False:\n        ok = False\n",
     'cd {dir} && mv ../README.md ../README.md.aside || exit 0; python3 {file} --self-test; rc=$?; '
     'mv ../README.md.aside ../README.md; test $rc -ne 0'),
]
