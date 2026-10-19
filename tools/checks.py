"""The checks of this repository's tools and documents, run by `check-all tools`.

`{bin}` is the shared bin directory (`~/.claude/bin`), `{root}` this
directory, `tools/`. What is here is the seconds-to-minutes half of
CLAUDE.md's standing checks: this repository's tools' self-tests, the
shared document checkers' self-tests over this repository's own rows, the
two linters over the Python and the shell here, the fresh-draw rule over the
tracked Haskell, the mechanical document passes over every tracked `.md` but
CHANGELOG.md, the defect records in both directions, the source lint and the
mutants. The shared tools in ~/slop/tools are checked there. The Haskell
build, the test suites and hlint stay in CLAUDE.md's list: a build inside a
command meant to run often makes it run rarely.

A linter that cannot be found is a finding and not a skip: a probe decides
and its silence fails the step by name. The reference check is BLOCKED at
exit 2 with a sibling checkout unmounted, and the citation check with a
foreign clone absent or lacking a pinned commit, which check-all reports
as a check that did not happen, never as one that passed.
"""

SCAN = ['.']
TIMEOUT = 3600

# One run of the checker over every document: each takes the list and
# aggregates as check-all does, a failure over a document that could not be
# checked, so no loop re-derives the verdict here -- the loop that did kept
# 0 over a status it did not define (checks-05) and split a name on its
# space (checks-06). What is left to say is that the pass did not happen: a
# root that cannot be entered or a listing with nothing in it, git failing
# among its causes, is 2 with its reason, where it was a loop over nothing
# exiting 0 (checks-03). A status the checkers do not define reaches
# check-all as it is, and anything but 0 and 2 is a failure there.
DOCS = ('cd "{root}/.." || { echo "cannot enter the repository root"; exit 2; }; '
        "readarray -t docs < <(git ls-files '*.md' ':!CHANGELOG.md'); "
        '[ ${#docs[@]} -gt 0 ] || { echo "git lists no tracked Markdown file, or could not be run; nothing checked"; exit 2; }; '
        'python3 ../tools/%s "${docs[@]}"')

STEPS = [
    ('check-conv-bench-props self-test', ['python3', '{root}/check-conv-bench-props.py', '--self-test']),
    ('check-fresh-draws self-test', ['python3', '{root}/check-fresh-draws.py', '--self-test']),
    # The shared checkers over this repository's rows and README.
    ('check-doc-refs self-test', ['python3', '{root}/../../tools/check-doc-refs.py', '--self-test'], '{root}/..'),
    ('check-doc-examples self-test', ['python3', '{root}/../../tools/check-doc-examples.py', '--self-test'], '{root}/..'),
    ('pyflakes', ['bash', '-c',
                  'cd "{root}" && { python3 -m pyflakes --version >/dev/null 2>&1 || { echo "python3 -m pyflakes --version failed, so tools/*.py went unlinted"; exit 1; }; } && python3 -m pyflakes *.py']),
    ('shellcheck', ['bash', '-c',
                    'cd "{root}/.." && { command -v shellcheck >/dev/null || { echo "shellcheck is not on PATH (command -v shellcheck finds nothing), so the shell scripts went unlinted"; exit 1; }; } && files=$(git ls-files "*.sh") && if [ -z "$files" ]; then echo "no tracked shell script; nothing linted"; else shellcheck -S warning -f gcc $files; fi']),
    ('fresh draws',            ['python3', '{root}/check-fresh-draws.py'], '{root}/..'),
    ('doc citations',          ['bash', '-c', DOCS % 'check-plan-citations.py']),
    ('doc refs',               ['bash', '-c', DOCS % 'check-doc-refs.py']),
    ('doc wrap',               ['bash', '-c', DOCS % 'check-doc-wrap.py']),
    ('doc examples',           ['bash', '-c', DOCS % 'check-doc-examples.py']),
    ('records validate',       ['python3', '{bin}/defect-cases.py', '{root}']),
    ('cases, ok direction',    ['python3', '{bin}/defect-run.py', '{root}']),
    ('cases, bug direction',   ['python3', '{bin}/defect-run.py', '--audit', '{root}']),
    ('source lint',            ['python3', '{bin}/defect-lint.py', '{root}']),
    ('selftest mutants',       ['python3', '{bin}/selftest-mutants.py', '{root}']),
]
