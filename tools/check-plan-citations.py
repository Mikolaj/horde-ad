#!/usr/bin/env python3
"""Check that file:line citations in a planning document still resolve.

Usage: python3 tools/check-plan-citations.py [DOC ...]
DOC defaults to CLAUDE.md. Runs from anywhere in the repository. --restamp takes one
DOC, since the stamp it writes is that document's own.

For every citation of the form `path/to/File.hs:12` or `File.hs:12-34`
(also .ts, .py, .c, .h, .cabal, .mjs, .html, .md, .txt, .yaml/.yml and
the Makefile --- documents cite each other and the tools), the script
resolves the file, checks the line range exists, and prints the first
cited line so a human can compare it against what the surrounding
sentence claims. A `/.../` component in a cited path is treated as a
wildcard (the document uses it to abbreviate long paths). A citation may
name several lines or ranges, comma-separated with no space
(`Core/OpsConcrete.hs:222,1581`); each member is resolved and printed on
its own line. The no-space rule is what the documents write and keeps
prose ("`Core/OpsConcrete.hs:222`, and the scatter path below") out of
the match.

Exit status is nonzero if any citation is UNRESOLVED (no such file),
AMBIGUOUS (a bare basename matching several files --- qualify it in the
document), OUT-OF-RANGE (the file is shorter than the cited line, the
line is 0, or a range runs backwards), or
PROSE-LINE (the target is a `.md`, whose line numbers move under the
formatter and so cannot be cited at all --- name a phrase or a heading).

Line numbers drift as commits land: after changing a cited file, re-run
this and eyeball the printed snippets; the document header records the
commit its citations were last verified against.

Pinned GitHub permalinks (`https://github.com/.../blob/<commit>/<path>#L12`
or `#L12-L34`) are also checked, against the pinned commit via
`git show <commit>:<path>` --- they never drift, so this catches typos,
wrong ranges and links whose commit or path is not in this repository
(foreign-repo links cannot be verified locally and are reported as
failures).

`git show` proves only that the commit is in *this* clone's object
database, which an unpushed or squashed-away commit is too --- such a link
resolves for one person on one machine and 404s everywhere else. So a
resolved permalink is then required to be an ancestor of PUBLISHED_REF,
and one that is not fails as UNPUBLISHED; if that ref is absent the run
stops (exit 2) rather than degrading to the weaker check, as
check-doc-refs.py does for an unmounted sibling.

The document's own stamp gets the same treatment, split by severity,
because the two states differ in whether they can heal. A stamp naming a
commit that is not an ancestor of HEAD is ORPHANED and fails: a squash or
amend dropped it and nothing but re-verification brings it back. A stamp
naming a commit that is in HEAD but not yet on PUBLISHED_REF only earns a
note: pushing the branch unrewritten makes it true. Both stamps that this
check was written for were orphaned, in documents whose every other pass
was green.

Stamp failures are counted apart from citation failures, and deliberately:
--restamp refuses on a failed citation pass, so folding the stamp verdict
into that count would let an orphaned stamp block the one command that
repairs it. They still both set the exit status. For the same reason
--restamp *writes* an unpublished anchor rather than refusing -- an
orphaned stamp left in place is strictly worse than an unpushed one -- and
prints an advisory naming the push it depends on.

Non-vacuity: run `python3 tools/check-plan-citations.py --self-test`.
It builds a scratch git repository -- files, commits, an origin/master
ref, an unpublished commit -- and a control document holding every
failing kind beside its passing controls, asserts each verdict and the
exact failure count, and then walks --restamp through its refusal table:
the rewrite, the already-current no-op, the unresolved-citation,
dirty-cited-file, no-stamp, two-stamp and no-citation refusals, and the
unpublished-anchor advisory. The AMBIGUOUS kind gets its first live
control there too: two files of one basename under different search
roots, with no copy at the repo root to shadow them. The self-test was
itself proved non-vacuous by breaking the checker in a copy
(2026-08-14): disabling the PROSE-LINE refusal, short-circuiting the
publication test, and disabling the dirty-cited-file refusal each
turned it red, naming exactly the branches broken. Its line-zero,
backwards-range and second-document rows were added 2026-08-28 for
three defects found by review, and reverting each fix in a copy turned
it red on that row alone; the subdirectory row likewise, the search
roots being root-relative and the script now moving there itself.

Two design points the self-test encodes. Its ORPHANED stamp is
`0000000aa`, deliberately: `git merge-base --is-ancestor` fails for an
object not in the database at all, so a well-formed nameless hash drives
the branch and cannot stop driving it, where a real hash's resolvability
rests on a branch or the reflog and expires with them -- the hand-run
controls this replaces died exactly that way, twice: an UNPUBLISHED row
pinned at a commit that a backup branch alone kept resolvable, and the
note branch's live pair (`bench/CLAUDE.md` and `test/CLAUDE.md`, both
stamped `d282ed596`) falling silent the day that commit reached
origin/master. And UNPUBLISHED takes a commit the scratch repository
mints fresh, since the branch is reached only after `git show` succeeds.

The PUBLISHED_REF-absent stop is exercised before the ref is created:
the same permalink document must exit 2 there, and pass once the ref
exists. The stop sits inside the permalink loop, so in a repo whose
documents pin no permalink a bogus PUBLISHED_REF stays silent -- true of
this repo's tracked documents, the pattern `blob/[0-9a-f]{7,40}/`
matching this file and four `.hs` sources but no document, the README's
whole-file pointers being deliberately `blob/master`.

Scope limits, deliberate: prose-style citations ("config.ui.default line
67") are not extracted, nor is a range left dangling from its filename
("`Core/OpsConcrete.hs:222` and `1581`") --- a bare `1581` in backticks is
indistinguishable from any other number, so a document that wants the
second line checked must repeat the filename.

Refuted, and not to be reopened without new evidence: extending that to
the *colon-led* continuation the documents also write ("...hs:182 '...',
:4310, :4487"), which unlike a bare number looks unambiguous. Measured
2026-07-31 over every `.md` here, attaching each `, :NNNN` to the nearest
preceding citation: 33 matches, all in one untracked scratch document and
**none in any tracked one**, so the coverage gain today is zero. Against
that, three of the 33 attach to the wrong file --- `Convert.hs:254` where
the sentence says check-doc-refs.py, `horde-ad.cabal:49-51` and
`BenchProdTools.hs:49-51` where it says this checker's docstring --- and
those files are long enough that all three *resolve*, so the rule would
print `ok` against the wrong file. That is the "a citation that resolves
can still lie" class, manufactured by the checker meant to catch it. No
gap threshold separates the cases either: correct attachments measured
55, 90, 146 and 179 characters, wrong ones 1538, 1633 and 2111, but
`TestConvSimplified.hs:1185-1186` sits at 184 and the ordering gives no
clean cut. Nor is a cut derivable from a bigger corpus: the LambdaHack
copy measured its own correct attachments to 660 characters and its wrong
ones from 2339, where the cut here would fall between 184 and 1538. Two
corpora, two cuts, neither implying the other --- the separation is an
artifact of each document's prose, not a rule to calibrate against.
Repeat the filename.
And the *claims* around citations are not checked
--- in particular, universally-quantified claims ("only X does Y", "exactly
two", "never") must be re-verified by repo-wide grep, not by re-reading
the cited file; that asymmetry is how a real error slipped in once.

The failing kinds each carry a history of having been silently
uncovered, which is why the self-test pins them one by one. NON-SOURCE:
only Haskell and web sources were extracted once, so a citation into a
`.py` or `.yml` file was skipped rather than checked, and a document
citing nothing but those reported a clean zero. CONTINUATION: extraction
took only the first number of a comma-continued citation, which left
seven sub-references unchecked in a LambdaHack planning document while
the run reported a clean count over the rest -- a silent search of
exactly the kind CLAUDE.md's portable notes warn about, invisible in the
exit status by construction. The leading dot: until it was allowed into
CITE_RE, `.hlint.yaml:22` was extracted as `hlint.yaml` and reported
UNRESOLVED, which from the outside read as a document being unable to
cite a dotfile at all. PROSE-LINE fires on a line that resolves as
readily as on one that does not -- the number is unstable rather than
wrong, so there is nothing for a passing resolution to mean. And
extracted citations are deduplicated, so the self-test's plain
out-of-range row and its continuation tail collapse into one report --
asserted there, so the collapse cannot silently widen.

The permalink rows depend on the order the checks run in, which is worth
knowing before either is edited: OUT-OF-RANGE is tested before
publication, so a range row fails as a range even when its commit is also
unpublished. Give the range row a commit that happens to be unpublished
and the two rows still report distinctly; swap the two checks and the
range row silently starts proving the publication branch instead, with
nothing in the output to say so.

A document carrying more than one stamp is quoting other documents'
stamps rather than making a claim about its own tree -- a findings or
handover document does -- so none of them is checked and a note says so.
That is the precondition --restamp already enforces ("no stamp, or two
stamps -> refuses"), so the two halves of the script agree on what counts
as this document's stamp. Until 2026-07-31 the plain pass failed such a
document three times over, on hashes it was merely reporting as dead.

Passing --restamp rewrites the document's own stamp, so the ritual the
documents ask for -- re-run the pass and restamp once the cited code has
moved -- stops depending on memory. The date a stamp carries is the day
the reading was done, not the date of the commit it names; the two are
spelled the same way and mean different things, so this docstring names
commit dates in words. Measured on 2026-07-30, all three stamped
documents naming `179de634e`, a commit of four days earlier:
`test/CLAUDE.md` was stale, its cited `horde-ad.cabal` having changed in
`2dc4f8783`; `CLAUDE.md`'s six cited files were last touched three days
*before* its stamp, by `fa508caa4`, so it named a tree its citations do
not come from either; and `bench/CLAUDE.md` cites no line at all, which
the flag refuses rather than guesses at (last row below). `179de634e`
and `2dc4f8783` are pre-squash hashes, unresolvable in this history --
kept because the measurement happened at them, and because what they now
demonstrate is the very defect the publication test above was added for.
`2dc4f8783`'s content survives as `8c6367789`. (`bench/CLAUDE.md` has
since been given one line citation exactly so that this flag can
maintain its stamp, which a hand-written one twice failed to survive.)

The commit it writes is not HEAD but the newest commit touching anything
the document cites. That referent is the one that survives editing the
document: a commit carrying only prose touches no cited file, so amending
or replaying it cannot move the answer, whereas a HEAD-based stamp is
falsified by the very commit that records it. It also means the stamp can
name a commit well behind HEAD -- correctly, because the cited lines come
from there, and re-verification is owed when *they* move, not when
anything moves. A restamp belongs in a commit touching only `.md` files:
such a commit can touch no citable file -- a `.md` target is refused as
PROSE-LINE -- so it cannot itself become the newest commit touching
anything cited and stale the stamp it writes, where a commit editing
both the document and a cited file is the one whose amending or
squashing orphans its own stamp.

What the flag cannot do is know that you *read* the document. The stamp
asserts two things -- that the citations resolve in some named tree, and
that they still say what the surrounding claims need -- and only the
first is mechanical. So restamp a document you have just re-read, not one
you have merely run this over; that asymmetry is why the flag is opt-in
rather than the default.

It refuses to write when anything is off, and the refusals are the point:

    a stale stamp, clean tree, clean pass  -> hash and date rewritten, 0
    the same run again                     -> "already current", no write, 0
    one unresolved citation                -> refuses, file untouched, 1
    a cited file modified against HEAD     -> refuses, file untouched, 1
    no stamp, or two stamps                -> refuses, file untouched, 1
    a stamp but no file:line citation      -> refuses, file untouched, 1
    the anchor it would write is unpushed  -> writes, plus an advisory, 0

The last row is not a refusal and belongs in the table anyway: an
orphaned stamp left in place is strictly worse than an unpushed one, so
the flag writes and says what the result depends on. Leaving it out
described the script as refusing in a case where it does not.

The dirty-cited-file refusal is the subtle one: with a cited file
modified, the pass verified the working tree, and no commit hash names
what was checked, so a stamp would be a false statement rather than a
stale one.

The --restamp rows are the self-test's too, one scratch document per
refusal; its anchor assertion -- the written hash must be the newest
commit touching the cited file, not HEAD -- is the row that would pass
vacuously under a HEAD-based rule, and its unpublished-anchor row is the
one that writes plus advises. When running any of this by hand instead,
check the exit status without a pipe: `tail` swallows it, which is how a
first run of the hand recipe in the LambdaHack copy read five successes
that were four refusals.

AMBIGUOUS (a bare basename matching several files) needs the scratch
repository, and deliberately: in this tree `test/CLAUDE.md` and
`bench/CLAUDE.md` share the only duplicated basename under the search
roots, and `resolve` returns at its `os.path.exists` check before
reaching the ambiguity branch, so the root `CLAUDE.md` shadows the pair
and `CLAUDE.md:1` resolves ok -- a live row needs a basename duplicated
under the search roots with no copy at the repo root, which the
self-test builds. The two copies of this script differ only in
SEARCH_ROOTS -- and, until a LambdaHack session syncs it, in the
--self-test added 2026-08-14; `tools/check-twin-sync.py` compares them
whenever both checkouts are mounted.
"""

import datetime
import os
import re
import shutil
import subprocess
import sys
import tempfile

SEARCH_ROOTS = ["src", "test", "bench", "example", "tools", ".github", "."]
# The ref a pinned commit has to be reachable from to count as published.
# `git show` is an object-database lookup with no reachability requirement,
# so without this a link or stamp naming an unpushed or squashed-away
# commit resolves here and nowhere else.
PUBLISHED_REF = "origin/master"


def chdir_root(paths):
    """Run from the repository root whatever the cwd -- the configuration's
    paths are root-relative -- and return PATHS rebased to it. Outside a
    repository nothing moves."""
    # answered dropped-status: an empty top is the failure, and the next line tests it
    top = subprocess.run(["git", "rev-parse", "--show-toplevel"],
                         capture_output=True, text=True).stdout.strip()
    if not top:
        return paths
    paths = [os.path.relpath(os.path.abspath(p), top) for p in paths]
    os.chdir(top)
    return paths

CITE_RE = re.compile(
    r"`?(\.?[A-Za-z][A-Za-z0-9_./-]*"
    r"\.(?:hs|ts|py|c|h|cabal|mjs|html|md|txt|yaml|yml)|Makefile)"
    r":(\d+(?:-\d+)?(?:,\d+(?:-\d+)?)*)")
URL_RE = re.compile(
    r"https://github\.com/[\w.-]+/[\w.-]+/blob/([0-9a-f]{7,40})/"
    r"([A-Za-z0-9_./-]+)#L(\d+)(?:-L(\d+))?")
# The document's own stamp, in either shape the documents use: an inline
# `hash` or a blockquoted **hash**, always followed by an ISO date in
# parentheses. The date is what keeps this from matching the other commit
# hashes documents mention (a bug's commit, a baseline's commit).
STAMP_RE = re.compile(
    r"(verified against[^`*]{0,120}?commit\s*>?\s*(?:`|\*\*))"
    r"([0-9a-f]{7,40})"
    r"((?:`|\*\*)\s*\()(\d{4}-\d{2}-\d{2})(\))")


def spans(spec):
    """Expand a citation's line spec into (lo, hi) pairs.

    A spec is one or more lines or ranges, comma-separated:
    "353", "377-381", "119,1271,1359", "353,362,771-781".
    """
    out = []
    for part in spec.split(","):
        lo, _, hi = part.partition("-")
        out.append((int(lo), int(hi or lo)))
    return out


def reachable_from(sha, ref):
    """Is sha an ancestor of ref? None if ref does not exist here."""
    if subprocess.run(["git", "rev-parse", "--verify", "--quiet",
                       f"{ref}^{{commit}}"], capture_output=True).returncode:
        return None
    return subprocess.run(["git", "merge-base", "--is-ancestor", sha, ref],
                          capture_output=True).returncode == 0


def published(sha):
    """Is sha reachable from PUBLISHED_REF? None if that ref is absent."""
    return reachable_from(sha, PUBLISHED_REF)


def all_files_named(basename):
    # answered dropped-status: the find's failure is an empty listing, and
    # an empty listing is what the caller reports
    out = subprocess.run(
        ["bash", "-c",
         "find " + " ".join(SEARCH_ROOTS[:-1])
         + f" -name {basename} 2>/dev/null; ls {basename} 2>/dev/null"],
        capture_output=True, text=True).stdout.split()
    return sorted(set(out))


def resolve(name):
    """Return (path, error) --- exactly one of the two is None."""
    if "/.../" in name:
        prefix, suffix = name.split("/.../", 1)
        hits = [h for h in all_files_named(os.path.basename(name))
                if h.startswith(prefix) and h.endswith("/" + suffix)]
        if len(hits) == 1:
            return hits[0], None
        return None, f"wildcard resolves to {hits or 'nothing'}"
    if os.path.exists(name):
        return name, None
    hits = [h for h in all_files_named(os.path.basename(name))
            if h.endswith("/" + name)]
    if len(hits) == 1:
        return hits[0], None
    if not hits:
        return None, "UNRESOLVED"
    return None, f"AMBIGUOUS: {hits} --- qualify the citation"


def require_readable(paths):
    """Exit cleanly on a mistyped name rather than with a traceback.

    Exit 2 means the run did not happen, as distinct from 1, which means
    it ran and found something.
    """
    for p in paths:
        if not os.path.isfile(p):
            print(f"no such document: {p}", file=sys.stderr)
            sys.exit(2)


def restamp(doc, text, cited_paths, failures):
    """Rewrite the document's own stamp to name HEAD. Refuse if unsure.

    Returns the exit status. Writes at most one file, and only when the
    pass was clean, the cited files are unmodified against HEAD (so that
    a commit really is what got checked) and the document holds exactly
    one stamp.
    """
    if failures:
        print(f"\nnot restamping {doc}: {failures} citation(s) failed")
        return 1
    others = sorted({p for p in cited_paths if os.path.abspath(p)
                     != os.path.abspath(doc)})
    if others:
        # --porcelain, never colourised, unlike --short. A status that
        # could not be read is not a clean one: its empty output used to
        # read as no dirty file and the stamp was rewritten over a tree
        # nobody had compared to HEAD (check-plan-citations-05).
        p = subprocess.run(["git", "status", "--porcelain", "--"] + others,
                           capture_output=True, text=True)
        if p.returncode != 0:
            print(f"\nnot restamping {doc}: git status could not be read"
                  f" ({p.stderr.strip()[:60] or 'exit ' + str(p.returncode)}),"
                  f" so whether the cited files match HEAD is unknown")
            return 2
        dirty = [ln for ln in p.stdout.splitlines() if ln.strip()]
        if dirty:
            print(f"\nnot restamping {doc}: cited files differ from HEAD, so"
                  f" the pass verified the working tree rather than a commit:")
            for ln in dirty:
                print("   " + ln)
            return 1
    stamps = list(STAMP_RE.finditer(text))
    if len(stamps) != 1:
        which = "no stamp" if not stamps else f"{len(stamps)} stamps"
        print(f"\nnot restamping {doc}: {which} found --- a stamp reads"
              f' "verified against ... commit `<hash>` (<date>)"')
        return 1
    if not others:
        print(f"\nnot restamping {doc}: no file:line citations, so no commit"
              f" to name")
        return 1
    # The stamp names the commit the cited *code* comes from, not HEAD: the
    # newest commit touching anything the document cites. That is what makes
    # it survive amending or replaying the commit that carries the document,
    # which touches no cited file and so cannot move the answer.
    # answered dropped-status: an empty anchor is the failure, refused below
    anchor = subprocess.run(
        ["git", "log", "-1", "--format=%h", "--abbrev=9", "--"] + others,
        capture_output=True, text=True).stdout.strip()
    if not anchor:
        print(f"\nnot restamping {doc}: no commit in history touches its"
              f" cited files")
        return 1
    today = datetime.date.today().isoformat()
    m = stamps[0]
    if (m.group(2), m.group(4)) == (anchor, today):
        print(f"\n{doc}: stamp already names {anchor} ({today}) --- unchanged")
        return 0
    open(doc, "w", encoding="utf-8").write(
        text[:m.start()] + m.group(1) + anchor + m.group(3) + today
        + m.group(5) + text[m.end():])
    print(f"\n{doc}: stamp {m.group(2)} ({m.group(4)})"
          f" -> {anchor} ({today})")
    # Written, not refused: leaving an orphaned stamp in place would be
    # strictly worse than naming a commit that is merely unpushed. But the
    # unpushed state is exactly what a later squash turns into an orphan,
    # so it is said every time rather than left to be remembered.
    if published(anchor) is False:
        print(f"  advisory: {anchor} is not on {PUBLISHED_REF}. Push this"
              f" branch without rewriting that commit, or re-run --restamp"
              f" after the push; a squash before it orphans the stamp.")
    return 0


def self_test():
    """Scratch-repository controls for every failing kind and the restamp
    table. Subprocess-driven: each case runs this script itself from the
    scratch repo, so extraction, resolution, git and the exit status are
    all the real thing. The module docstring records what each case
    proves."""
    if not shutil.which("git"):
        print("BLOCKED: git not on PATH, self-test did not run")
        return 2
    script = os.path.abspath(__file__)
    prev = os.getcwd()
    bad = []

    def expect(case, got, want):
        if got != want:
            bad.append(f"{case}: got {got!r}, expected {want!r}")

    def contains(case, out, *needles):
        for n in needles:
            if n not in out:
                bad.append(f"{case}: output lacks {n!r}")

    def run(*argv, cwd=None, env=None):
        return subprocess.run([sys.executable, script] + list(argv),
                              capture_output=True, text=True, cwd=cwd,
                              env=env)

    with tempfile.TemporaryDirectory() as td:
        os.chdir(td)
        try:
            def git(*a):
                subprocess.run(["git"] + list(a), check=True,
                               capture_output=True)
            git("init", "-q")
            git("config", "user.email", "t@t")
            git("config", "user.name", "t")
            git("config", "commit.gpgsign", "false")
            open("a.hs", "w").write("line one\nline two\nline three\n")
            os.makedirs("sub")
            open("sub/b.py", "w").write("print(1)\n")
            open("note.md", "w").write("prose\n")
            open(".dot.yaml", "w").write("key: value\n")
            os.makedirs("test")
            os.makedirs("tools")
            open("test/Dup.hs", "w").write("dup\n")
            open("tools/Dup.hs", "w").write("dup\n")
            git("add", "-A")
            git("commit", "-qm", "c1")
            c1 = subprocess.run(["git", "rev-parse", "HEAD"],
                                capture_output=True, text=True,
                                check=True).stdout.strip()
            url = "https://github.com/x/y/blob/%s/a.hs"

            open("stop.md", "w").write("Link %s#L1 pinned.\n" % (url % c1))
            p = run("stop.md")
            expect("PUBLISHED_REF absent stops", p.returncode, 2)

            git("update-ref", "refs/remotes/origin/master", c1)
            open("a.hs", "a").write("line four\n")
            git("commit", "-aqm", "c2")
            c2 = subprocess.run(["git", "rev-parse", "HEAD"],
                                capture_output=True, text=True,
                                check=True).stdout.strip()
            p = run("stop.md")
            expect("same link passes once the ref exists", p.returncode, 0)
            open("ok.md", "w").write("`a.hs:1` fine.\n")
            open("bad.md", "w").write("`a.hs:999999` not.\n")
            p = run("ok.md", "bad.md")
            expect("every named document is checked", p.returncode, 1)
            contains("every named document", p.stdout, "=== bad.md ===",
                     "OUT-OF-RANGE")
            p = run("ok.md", "bad.md", "--restamp")
            expect("restamp takes one document", p.returncode, 2)

            open("doc.md", "w").write(
                "# control\n\n"
                "`a.hs:1` control. `NoSuchFile.hs:12` unresolved.\n"
                "`a.hs:999999` out of range. `sub/b.py:999999` extracted\n"
                "too. `a.hs:0` line zero, `a.hs:3-2` backwards.\n"
                "too. `a.hs:1,999999` continuation tail.\n"
                "`note.md:1` prose line. `Dup.hs:1` ambiguous.\n"
                "`.dot.yaml:1` dotfile control, `.dot.yaml:999999` its"
                " pair.\n"
                "%s#L1 pinned ok. %s#L99999 pinned range.\n"
                "%s#L0 pinned zero. %s#L3-L1 pinned backwards.\n"
                "https://github.com/ghc/ghc/blob/0123456789abcdef01234567"
                "89abcdef01234567/x.hs#L1 foreign.\n"
                "%s#L1-L3 unpublished.\n\n"
                "Citations were verified against the tree at commit"
                " `0000000aa` (2020-01-01).\n"
                % (url % c1, url % c1, url % c1, url % c1, url % c2))
            p = run("doc.md")
            expect("kitchen-sink document fails", p.returncode, 1)
            contains("kitchen-sink document", p.stdout,
                     "UNRESOLVED", "OUT-OF-RANGE", "PROSE-LINE",
                     "AMBIGUOUS", "ORPHANED", "UNPUBLISHED",
                     "not in this repository",
                     "ok   a.hs:1 |", "ok   .dot.yaml:1 |",
                     "a.hs#L1 @", "13 failed", "a.hs:0-0 --- OUT",
                     "a.hs:3-2 --- OUT", "#L0-L0 @", "#L3-L1 @")
            expect("continuation collapses with the plain row",
                   p.stdout.count("a.hs:999999"), 1)
            p = run("../doc.md", cwd="sub")
            expect("same verdict from a subdirectory", p.returncode, 1)
            contains("same verdict from a subdirectory", p.stdout,
                     "13 failed")

            open("two.md", "w").write(
                "`a.hs:1` cited.\n\n"
                "One: citations were verified against the tree at commit"
                " `%s` (2020-01-01).\n"
                "Two: citations were verified against the tree at commit"
                " `%s` (2020-01-02).\n" % (c1, c1))
            p = run("two.md")
            contains("two stamps are quotations", p.stdout, "note 2 stamps")
            expect("two stamps still pass the citations", p.returncode, 0)

            stamped = ("`a.hs:1` cited.\n\nCitations were verified against"
                       " the tree at commit `0000000aa` (2020-01-01).\n")
            open("r.md", "w").write(stamped)
            p = run("r.md", "--restamp")
            expect("restamp rewrites", p.returncode, 0)
            contains("restamp rewrites", p.stdout, "->", "advisory")
            expect("restamp wrote the newest cited-file commit",
                   c2[:9] in open("r.md").read(), True)
            p = run("r.md", "--restamp")
            expect("already current", p.returncode, 0)
            contains("already current", p.stdout, "already names")
            # A git whose status fails, everything else handed to the real
            # one: the restamp must refuse, not read the silence as clean.
            os.makedirs("shim")
            open("shim/git", "w").write(
                '#!/bin/sh\ncase "$*" in *status*) exit 128;; esac\n'
                'exec /usr/bin/git "$@"\n')
            os.chmod("shim/git", 0o755)
            p = run("r.md", "--restamp", env={
                **os.environ, "PATH": os.path.abspath("shim") + os.pathsep
                + os.environ.get("PATH", "")})
            expect("git status failing refuses the restamp", p.returncode, 2)
            contains("git status failing refuses the restamp", p.stdout,
                     "could not be read")

            open("r2.md", "w").write(
                "`NoSuchFile.hs:12` cited.\n\nCitations were verified"
                " against the tree at commit `0000000aa` (2020-01-01).\n")
            p = run("r2.md", "--restamp")
            expect("failed pass refuses", p.returncode, 1)
            contains("failed pass refuses", p.stdout, "not restamping")

            open("a.hs", "a").write("dirty\n")
            open("r3.md", "w").write(stamped)
            p = run("r3.md", "--restamp")
            expect("dirty cited file refuses", p.returncode, 1)
            contains("dirty cited file refuses", p.stdout,
                     "differ from HEAD")
            git("checkout", "--", "a.hs")

            open("r4.md", "w").write("`a.hs:1` cited, no stamp.\n")
            p = run("r4.md", "--restamp")
            expect("no stamp refuses", p.returncode, 1)
            contains("no stamp refuses", p.stdout, "no stamp")

            open("r5.md", "w").write(open("two.md").read())
            p = run("r5.md", "--restamp")
            expect("two stamps refuse", p.returncode, 1)
            contains("two stamps refuse", p.stdout, "2 stamps")

            open("r6.md", "w").write(
                "A stamp but no citation.\n\nCitations were verified"
                " against the tree at commit `0000000aa` (2020-01-01).\n")
            p = run("r6.md", "--restamp")
            expect("no citation refuses", p.returncode, 1)
            contains("no citation refuses", p.stdout,
                     "no file:line citations")
        finally:
            os.chdir(prev)
    for b in bad:
        print(f"FAIL: {b}")
    if not bad:
        print("ok:   every self-test case behaved as expected")
    return 1 if bad else 0


def main():
    flags = {a for a in sys.argv[1:] if a.startswith("--")}
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    unknown = flags - {"--restamp", "--self-test"}
    if unknown:
        print(f"unknown flag(s): {' '.join(sorted(unknown))};"
              f" only --restamp and --self-test are understood",
              file=sys.stderr)
        sys.exit(2)
    if "--self-test" in flags:
        return self_test()
    docs = chdir_root(args) or ["CLAUDE.md"]
    require_readable(docs)
    if "--restamp" in flags and len(docs) > 1:
        print("--restamp takes one document: the stamp it writes is that"
              " document's own", file=sys.stderr)
        sys.exit(2)
    # Every document named is checked. Until 2026-08-28 only the first was,
    # and the rest reported nothing while the run exited 0.
    worst = 0
    for doc in docs:
        if len(docs) > 1:
            print(f"=== {doc} ===")
        worst = max(worst, check(doc, "--restamp" in flags))
    return worst


def check(doc, do_restamp):
    """Check one document; its exit status."""
    text = open(doc, encoding="utf-8").read()
    cites = sorted({(m.group(1),) + span
                    for m in CITE_RE.finditer(text)
                    for span in spans(m.group(2))})
    failures = 0
    for name, lo, hi in cites:
        # A line number into PROSE is not a citation, it is a guess with a
        # colon in it. The formatter rewraps a document whenever it is
        # edited -- and, where a hook restores its committed form, between
        # one session turn and the next -- so every line below the change
        # moves while the cited file's own history records nothing: the
        # stamp cannot go stale, because the cited file was not touched.
        # Cite prose by a phrase or a heading, which survives the reflow;
        # `--para` and every exact-match edit already work that way. This
        # was an unenforced observation in CLAUDE.md until it was found
        # leaning on two separate arguments, one of them added the day the
        # rewrapping hook was.
        if name.endswith(".md"):
            print(f"FAIL {name}:{lo}-{hi} --- PROSE-LINE (a line number into"
                  f" a document does not survive a reflow; cite a phrase or"
                  f" a heading)")
            failures += 1
            continue
        path, err = resolve(name)
        if err:
            print(f"FAIL {name}:{lo}-{hi} --- {err}")
            failures += 1
            continue
        lines = open(path, encoding="utf-8",
                     errors="replace").read().splitlines()
        # Every bound, not only the upper: `:0` indexed the file's last
        # line and a backwards range printed its first as ok.
        if lo < 1 or lo > hi or hi > len(lines):
            print(f"FAIL {name}:{lo}-{hi} --- OUT-OF-RANGE "
                  f"(file has {len(lines)} lines)")
            failures += 1
            continue
        span = f"{lo}" if lo == hi else f"{lo}-{hi}"
        print(f"ok   {name}:{span} | {lines[lo - 1].strip()[:80]}")
    urlcites = sorted({(m.group(1), m.group(2), int(m.group(3)),
                        int(m.group(4) or m.group(3)))
                       for m in URL_RE.finditer(text)})
    for sha, path, lo, hi in urlcites:
        proc = subprocess.run(["git", "show", f"{sha}:{path}"],
                              capture_output=True, text=True)
        if proc.returncode != 0:
            print(f"FAIL {path}#L{lo}-L{hi} @ {sha[:9]} --- commit or path"
                  f" not in this repository")
            failures += 1
            continue
        lines = proc.stdout.splitlines()
        if lo < 1 or lo > hi or hi > len(lines):
            print(f"FAIL {path}#L{lo}-L{hi} @ {sha[:9]} --- OUT-OF-RANGE "
                  f"(file has {len(lines)} lines at that commit)")
            failures += 1
            continue
        pub = published(sha)
        if pub is None:
            print(f"stopping: {PUBLISHED_REF} does not exist here, so"
                  f" whether {sha[:9]} is published cannot be told."
                  f" Fetch it, or set PUBLISHED_REF to the ref this"
                  f" repository publishes from.", file=sys.stderr)
            sys.exit(2)
        if not pub:
            print(f"FAIL {path}#L{lo}-L{hi} @ {sha[:9]} --- UNPUBLISHED"
                  f" (resolves here but is not an ancestor of"
                  f" {PUBLISHED_REF}, so the link 404s for everyone else)")
            failures += 1
            continue
        span = f"L{lo}" if lo == hi else f"L{lo}-L{hi}"
        print(f"ok   {path}#{span} @ {sha[:9]}"
              f" | {lines[lo - 1].strip()[:70]}")
    # Counted apart from citation failures: --restamp is gated on those,
    # and an orphaned stamp is the very thing it repairs, so folding it in
    # would make a bad stamp block its own fix.
    stamp_failures = 0
    found = list(STAMP_RE.finditer(text))
    # Only a document's *own* stamp is checked, and a document has one.
    # Several means it is quoting other documents' stamps -- which a
    # findings or handover document does -- and a quotation is not a claim
    # about this file's tree. This is the same precondition --restamp
    # enforces, so the two agree on what counts as a stamp.
    if len(found) > 1:
        print(f"note {len(found)} stamps found --- quotations, not this"
              f" document's own; none checked")
        found = []
    for m in found:
        sha = m.group(2)
        if reachable_from(sha, "HEAD") is False:
            print(f"FAIL stamp @ {sha[:9]} --- ORPHANED (not an ancestor of"
                  f" HEAD; a squash or amend dropped it, so no clone can"
                  f" resolve the tree this document claims to name)")
            stamp_failures += 1
        elif published(sha) is False:
            print(f"note stamp @ {sha[:9]} --- not on {PUBLISHED_REF} yet;"
                  f" sound only if this branch is pushed without"
                  f" rewriting that commit")
    print(f"\n{len(cites) + len(urlcites)} citations checked,"
          f" {failures} failed"
          f" --- now eyeball the snippets against the document's claims.")
    if do_restamp:
        resolved = [resolve(name)[0] for name, _lo, _hi in cites]
        return restamp(doc, text, [p for p in resolved if p], failures)
    return 1 if failures or stamp_failures else 0


if __name__ == "__main__":
    sys.exit(main())
