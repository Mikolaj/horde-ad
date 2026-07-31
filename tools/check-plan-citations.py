#!/usr/bin/env python3
"""Check that file:line citations in a planning document still resolve.

Usage: python3 tools/check-plan-citations.py [DOC]
DOC defaults to CLAUDE.md. Run from the repo root.

For every citation of the form `path/to/File.hs:12` or `File.hs:12-34`
(also .ts, .py, .c, .h, .cabal, .mjs, .html, .md, .txt, .yaml/.yml and
the Makefile — documents cite each other and the tools), the script
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
AMBIGUOUS (a bare basename matching several files — qualify it in the
document), or OUT-OF-RANGE (the file is shorter than the cited line).

Line numbers drift as commits land: after changing a cited file, re-run
this and eyeball the printed snippets; the document header records the
commit its citations were last verified against.

Pinned GitHub permalinks (`https://github.com/.../blob/<commit>/<path>#L12`
or `#L12-L34`) are also checked, against the pinned commit via
`git show <commit>:<path>` — they never drift, so this catches typos,
wrong ranges and links whose commit or path is not in this repository
(foreign-repo links cannot be verified locally and are reported as
failures).

`git show` proves only that the commit is in *this* clone's object
database, which an unpushed or squashed-away commit is too — such a link
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

Non-vacuity for these four branches, reproduced 2026-07-31 in this repo:
a scratch document pinning a permalink at `2dc4f8783` (squashed off
master, still held by `backup-pre-squash`, so `git show` resolves it)
reported UNPUBLISHED, exit 1; one stamped `0000000aa` reported ORPHANED,
exit 1. The restamp interaction was proved by repairing a scratch
document stamped the same way: the plain pass fails it, --restamp
rewrites it anyway and prints the advisory, exit 0.

The two rows want different hashes, and deliberately. UNPUBLISHED needs a
commit that resolves, since it is reached only after `git show` succeeds,
so it takes a real one. ORPHANED does not: it asks
`git merge-base --is-ancestor`, which fails for an object that is not in
the database at all, so `0000000aa` -- well-formed and nameless -- drives
it just as well as a real dropped commit and cannot stop driving it.
That row used to name `179de634e`, held by `origin/perf-gather-drafts`
alone; a hash whose resolvability rests on a branch, or on the reflog,
proves the same thing today and becomes unresolvable when the branch goes
or at the next gc, which is how a live row turns vacuous without anyone
touching it.

Only the note branch has a live control: `bench/CLAUDE.md` and
`test/CLAUDE.md` are both stamped `d282ed596`, which is in HEAD but not
an ancestor of origin/master, so every run over either prints the note
and exits 0. It goes away when that commit reaches origin/master, and a
squash before that orphans both stamps instead -- either way this
paragraph then needs a fresh control. ORPHANED needs its scratch
document meanwhile, all three stamps here being reachable from HEAD.

Neither permalink branch has a live control, and neither has the exit-2
stop: no tracked `.md` here carries a pinned `blob/<sha>/` link at all,
the pattern `blob/[0-9a-f]{7,40}/` matching this file and four `.hs`
sources but no document, the README's whole-file pointers being
deliberately `blob/master`. The stop sits inside the permalink loop, so
a bogus PUBLISHED_REF is silent without one: this script copied with
PUBLISHED_REF set to `origin/no-such-ref` exits 0 on CLAUDE.md and 2 on
a scratch document holding one link pinned at the published `e1bd5f5e2`.
That scratch document is the passing control too; the file that played
the part until 2026-07-31, `notes-add-zero-gather.md`, is not in this
tree but on an unmerged branch, so write a fresh one rather than hunt
for it. The exit status was read without a pipe, `tail` swallowing it
being the trap the recipe above records.

Scope limits, deliberate: prose-style citations ("config.ui.default line
67") are not extracted, nor is a range left dangling from its filename
("`Core/OpsConcrete.hs:222` and `1581`") — a bare `1581` in backticks is
indistinguishable from any other number, so a document that wants the
second line checked must repeat the filename.

Refuted, and not to be reopened without new evidence: extending that to
the *colon-led* continuation the documents also write ("…hs:182 '…',
:4310, :4487"), which unlike a bare number looks unambiguous. Measured
2026-07-31 over every `.md` here, attaching each `, :NNNN` to the nearest
preceding citation: 33 matches, all in one untracked scratch document and
**none in any tracked one**, so the coverage gain today is zero. Against
that, three of the 33 attach to the wrong file — `Convert.hs:254` where
the sentence says check-doc-refs.py, `horde-ad.cabal:49-51` and
`BenchProdTools.hs:49-51` where it says this checker's docstring — and
those files are long enough that all three *resolve*, so the rule would
print `ok` against the wrong file. That is the "a citation that resolves
can still lie" class, manufactured by the checker meant to catch it. No
gap threshold separates the cases either: correct attachments measured
55, 90, 146 and 179 characters, wrong ones 1538, 1633 and 2111, but
`TestConvSimplified.hs:1185-1186` sits at 184 and the ordering gives no
clean cut. Nor is a cut derivable from a bigger corpus: the LambdaHack
copy measured its own correct attachments to 660 characters and its wrong
ones from 2339, where the cut here would fall between 184 and 1538. Two
corpora, two cuts, neither implying the other — the separation is an
artifact of each document's prose, not a rule to calibrate against.
Repeat the filename.
And the *claims* around citations are not checked
— in particular, universally-quantified claims ("only X does Y", "exactly
two", "never") must be re-verified by repo-wide grep, not by re-reading
the cited file; that asymmetry is how a real error slipped in once.

Non-vacuity (per CLAUDE.md's "prove a checker non-vacuous"): feed it a
scratch document holding one citation of each failing kind and confirm
all six are reported and the exit status is 1 —

    UNRESOLVED       `NoSuchFile.hs:12`
    OUT-OF-RANGE     `Core/Ast.hs:999999`
    CONTINUATION     `Core/Ops.hs:1,999999` (the tail member must be checked)
    NON-SOURCE       `CLAUDE.md:999999`   (documents and tools cite each other)
    PERMALINK range  .../blob/5f0647baa/CLAUDE.md#L99999
    PERMALINK repo   https://github.com/ghc/ghc/blob/0123456789abcdef/x.hs#L1
    UNPUBLISHED      .../blob/<a commit not on PUBLISHED_REF>/CLAUDE.md#L1-L3
    ORPHANED stamp   a stamp naming a commit not an ancestor of HEAD

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

plus a control that must still pass (`Core/Ast.hs:1`). The two
out-of-range rows name different files deliberately — extracted
citations are deduplicated, so on one file they collapse and the run
reports five. A run reporting fewer than six failures means extraction,
resolution or the `git show` branch has silently stopped covering that
kind. Two rows are there because their
kind was silently uncovered for a while. NON-SOURCE: only Haskell and
web sources were extracted, so a citation into a `.md`, `.py` or `.yml`
file was skipped rather than checked, and a document citing nothing but
those reported a clean zero. CONTINUATION: extraction took only the
first number of a comma-continued citation, which left seven
sub-references unchecked in a LambdaHack planning document while the run
reported a clean count over the rest — a silent search of exactly the
kind CLAUDE.md's portable notes warn about, and invisible in the exit
status by construction. No document here writes such a citation today,
so the scratch recipe is that branch's only control.

Reproduced 2026-07-30: six failures and exit 1, the control resolving to
`Core/Ast.hs`'s first line. A recipe with no date behind it is a claim
like any other.

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
`2dc4f8783`'s content survives as `8c6367789`.

The commit it writes is not HEAD but the newest commit touching anything
the document cites. That referent is the one that survives editing the
document: a commit carrying only prose touches no cited file, so amending
or replaying it cannot move the answer, whereas a HEAD-based stamp is
falsified by the very commit that records it. It also means the stamp can
name a commit well behind HEAD -- correctly, because the cited lines come
from there, and re-verification is owed when *they* move, not when
anything moves.

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

Non-vacuity (per CLAUDE.md's "prove a checker non-vacuous", applied to a
writer rather than a reader): reproduce the six rows above with scratch
documents -- one citing `tools/heading-outline.py:1` with a stamp reading
`0000000aa` (2020-01-01) for the first two rows, one citing
`NoSuchFile.hs:12` for the third, one citing a file you have just touched
for the fourth, two more with zero and two stamps, and one with a stamp
and no citation at all. Check the exit status without a pipe: `tail`
swallows it, which is how a first run of this recipe in the LambdaHack
copy read five successes that were four refusals. Reproduced 2026-07-30:
rows in order 0, 0, 1, 1, 1, 1, with the file rewritten in the first row
only -- and the hash it wrote was the last commit touching
`tools/heading-outline.py`, not HEAD, which is the row that would have
passed vacuously under a HEAD-based rule.

Six failing kinds in the first recipe, seven in the LambdaHack copy,
where the AMBIGUOUS kind (a bare basename matching several files) has a
live row: `LoopM.hs` sits in both `Client/` and `Server/`. Here it has
none -- but not for want of a duplicate basename, as this docstring used
to say. `test/CLAUDE.md` and `bench/CLAUDE.md` are one, and the only one
under the search roots; the reason is that `resolve` returns at its
`os.path.exists` check before reaching the ambiguity branch, so the root
`CLAUDE.md` shadows the pair and `CLAUDE.md:1` resolves ok. A live row
therefore needs a basename duplicated under the search roots with *no*
copy at the repo root; add the row when one appears rather than leaving
the kind untested. The branch itself is reachable, exercised on
2026-07-30 with two scratch files of a novel basename: AMBIGUOUS naming
both paths, exit 1. The two copies otherwise differ only in
SEARCH_ROOTS.
"""

import datetime
import os
import re
import subprocess
import sys

SEARCH_ROOTS = ["src", "test", "bench", "example", "tools", ".github", "."]
# The ref a pinned commit has to be reachable from to count as published.
# `git show` is an object-database lookup with no reachability requirement,
# so without this a link or stamp naming an unpushed or squashed-away
# commit resolves here and nowhere else.
PUBLISHED_REF = "origin/master"
CITE_RE = re.compile(
    r"`?([A-Za-z][A-Za-z0-9_./-]*"
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
    out = subprocess.run(
        ["bash", "-c",
         "find " + " ".join(SEARCH_ROOTS[:-1])
         + f" -name {basename} 2>/dev/null; ls {basename} 2>/dev/null"],
        capture_output=True, text=True).stdout.split()
    return sorted(set(out))


def resolve(name):
    """Return (path, error) — exactly one of the two is None."""
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
    return None, f"AMBIGUOUS: {hits} — qualify the citation"


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
        # --porcelain, never colourised, unlike --short
        dirty = [ln for ln in subprocess.run(
            ["git", "status", "--porcelain", "--"] + others,
            capture_output=True, text=True).stdout.splitlines() if ln.strip()]
        if dirty:
            print(f"\nnot restamping {doc}: cited files differ from HEAD, so"
                  f" the pass verified the working tree rather than a commit:")
            for ln in dirty:
                print("   " + ln)
            return 1
    stamps = list(STAMP_RE.finditer(text))
    if len(stamps) != 1:
        which = "no stamp" if not stamps else f"{len(stamps)} stamps"
        print(f"\nnot restamping {doc}: {which} found — a stamp reads"
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
        print(f"\n{doc}: stamp already names {anchor} ({today}) — unchanged")
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


def main():
    flags = {a for a in sys.argv[1:] if a.startswith("--")}
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    unknown = flags - {"--restamp"}
    if unknown:
        print(f"unknown flag(s): {' '.join(sorted(unknown))};"
              f" only --restamp is understood", file=sys.stderr)
        sys.exit(2)
    doc = args[0] if args else "CLAUDE.md"
    require_readable([doc])
    text = open(doc, encoding="utf-8").read()
    cites = sorted({(m.group(1),) + span
                    for m in CITE_RE.finditer(text)
                    for span in spans(m.group(2))})
    failures = 0
    for name, lo, hi in cites:
        path, err = resolve(name)
        if err:
            print(f"FAIL {name}:{lo}-{hi} — {err}")
            failures += 1
            continue
        lines = open(path, encoding="utf-8",
                     errors="replace").read().splitlines()
        if hi > len(lines):
            print(f"FAIL {name}:{lo}-{hi} — OUT-OF-RANGE "
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
            print(f"FAIL {path}#L{lo}-L{hi} @ {sha[:9]} — commit or path"
                  f" not in this repository")
            failures += 1
            continue
        lines = proc.stdout.splitlines()
        if hi > len(lines):
            print(f"FAIL {path}#L{lo}-L{hi} @ {sha[:9]} — OUT-OF-RANGE "
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
            print(f"FAIL {path}#L{lo}-L{hi} @ {sha[:9]} — UNPUBLISHED"
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
        print(f"note {len(found)} stamps found — quotations, not this"
              f" document's own; none checked")
        found = []
    for m in found:
        sha = m.group(2)
        if reachable_from(sha, "HEAD") is False:
            print(f"FAIL stamp @ {sha[:9]} — ORPHANED (not an ancestor of"
                  f" HEAD; a squash or amend dropped it, so no clone can"
                  f" resolve the tree this document claims to name)")
            stamp_failures += 1
        elif published(sha) is False:
            print(f"note stamp @ {sha[:9]} — not on {PUBLISHED_REF} yet;"
                  f" sound only if this branch is pushed without"
                  f" rewriting that commit")
    print(f"\n{len(cites) + len(urlcites)} citations checked,"
          f" {failures} failed"
          f" — now eyeball the snippets against the document's claims.")
    if "--restamp" in flags:
        resolved = [resolve(name)[0] for name, _lo, _hi in cites]
        return restamp(doc, text, [p for p in resolved if p], failures)
    return 1 if failures or stamp_failures else 0


if __name__ == "__main__":
    sys.exit(main())
