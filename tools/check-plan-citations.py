#!/usr/bin/env python3
"""Check that file:line citations and permalinks in a document still resolve.

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
It is 2 where the run did not happen: a usage error, a document that cannot
be read, no repository to run in, or a --restamp refused.

Line numbers drift as commits land: after changing a cited file, re-run
this and eyeball the printed snippets; the document header records the
commit its citations were last verified against.

Pinned GitHub permalinks (`https://github.com/.../blob/<commit>/<path>#L12`
or `#L12-L34`) are also checked, against the pinned commit via
`git show <commit>:<path>` --- they never drift, so this catches typos,
wrong ranges and links whose commit or path is not in this repository.
This repository is the GitHub one that PUBLISHED_REF's remote names, and
with no GitHub remote every link is taken for this repository's; a link into
another is listed as not checked unless FOREIGN names a clone of it.

`git show` proves only that the commit is in *this* clone's object
database, which an unpushed or squashed-away commit is too --- such a link
resolves for one person on one machine and 404s everywhere else. So a
resolved permalink is then required to be an ancestor of PUBLISHED_REF,
and one that is not fails as UNPUBLISHED; if that ref is absent the
document is BLOCKED (exit 2, unless another document of the run failed)
rather than degraded to the weaker check, as check-doc-refs.py does for
an unmounted sibling.

FOREIGN, in the per-repo block, maps the URL prefix of another repository's
permalinks to a local clone of it, GHC's GitLab to `ghc` here, and such a
link is checked in the clone the same way: a GitLab range reads `#L12-34`, a
link with no line names the whole file, and published means that one of the
clone's remote-tracking refs holds the commit. A clone or a commit missing
here makes the document BLOCKED (exit 2, unless something failed), stderr
saying which is missing. `--foreign=PREFIX=CLONE` adds a mapping for one
run.

A document's links are checked for their own claims too. A `[text][label]`
with no definition renders as plain text and fails. A permalink's link text
shaped like a path must be the end of its URL, and a `#L` one must continue
the file the paragraph's last path-shaped one named. And of the names written
beside a permalink in its clause --- backticked code, a `Note [...]`, a
quotation of twelve characters or more, the link text included --- the
cited file's own path and those the file does not hold as a whole word are
dropped, and one of the rest must occur within NAME_WINDOW lines of the
cited ones or in a definition or Note enclosing them. The drop is what lets
a clause name the program a draft is about, while a link whose lines moved
still fails.

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

Non-vacuity: run `python3 tools/check-plan-citations.py --self-test`. It
builds a scratch git repository -- files, commits, an origin/master ref,
an unpublished commit -- and a control document holding every failing kind
beside its passing controls, asserts each verdict and the exact failure
count, and then walks --restamp through its refusal table: the rewrite, the
already-current no-op, the unresolved-citation, dirty-cited-file, no-stamp,
two-stamp and no-citation refusals, and the unpublished-anchor advisory. A
second scratch repository stands in for a foreign clone, a published commit
and an unpublished one in it, for the FOREIGN and link rows and both BLOCKED
stops. The
AMBIGUOUS kind gets its first live control there too: two files of one basename
under different search roots, with no copy at the repo root to shadow them. Its
line-zero, backwards-range and second-document rows were added for three
defects found by review, and the subdirectory row for a fourth, the search
roots being root-relative and the script now moving there itself. That the
self-test bites is mutants.py's to show.

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
the same permalink document must exit 2 there, a failing document named
after it in the same run must still be checked with the run at 1, and
the permalink must pass once the ref exists. The stop sits inside the
permalink loop, so in a repo whose
documents pin no permalink of its own a bogus PUBLISHED_REF stays silent --
true of this repo's tracked documents, whose pinned links all point into
other repositories, the README's whole-file pointers being deliberately
`blob/master`.

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
self-test builds. The two copies of this script differ only in the
per-repo block; `tools/check-twin-sync.py` compares them whenever both
checkouts are mounted.
"""

import collections
import datetime
import functools
import os
import re
import shutil
import subprocess
import sys
import tempfile

# Beside this file, which a path import (a defect case's unit) leaves off
# sys.path.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common  # noqa: E402

# --- per-repo configuration -----------------------------------------
SEARCH_ROOTS = ["src", "test", "bench", "example", "tools", ".github", "."]
# The ref a pinned commit has to be reachable from to count as published.
# `git show` is an object-database lookup with no reachability requirement,
# so without this a link or stamp naming an unpushed or squashed-away
# commit resolves here and nowhere else.
PUBLISHED_REF = "origin/master"
# Permalinks into another repository that a local clone can check, keyed by
# the URL up to the commit: the clone's path from the root. A commit there
# counts as published when one of the clone's remote-tracking refs holds it.
FOREIGN = {"https://gitlab.haskell.org/ghc/ghc/-/blob/": "ghc"}
# --- end per-repo configuration --------------------------------------
# FOREIGN with this run's --foreign= additions, which main() sets.
FOREIGN_RUN = dict(FOREIGN)

# The extensions are check-doc-refs.py's PATH_EXT: that pass skips every
# backticked `path:NN` token as this one's, so an extension missing here is
# cited by nobody (check-plan-citations-07). Two twin-synced files, so the
# list is written twice and each names the other.
CITE_RE = re.compile(
    r"`?(\.?[A-Za-z][A-Za-z0-9_./-]*"
    r"\.(?:hs|ts|py|c|h|cabal|mjs|html|md|txt|yaml|yml|json|sh)|Makefile)"
    r":(\d+(?:-\d+)?(?:,\d+(?:-\d+)?)*)")
URL_RE = re.compile(
    r"https://github\.com/([\w.-]+/[\w.-]+)/blob/([0-9a-f]{7,40})/"
    r"([A-Za-z0-9_./-]+)#L(\d+)(?:-L(\d+))?")
# A reference definition, `[g1]: URL`, and a link written either way,
# `[text][label]` or `[text](URL)`, one level of brackets allowed inside the
# text; code spans are blanked before the links are looked for.
DEF_RE = re.compile(r"^ {0,3}\[([^\]\n]+)\]:[ \t]*<?([^\s>]+)>?[ \t]*$")
LINK_RE = re.compile(r"\[((?:[^\[\]\n]|\[[^\[\]\n]*\])*)\]"
                     r"(?:\[([^\[\]\n]*)\]|\(([^()\s]+)\))")
CODE_RE = re.compile(r"(`+)(.+?)\1", re.S)
# Link text that names a file and line rather than saying something:
# `compiler/GHC/X.hs#L12`, `X.hs`, `#L40`.
PATHISH_RE = re.compile(r"[A-Za-z0-9_./+-]*(?:#L\d+(?:-L?\d+)?)?")
# The names beside a link that say what its line holds: code, a Note, or a
# quotation of the source.
NAME_RE = re.compile(r"`([^`\n]+)`|Note \[([^\]\n]+)\]|\"([^\"\n]{12,})\"")
IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']{2,}")
# How far from the cited lines a name beside the link may sit.
NAME_WINDOW = 15
# Words of Haskell's own that a code span beside a link holds and that say
# nothing about which line it cites.
KEYWORDS = frozenset(
    "case class data default deriving else forall foreign import infix"
    " infixl infixr instance let module newtype qualified then type where"
    .split())
# The document's own stamp, in either shape the documents use: an inline
# `hash` or a blockquoted **hash**, always followed by an ISO date in
# parentheses. The date is what keeps this from matching the other commit
# hashes documents mention (a bug's commit, a baseline's commit).
# `[\s>]*` wherever the stamp allows a gap, because the formatter may put a
# line break anywhere in it and a break inside a blockquote carries a `>`
# onto the next line. A stamp the wrapper split between the hash and its
# date read as no stamp at all, so --restamp refused a document that had
# one -- and which break lands where moves whenever a paragraph above is
# edited, so this is not a shape any document can be kept in.
STAMP_RE = re.compile(
    # A line break, or a blockquote's >, may fall between the words: one
    # space alone left a stamp so wrapped unread (check-plan-citations-13).
    r"(verified[\s>]+against[^`*]{0,120}?commit[\s>]*(?:`|\*\*))"
    r"([0-9a-f]{7,40})"
    r"((?:`|\*\*)[\s>]*\()(\d{4}-\d{2}-\d{2})(\))")


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


def foreign_res(foreign):
    """One URL pattern per foreign repository: commit, path, and a line or
    range in either host's spelling, GitLab's `#L12-34` or GitHub's
    `#L12-L34`; a link with no line names the whole file."""
    return [(clone, re.compile(re.escape(prefix)
                               + r"([0-9a-f]{7,40})/([^\s#)>\]]+)"
                               r"(?:#L(\d+)(?:-L?(\d+))?)?"))
            for prefix, clone in sorted(foreign.items())]


@functools.lru_cache(maxsize=None)
def is_clone(clone):
    """Is CLONE a git repository here?"""
    return subprocess.run(["git", "-C", clone, "rev-parse", "--git-dir"],
                          capture_output=True).returncode == 0


@functools.lru_cache(maxsize=None)
def blob_lines(clone, sha, path):
    """PATH's lines at SHA in CLONE: None when the commit is not there,
    False when the path is not."""
    if subprocess.run(["git", "-C", clone, "cat-file", "-e",
                       f"{sha}^{{commit}}"], capture_output=True).returncode:
        return None
    p = subprocess.run(["git", "-C", clone, "show", f"{sha}:{path}"],
                       capture_output=True, text=True, errors="replace")
    return p.stdout.splitlines() if p.returncode == 0 else False


Body = collections.namedtuple("Body", "text squashed flat words")
WORD_RE = re.compile(r"[\w']+")


@functools.lru_cache(maxsize=None)
def blob_body(clone, sha, path):
    """PATH's text at SHA in CLONE but its imports: as it is, squashed to
    lower-case letters and digits, with its runs of white space single
    spaces, and as the set of its words. Read once a file, however many
    links cite it."""
    text = "\n".join(ln for ln in blob_lines(clone, sha, path)
                     if not ln.startswith("import "))
    return Body(text, re.sub(r"[^a-z0-9]", "", text.lower()),
                " ".join(text.split()), frozenset(WORD_RE.findall(text)))


@functools.lru_cache(maxsize=None)
def foreign_published(clone, sha):
    """Does one of CLONE's remote-tracking refs hold SHA?"""
    # origin's default branch first: one ancestry test, where the scan below
    # walks every remote ref, which in a GHC clone is seconds a commit.
    if subprocess.run(["git", "-C", clone, "merge-base", "--is-ancestor",
                       sha, "refs/remotes/origin/HEAD"],
                      capture_output=True).returncode == 0:
        return True
    p = subprocess.run(["git", "-C", clone, "for-each-ref", "--count=1",
                        "--contains", sha, "refs/remotes"],
                       capture_output=True, text=True)
    return p.returncode == 0 and bool(p.stdout.strip())


def permalink(url, own, foreign):
    """(clone, sha, path, lo, hi) of a permalink this run checks, "." being
    this repository and lo None for a whole file; None for any other URL."""
    m = URL_RE.match(url)
    if m and (own is None or m.group(1).lower() == own):
        return (".", m.group(2), m.group(3), int(m.group(4)),
                int(m.group(5) or m.group(4)))
    for clone, rx in foreign_res(foreign):
        m = rx.match(url)
        if m:
            lo = int(m.group(3)) if m.group(3) else None
            return (clone, m.group(1), m.group(2), lo,
                    int(m.group(4) or m.group(3)) if lo is not None else None)
    return None


def paragraphs(text):
    """The document's paragraphs outside fenced code."""
    out, cur = [], []
    for line, kind, _info in common.fence_scan(text.split("\n")):
        if kind is None and line.strip():
            cur.append(line)
            continue
        if cur:
            out.append("\n".join(cur))
        cur = []
    if cur:
        out.append("\n".join(cur))
    return out


def norm_label(label):
    """A reference label as Markdown matches it: case and spacing folded."""
    return " ".join(label.split()).lower()


def trailing_end(masked, end, stop):
    """Where the words after a link that are about it end: a parenthesis
    opening right after it, else the clause it closes, up to a `;`, `:` or
    `. `, a parenthesis the link sits in closing, or STOP, the next link."""
    j = end
    while j < stop and masked[j] == " ":
        j += 1
    depth = 0
    for k in range(j, stop):
        ch = masked[k]
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth < 0:
                return k
            if depth == 0 and k > j and masked[j] == "(":
                return k + 1
        elif depth == 0 and (ch in ";:" or masked[k:k + 2] == ". "):
            return k
    return stop


def described(par, masked, uses, i):
    """The text that says what link I points at: its clause before it, back
    to the last `;`, `:` or `. ` since the previous link, and the words after
    it up to trailing_end. Words between two links count for both, the any
    of the check being lenient; a separator keeps a neighbour's clause out."""
    start, end = uses[i][0], uses[i][1]
    nxt = uses[i + 1][0] if i + 1 < len(uses) else len(masked)
    lo = uses[i - 1][1] if i else 0
    cuts = [m.end() for m in re.finditer(r"[;:] |\. ", masked[lo:start])]
    left = lo + (cuts[-1] if cuts else 0)
    return par[left:end] + " " + par[end:trailing_end(masked, end, nxt)]


def indent(ln):
    return len(ln) - len(ln.lstrip(" "))


def enclosing(lines, lo):
    """What names the cited line from above: the header of each definition
    it sits in, local ones included, and the title of the Note it sits in."""
    out = []
    level = indent(lines[lo - 1]) if lines[lo - 1].strip() else 10 ** 6
    for j in range(lo - 2, max(-1, lo - 2 - 400), -1):
        ln = lines[j]
        if ln.strip() and indent(ln) < level and not ln.lstrip().startswith(
                ("--", "{-", "-}", "#", ")", "]", "}", ",", "|", "~")):
            out.append(ln)
            level = indent(ln)
            if level == 0:
                break
    for j in range(lo, min(len(lines), lo + 200)):
        if re.match(r"[a-z_][\w']*\b[^=]*(?:::|=)", lines[j]):
            out.append(lines[j])        # the definition a comment documents
            break
    for j in range(lo - 1, -1, -1):
        if (re.match(r"\s*(?:\{-\s*)?Note \[[^\]]+\]\s*$", lines[j])
                and j + 1 < len(lines)
                and lines[j + 1].strip().startswith("~~~")):
            out.append(lines[j])
            break
    return out


def name_keys(code, note, quote):
    """What to look for in the source for one name beside a link: its
    identifiers of three letters or more, a flag also as the `Opt_` constant
    it sets, a Note's title, a quotation's words; nothing for a name too
    short to tell anything apart."""
    if note:
        return [note]
    if quote:
        return [" ".join(quote.split())]
    m = re.fullmatch(r"-[fdW](?:no-)?([a-z][a-z0-9-]*)(?:=.*)?", code)
    if m:
        return ["flag:" + m.group(1).replace("-", "")]
    return [k for k in IDENT_RE.findall(code) if k not in KEYWORDS]


def word_in(key, body):
    """Is KEY in BODY as a whole identifier, or, a phrase, at all?"""
    if " " in key:
        return key in body.flat
    if not key[0].isalpha() and key[0] != "_":
        return key in body.text
    if WORD_RE.fullmatch(key):
        return key in body.words
    return re.search(r"(?<![\w'])" + re.escape(key) + r"(?![\w'])",
                     body.text) is not None


def names_path(code, path):
    """Is CODE the cited PATH, or its end after a slash? Such a name says
    which file a link cites, not which of its lines."""
    return bool(code) and ("/" + path).endswith("/" + code)


def check_links(text, own, foreign):
    """The links' own claims, apart from where their targets are: every
    label used is defined; a path-like link text is the end of its
    permalink; a `#L` continuation stays in the file its paragraph last
    named; and at least one name beside a permalink occurs near the line it
    cites. Returns the failures."""
    defs = {}
    for line, kind, _info in common.fence_scan(text.split("\n")):
        m = DEF_RE.match(line) if kind is None else None
        if m:
            defs.setdefault(norm_label(m.group(1)), m.group(2))
    failures = 0
    for par in paragraphs(text):
        masked = CODE_RE.sub(lambda m: " " * len(m.group(0)), par)
        uses = []
        for m in LINK_RE.finditer(masked):
            shown = par[m.start(1):m.end(1)]
            url = m.group(3)
            if url is None:
                label = m.group(2) or shown
                url = defs.get(norm_label(label))
                if url is None:
                    print(f"FAIL [{shown}][{m.group(2)}] --- no definition"
                          f" of [{label}], so it renders as plain text")
                    failures += 1
                    continue
            uses.append((m.start(), m.end(), shown, url))
        last = None
        for i, (start, end, shown, url) in enumerate(uses):
            t = permalink(url, own, foreign)
            if t is None:
                continue
            clone, sha, path, lo, hi = t
            if PATHISH_RE.fullmatch(shown) and ("#" in shown or "/" in shown
                                                or "." in shown):
                cut = len(url) - len(shown)
                if not url.endswith(shown) or not (
                        shown.startswith("#") or url[cut - 1] == "/"):
                    print(f"FAIL [{shown}] --- the link text is not the end"
                          f" of its URL, {url}")
                    failures += 1
                if shown.startswith("#"):
                    if last is not None and path != last:
                        print(f"FAIL [{shown}] --- a continuation into {path},"
                              f" where its paragraph last named {last}")
                        failures += 1
                else:
                    last = path
            if lo is None:
                continue
            lines = blob_lines(clone, sha, path)
            if not lines:
                continue                  # reported where the URL is checked
            names = [(name, name_keys(*name)) for name in
                     NAME_RE.findall(described(par, masked, uses, i))
                     if not names_path(name[0], path)]
            # A name the file does not hold, or holds in its imports alone,
            # is about something else, the program a draft describes most
            # often, and says nothing about the line.
            body = blob_body(clone, sha, path)
            names = [(name, [k for k in keys if (
                k[5:] in body.squashed if k.startswith("flag:")
                else word_in(k, body))]) for name, keys in names]
            names = [(name, keys) for name, keys in names if keys]
            if not names:
                continue
            near = "\n".join(lines[max(0, lo - 1 - NAME_WINDOW):
                                   hi + NAME_WINDOW]
                             + enclosing(lines, lo))
            flat = " ".join(near.split())
            squashed = re.sub(r"[^a-z0-9]", "", near.lower())
            # Near is a substring, case folded, where in the file is a whole
            # word: a name passes by sitting anywhere near the line, and
            # leniency there costs only a missed catch.
            folded = flat.lower()
            if not any(k[5:] in squashed if k.startswith("flag:") else
                       k.lower() in folded
                       for _name, keys in names for k in keys):
                said = ", ".join(f"`{c}`" if c else
                                 f"Note [{n}]" if n else f'"{q}"'
                                 for (c, n, q), _keys in names)
                span = f"L{lo}" if lo == hi else f"L{lo}-L{hi}"
                print(f"FAIL {path}#{span} @ {sha[:9]} --- none of {said}"
                      f" beside the link is within {NAME_WINDOW} lines of"
                      f" it")
                failures += 1
    return failures


@functools.lru_cache(maxsize=None)
def all_files_named(basename):
    # One find per basename: per citation it was one per `/.../` or bare
    # name, most of a run's time on a long document (check-plan-citations-08).
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
    # The scratch repository is found by the cwd, by every git call here and
    # every run of this script: an inherited GIT_DIR took the commits to the
    # caller's repository (check-plan-citations-14).
    for k in common.GIT_LOCATION:
        os.environ.pop(k, None)
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

            def head(*a):
                return subprocess.run(["git", *a, "rev-parse", "HEAD"],
                                      capture_output=True, text=True,
                                      check=True).stdout.strip()
            common.scratch_repo()
            git("remote", "add", "origin", "https://github.com/x/y.git")
            open("a.hs", "w").write("line one\nline two\nline three\n")
            os.makedirs("sub")
            open("sub/b.py", "w").write("print(1)\n")
            open("note.md", "w").write("prose\n")
            open(".dot.yaml", "w").write("key: value\n")
            os.makedirs("test")
            os.makedirs("tools")
            open("test/Dup.hs", "w").write("dup\n")
            open("tools/Dup.hs", "w").write("dup\n")
            open("d.json", "w").write("{}\n")
            open("s.sh", "w").write("true\n")
            git("add", "-A")
            git("commit", "-qm", "c1")
            c1 = head()
            url = "https://github.com/x/y/blob/%s/a.hs"

            open("stop.md", "w").write("Link %s#L1 pinned.\n" % (url % c1))
            p = run("stop.md")
            expect("PUBLISHED_REF absent stops", p.returncode, 2)
            open("bad.md", "w").write("`a.hs:999999` not.\n")
            p = run("stop.md", "bad.md")
            expect("a failure outranks the stop", p.returncode, 1)
            contains("a failure outranks the stop", p.stdout + p.stderr,
                     "OUT-OF-RANGE", "does not exist here")

            git("update-ref", "refs/remotes/origin/master", c1)
            open("a.hs", "a").write("line four\n")
            git("commit", "-aqm", "c2")
            c2 = head()
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
                " pair. `d.json:1` and `s.sh:1` are extensions once\n"
                "cited by nobody.\n"
                "%s#L1 pinned ok. %s#L99999 pinned range.\n"
                "%s#L0 pinned zero. %s#L3-L1 pinned backwards.\n"
                "https://github.com/ghc/ghc/blob/0123456789abcdef01234567"
                "89abcdef01234567/x.hs#L1 foreign.\n"
                "https://github.com/x/y/blob/0123456789abcdef01234567"
                "89abcdef01234567/a.hs#L1 own, commit missing.\n"
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
                     "in ghc/ghc, another repository, not checked",
                     "ok   a.hs:1 |", "ok   .dot.yaml:1 |",
                     "ok   d.json:1 |", "ok   s.sh:1 |",
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

            # A stamp the formatter wrapped, inside a blockquote, so that the
            # hash ends one line and the date opens the next behind a `>`.
            # This read as no stamp at all: --restamp refused a document that
            # had one, and the stamp's own orphan and publication checks
            # passed over it in silence. Two of this repo's five stamped
            # documents were in that shape when it was found.
            open("r7.md", "w").write(
                "`a.hs:1` cited.\n\n> Citations were verified against the"
                " tree at commit **0000000aa**\n> (2020-01-01).\n")
            p = run("r7.md", "--restamp")
            expect("wrapped stamp is found", p.returncode, 0)
            contains("wrapped stamp is found", p.stdout, "0000000aa (2020-01-01) ->")
            contains("wrapped stamp is checked", p.stdout, "ORPHANED")
            after = open("r7.md").read()
            if "**\n> (" not in after:
                bad.append("wrapped stamp rewritten without its line break:"
                           f" {after!r}")

            # A foreign repository checked through a local clone, mapped by
            # --foreign= so that these rows run whatever FOREIGN configures:
            # a published commit and a local-only one, one document holding
            # every failing kind beside its passing controls, and the two
            # stops, a commit and a clone missing here.
            src = (["module M where", "", "-- | foo's comment",
                    "foo :: Int", "foo = 1", ""]
                   + ["filler %d" % k for k in range(14)]
                   + ["bar :: Int -> Int", "bar x ="]
                   + ["    + %d" % k for k in range(20)]
                   + ["", "{- Note [Some note]", "~~~~~~~~~~~~~~~~~~",
                      "The note body says hello there."]
                   + ["more note %d" % k for k in range(20)]
                   + ["-}", "", "baz :: Int", "baz = 2"])

            def at(text):
                return src.index(text) + 1

            os.makedirs("fx/src")
            open("fx/src/M.hs", "w").write("\n".join(src) + "\n")
            open("fx/src/N.hs", "w").write("module N where\n")
            open("fx/src/Words.hs", "w").write(
                "alpha = 1\n" + "filler\n" * 19 + "-- Words here\n")

            def fgit(*a):
                git("-C", "fx", *a)
            common.scratch_repo("fx")
            fgit("add", "-A")
            fgit("commit", "-qm", "f1")
            fa = head("-C", "fx")
            fgit("update-ref", "refs/remotes/origin/main", fa)
            open("fx/src/N.hs", "a").write("-- local\n")
            fgit("commit", "-aqm", "f2")
            fb = head("-C", "fx")
            pre = "https://example.org/fx/-/blob/"
            fmap = "--foreign=" + pre + "=fx"
            deep = at("    + 19")
            note = at("more note 19")
            hello = at("The note body says hello there.")
            defs = {"f1": f"{fa}/src/M.hs#L{at('foo :: Int')}",
                    "f2": f"{fa}/src/M.hs",
                    "f3": f"{fa}/src/Nope.hs#L1",
                    "f4": f"{fa}/src/M.hs#L99999",
                    "f5": f"{fb}/src/N.hs#L1",
                    "f6": f"{fa}/src/M.hs#L4-5",
                    "f7": f"{fa}/src/N.hs#L1",
                    "f8": f"{fa}/src/M.hs#L{deep}",
                    "f9": f"{fa}/src/M.hs#L{note}",
                    "fa": f"{fa}/src/M.hs#L{hello}",
                    "fw": f"{fa}/src/Words.hs#L1"}
            open("f.md", "w").write(
                "Ok, `foo` at [src/M.hs#L4][f1]; the file, [src/M.hs][f2];"
                " a GitLab range, [src/M.hs#L4-5][f6] (`foo`).\n\n"
                "A missing path [src/Nope.hs#L1][f3], a range [x][f4],"
                " an unpublished commit [src/N.hs#L1][f5].\n\n"
                "An undefined label [y][nosuch]. Text naming another line,"
                " [src/M.hs#L5][f1].\n\n"
                "[src/M.hs#L4][f1] and then [#L1][f7], into another file.\n\n"
                "A far name: [src/M.hs#L4][f1] (`baz`). A name the file does"
                " not hold says nothing: [src/M.hs#L4][f1] (`Repro`).\n\n"
                "Inside `bar`, [src/M.hs#L%d][f8]; inside Note [Some note],"
                " [src/M.hs#L%d][f9]; quoted, \"says hello there\""
                " [src/M.hs#L%d][fa].\n\n" % (deep, note, hello)
                + "The file's own name, [`src/Words.hs`, line 1][fw].\n\n"
                + "".join(f"[{k}]: {pre}{v}\n" for k, v in defs.items()))
            p = run("f.md", fmap)
            expect("foreign kitchen sink fails", p.returncode, 1)
            contains("foreign kitchen sink", p.stdout,
                     "ok   src/M.hs#L4 @", "ok   src/M.hs @",
                     "ok   src/M.hs#L4-L5 @",
                     "no such path in fx", "OUT-OF-RANGE", "UNPUBLISHED",
                     "no definition of [nosuch]",
                     "[src/M.hs#L5] --- the link text is not the end",
                     "[#L1] --- a continuation into src/N.hs",
                     "none of `baz`", "7 failed")
            for quiet in ("`Repro`", "none of `src/Words.hs`",
                          f"#L{deep} @ {fa[:9]} --- none",
                          f"#L{note} @ {fa[:9]} --- none",
                          f"#L{hello} @ {fa[:9]} --- none"):
                if quiet in p.stdout:
                    bad.append(f"foreign kitchen sink: {quiet!r} reported")
            open("fb.md", "w").write(
                f"[src/M.hs#L1][z]\n\n[z]: {pre}{'0' * 40}/src/M.hs#L1\n")
            p = run("fb.md", fmap)
            expect("a commit missing from the clone blocks", p.returncode, 2)
            contains("a commit missing from the clone blocks", p.stderr,
                     "is not in fx")
            p = run("fb.md", "--foreign=" + pre + "=nowhere")
            expect("a clone missing here blocks", p.returncode, 2)
            contains("a clone missing here blocks", p.stderr,
                     "nowhere is not a git repository")
        finally:
            os.chdir(prev)
    for b in bad:
        print(f"FAIL: {b}")
    if not bad:
        print("ok:   every self-test case behaved as expected")
    return 1 if bad else 0


def main():
    global FOREIGN_RUN
    FOREIGN_RUN = dict(FOREIGN)
    for a in sys.argv[1:]:
        if a.startswith("--foreign="):
            prefix, _, clone = a[len("--foreign="):].partition("=")
            if not prefix or not clone:
                print("--foreign takes PREFIX=CLONE", file=sys.stderr)
                sys.exit(2)
            FOREIGN_RUN[prefix] = clone
    flags = {a for a in sys.argv[1:]
             if a.startswith("--") and not a.startswith("--foreign=")}
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    unknown = flags - {"--restamp", "--self-test"}
    if unknown:
        print(f"unknown flag(s): {' '.join(sorted(unknown))};"
              f" only --restamp, --self-test and --foreign= are understood",
              file=sys.stderr)
        sys.exit(2)
    # From the root before anything, the self-test included, as every
    # checker here does: this one's self-test names no root-relative path,
    # but two siblings' did and reported wrongly from a subdirectory.
    docs = common.chdir_root(args)
    if "--self-test" in flags:
        return self_test()
    docs = docs or ["CLAUDE.md"]
    common.require_readable(docs)
    if "--restamp" in flags and len(docs) > 1:
        print("--restamp takes one document: the stamp it writes is that"
              " document's own", file=sys.stderr)
        sys.exit(2)
    # Every document named is checked. Until 2026-08-28 only the first was,
    # and the rest reported nothing while the run exited 0.
    results = []
    for doc in docs:
        if len(docs) > 1:
            print(f"=== {doc} ===")
        results.append(check(doc, "--restamp" in flags))
    # A failure outranks a document that could not be checked, as
    # check-all aggregates its steps.
    return 1 if 1 in results else (2 if 2 in results else 0)


def check(doc, do_restamp):
    """Check one document; its exit status."""
    text = open(doc, encoding="utf-8").read()
    cites = sorted({(m.group(1),) + span
                    for m in CITE_RE.finditer(text)
                    for span in spans(m.group(2))})
    failures = 0
    blocked = False
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
    urlcites = sorted({(m.group(1).lower(), m.group(2), m.group(3),
                        int(m.group(4)), int(m.group(5) or m.group(4)))
                       for m in URL_RE.finditer(text)})
    # The repository PUBLISHED_REF's remote names; None, no such remote or
    # not on GitHub, leaves every link checked as this repository's.
    own = common.github_repo(PUBLISHED_REF.split("/", 1)[0])
    for slug, sha, path, lo, hi in urlcites:
        if own is not None and slug != own:
            print(f"note {path}#L{lo}-L{hi} @ {sha[:9]} --- in {slug},"
                  f" another repository, not checked")
            continue
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
            # The document's status, not the run's: an exit here folded
            # earlier documents' FAIL verdicts into the stop and left the
            # later ones unchecked (check-plan-citations-09).
            if not blocked:
                print(f"BLOCKED: {PUBLISHED_REF} does not exist here, so"
                      f" whether {sha[:9]} is published cannot be told."
                      f" Fetch it, or set PUBLISHED_REF to the ref this"
                      f" repository publishes from.", file=sys.stderr)
            blocked = True
            continue
        if not pub:
            print(f"FAIL {path}#L{lo}-L{hi} @ {sha[:9]} --- UNPUBLISHED"
                  f" (resolves here but is not an ancestor of"
                  f" {PUBLISHED_REF}, so the link 404s for everyone else)")
            failures += 1
            continue
        span = f"L{lo}" if lo == hi else f"L{lo}-L{hi}"
        print(f"ok   {path}#{span} @ {sha[:9]}"
              f" | {lines[lo - 1].strip()[:70]}")
    # Permalinks into a repository a local clone here can check, by the same
    # verdicts on that clone. A clone or a commit missing here is no verdict
    # on the document, so it blocks rather than fails.
    foreign = sorted({(clone, m.group(1), m.group(2), m.group(3) or "",
                       m.group(4) or m.group(3) or "")
                      for clone, rx in foreign_res(FOREIGN_RUN)
                      for m in rx.finditer(text)})
    absent = collections.Counter()
    for clone, sha, path, lo, hi in foreign:
        where = path + (f"#L{lo}" + (f"-L{hi}" if hi != lo else "")
                        if lo else "")
        if not is_clone(clone):
            absent[(clone, None)] += 1
            continue
        lines = blob_lines(clone, sha, path)
        if lines is None:
            absent[(clone, sha)] += 1
            continue
        if lines is False:
            print(f"FAIL {where} @ {sha[:9]} --- no such path in {clone} at"
                  f" that commit")
            failures += 1
            continue
        lo, hi = (int(lo), int(hi)) if lo else (None, None)
        if lo is not None and (lo < 1 or lo > hi or hi > len(lines)):
            print(f"FAIL {where} @ {sha[:9]} --- OUT-OF-RANGE (file has"
                  f" {len(lines)} lines at that commit)")
            failures += 1
            continue
        if not foreign_published(clone, sha):
            print(f"FAIL {where} @ {sha[:9]} --- UNPUBLISHED (in {clone}, but"
                  f" no remote-tracking ref there holds it, so the link"
                  f" 404s for everyone else)")
            failures += 1
            continue
        print(f"ok   {where} @ {sha[:9]}"
              + (f" | {lines[lo - 1].strip()[:70]}" if lo else
                 f" ({len(lines)} lines)"))
    for (clone, sha), n in sorted(absent.items(), key=str):
        blocked = True
        if sha is None:
            print(f"BLOCKED: {clone} is not a git repository here, so {n}"
                  f" permalink(s) into it were not checked", file=sys.stderr)
        else:
            print(f"BLOCKED: commit {sha[:10]} is not in {clone}, so {n}"
                  f" permalink(s) pinning it were not checked; fetch it,"
                  f" `git -C {clone} fetch origin`, and re-run",
                  file=sys.stderr)
    failures += check_links(text, own, FOREIGN_RUN)
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
    print(f"\n{len(cites) + len(urlcites) + len(foreign)} citations checked,"
          f" {failures} failed"
          f" --- now eyeball the snippets against the document's claims.")
    if do_restamp:
        if blocked and not failures:
            print(f"\nnot restamping {doc}: whether its permalinks are"
                  f" published could not be told")
            return 2
        resolved = [resolve(name)[0] for name, _lo, _hi in cites]
        return restamp(doc, text, [p for p in resolved if p], failures)
    return 1 if failures or stamp_failures else (2 if blocked else 0)


if __name__ == "__main__":
    sys.exit(main())
