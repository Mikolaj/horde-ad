#!/usr/bin/env python3
"""Check that a document is as `wrap80` leaves it, in whichever form it keeps.

Usage: python3 tools/check-doc-wrap.py [DOC ...]
DOC defaults to every Markdown file git tracks. Run from the repo root.

A document here keeps one of two forms, and both are the formatter's: prose
wrapped to a column limit, or one line per paragraph, which is how a text
bound for a GitHub issue body has to be written since a single newline
renders there as a hard break. Both are fixed points of the same pass, so
both can be asked for, and neither has to be maintained by hand.

This asks for the formatter's output rather than for a width, which is
stronger and cheaper at once. Stronger, because a width sees only the
lines past it: a document left under-wrapped, and a line ending on a
dangling "a" or "the", both pass an "under 80" test and both fail this
one. Cheaper, because the fix is `wrap80 -i DOC` with nothing left to
judge -- where a width invites fixing the offending line, which does not
converge, since shortening one line pushes its last words onto the next.

No width appears here. The number lives in `wrap80` alone, as its name
and its default, so there is nowhere for a second copy to drift from.

Non-vacuous: over `docs/position-effect.md`, each of the three defects
this exists to catch fails it and names a line to look at -- a line
lengthened by hand past the width, the file re-wrapped narrower, and a
break moved so a line ends on "the" -- while the document as committed
passes. The other branches fire too: a document whose committed version
sits at neither fixed point is refused rather than guessed at, and the
one-line-per-paragraph half caught a paragraph in CREDITS.md broken
across two lines, which nothing had ever looked at. The fake-enumerator
branch fires on a planted "2b." and on nothing in any document of these
repos. Confirmed 2026-08-13.

The paragraph rule and the derived form were proven the same day, and the
middle case is the one they exist for. Untouched, position-effect.md is
`ok`. With one paragraph unwrapped -- what one edit leaves -- it is `ok`,
mid-edit, exit 0, where the whole-file test this replaces called that same
file 11 lines wrong and exited 1. With one paragraph rewritten a word per
line it is named, given its line, exit 1. An untracked document is
refused. And the derivation reproduced the two hand-maintained lists it
replaced exactly: the same ten documents, the same three wrapped and seven
one-line-per-paragraph, which is what let the lists go.
"""

import difflib
import os
import re
import subprocess
import sys

# Which form a document keeps cannot be read off its bytes -- long lines mean
# badly wrapped or deliberately unwrapped, and nothing in the file says which
# -- but it CAN be read off its history. The committed version is at whichever
# fixed point the document is kept in, so `git show HEAD:DOC` answers what two
# hand-maintained lists used to, and answers it for a document mid-edit too,
# HEAD being unaffected by the working copy. A document whose committed
# version is at neither fixed point, and one git does not have, are refused
# rather than guessed at, exactly as an unlisted one was.
#
# The lists this replaces named ten documents and had to be added to by hand
# once per new document, in a repo whose CLAUDE.md is itself one of the ten.
# Deriving them reproduced all ten, which is the check that let them go.


def committed_form(rel):
    """("--unwrap" flag, name) for the form DOC's last commit is in, or None.

    None where git has no such file, and where the committed version sits at
    neither fixed point -- someone else's hand-wrapping, or a document nobody
    has run the formatter over yet. Both are refusals rather than guesses.
    """
    p = subprocess.run(["git", "show", "HEAD:" + rel],
                       capture_output=True, text=True)
    if p.returncode != 0:
        return None
    base = p.stdout
    try:
        w = subprocess.run(["wrap80"], input=base, capture_output=True,
                           text=True, check=True).stdout
        u = subprocess.run(["wrap80", "--unwrap"], input=base,
                           capture_output=True, text=True, check=True).stdout
    except (OSError, subprocess.CalledProcessError):
        return None
    if base == w:                      # a short document is at both, and the
        return ([], "wrapped")         # wrapped pass is then a no-op anyway
    if base == u:
        return (["--unwrap"], "one line per paragraph")
    return None


def tracked_markdown():
    """Every Markdown file git has, which is what the lists used to spell."""
    p = subprocess.run(["git", "ls-files", "*.md"],
                       capture_output=True, text=True)
    return p.stdout.split() if p.returncode == 0 else []


# A line that looks like an enumerated item to a writer and is not one to
# Markdown, which wants a bullet or plain digits: "2b.", "iv.", "A.", "a)".
# It renders as a paragraph, so it loses the numbering it was written for and
# the indentation under it stops being a list's, which is a shape this tool
# then declines to touch -- a defect that hid a broken code span in the
# doc-verification skill until it was looked for. Ordinary prose does not
# trip it: over every document in these repos it matched nothing, while a
# plain "1990. The year" is a real list item and is left alone.
FAKE_MARKER = re.compile(r"^\s*(\d+[a-z]|[a-z]|[A-Z]|[ivxlcIVXLC]+)[.)]\s")
REAL_MARKER = re.compile(r"^\s*([-*+]\s|\d{1,9}[.)]\s)")
FENCE = re.compile(r"^\s*(```|~~~)")


def fake_markers(text):
    """[(line number, line)] for enumerators Markdown will not read as such."""
    out, fenced = [], False
    for i, l in enumerate(text.split("\n"), 1):
        if FENCE.match(l):
            fenced = not fenced
        elif not fenced and FAKE_MARKER.match(l) and not REAL_MARKER.match(l):
            out.append((i, l.strip()))
    return out


def check(doc):
    """0 if as wrap80 leaves it or not wrapped, 1 if it needs re-wrapping,
    2 if nothing could be checked -- which `wrap80 -i` would not fix, so the
    summary has to count it apart rather than call it a wrapping failure."""
    rel = os.path.normpath(doc)
    got = committed_form(rel)
    if got is None:
        print(f"FAIL {rel}: its committed version is at neither of wrap80's"
              f" fixed points, or git has no such file, so the form it keeps"
              f" cannot be told — run the formatter over it and commit that")
        return 1
    flag, form = got
    try:
        want = subprocess.run(["wrap80"] + flag + [rel], capture_output=True,
                              text=True, check=True).stdout
    except OSError:
        print(f"BLOCKED {rel}: wrap80 is not on PATH, so nothing was checked")
        return 2
    except subprocess.CalledProcessError as e:
        print(f"BLOCKED {rel}: wrap80 failed ({e.returncode}), nothing checked")
        return 2
    have = open(rel, encoding="utf-8").read()
    fake = fake_markers(have)
    if fake:
        i, l = fake[0]
        print(f"FAIL {rel}: line {i} opens with an enumerator Markdown does not"
              f" read as one — {l[:40]!r}; use a bullet or plain digits"
              + (f" ({len(fake)} such lines)" if len(fake) > 1 else ""))
        return 1
    if want == have:
        print(f"ok   {rel}: as wrap80 leaves it, {form}")
        return 0
    # WHAT IS FORBIDDEN IS HAND-WRAPPING, and that is a property of a
    # PARAGRAPH. Asking the whole file to be exactly as wrap80 leaves it fails
    # a document with one paragraph edited and left long -- which is the state
    # the standing rule asks for, an edit being made at whatever length falls
    # out of it. So this went red on an ordinary edit and the way to green was
    # to wrap; wrapping between edits moves the breaks the next exact-match
    # edit has to quote, so the way on was to unwrap, and the cycle repeated
    # per edit. The pressure was this check, so this is where it is removed.
    #
    # A paragraph mid-edit is one of two innocent things: as wrap80 leaves it,
    # or entirely on one line. Hand-wrapping is neither. Blocks align by index
    # because wrapping never adds or removes a blank line; where they do not,
    # something outside this check's subject moved one and the whole-file
    # comparison below is the honest thing left to report.
    #
    # NO LIVE CONTROL, and named rather than left to look exercised: over
    # the eleven documents of these two repos the counts never differ, and
    # by construction cannot. The branch earns its place because `zip`
    # truncates to the shortest, so without it a mismatch would under-check
    # in silence rather than fall back loudly.
    try:
        flat = subprocess.run(["wrap80", "--unwrap", rel], capture_output=True,
                              text=True, check=True).stdout
    except (OSError, subprocess.CalledProcessError):
        flat = None
    hp, wp, fp = (t.split("\n\n") for t in (have, want, flat or ""))
    if flat is not None and len(hp) == len(wp) == len(fp):
        hand = [i for i, (h, w, f) in enumerate(zip(hp, wp, fp))
                if h != w and h != f]
        loose = sum(1 for h, w, f in zip(hp, wp, fp) if h != w and h == f)
        if not hand:
            print(f"ok   {rel}: no paragraph is hand-wrapped, {form};"
                  f" {loose} still on one line, so it is mid-edit —"
                  f" `wrap80 {' '.join(flag + ['-i', rel])}` before committing")
            return 0
        at = have[:have.index(hp[hand[0]])].count("\n") + 1
        fix = " ".join(["wrap80"] + flag + ["-i", rel])
        print(f"FAIL {rel}: {len(hand)} paragraph(s) are neither as wrap80"
              f" leaves them nor on one line, so they were wrapped by hand,"
              f" {form} — first at line {at}; run `{fix}`")
        return 1
    # Diffed rather than compared by position: one inserted line shifts every
    # line under it, so a position count reports the whole file as changed and
    # hides the one line worth looking at.
    d = list(difflib.unified_diff(have.split("\n"), want.split("\n"),
                                  lineterm="", n=0))
    n = sum(1 for l in d if l[:1] in "+-" and not l.startswith(("---", "+++")))
    at = next((m.group(1) for l in d
               for m in [re.match(r"@@ -(\d+)", l)] if m), "?")
    fix = " ".join(["wrap80"] + flag + ["-i", rel])
    print(f"FAIL {rel}: not as wrap80 leaves it, {form} ({n} line(s), from"
          f" line {at}) — run `{fix}`, never re-wrap a line by hand")
    return 1


def main():
    docs = sys.argv[1:] or tracked_markdown()
    missing = [d for d in docs if not os.path.isfile(d)]
    if missing:
        print(f"no such file: {', '.join(missing)} (run from the repo root)")
        return 2
    results = [check(d) for d in docs]
    bad, blocked = results.count(1), results.count(2)
    print(f"\n{bad} of {len(docs)} document(s) are not as wrap80 leaves them"
          f" — `wrap80 -i DOC` fixes every one of them."
          + (f" {blocked} could not be checked at all." if blocked else ""))
    return 1 if bad or blocked else 0


if __name__ == "__main__":
    sys.exit(main())
