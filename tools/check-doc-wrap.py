#!/usr/bin/env python3
"""Check that a document is as `wrap80` leaves it, in whichever form it keeps.

Usage: python3 tools/check-doc-wrap.py [DOC ...]
DOC defaults to every document listed below. Run from the repo root.

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
passes. The other branches fire too: an unlisted document is refused
rather than guessed at, and the one-line-per-paragraph half caught a
paragraph in CREDITS.md broken across two lines, which nothing had ever
looked at. Confirmed 2026-08-12.
"""

import difflib
import os
import re
import subprocess
import sys

# Which list a document belongs to cannot be read off its bytes: long lines
# mean badly wrapped or deliberately unwrapped, and nothing says which. So a
# document in neither is refused rather than guessed at, and a new one is
# classified here by hand, once.
WRAPPED = (   # prose reflowed to wrap80's fixed point
    "README.md",
    "CHANGELOG.md",
    "docs/position-effect.md",
)
# One line per paragraph, deliberately: GitHub renders a single newline as
# a hard <br> in an issue or PR body, and a CLAUDE.md is edited the same way
# so that a paragraph is one unit to a reader and to a diff.
UNWRAPPED = (
    "CLAUDE.md",
    "CREDITS.md",
    "bench/CLAUDE.md",
    "test/CLAUDE.md",
    "docs/ghc-issue-block-pool-fragmentation.md",
    "docs/ghc-issue-no-loop-alignment.md",
    "docs/ghc-issue-recompilation-ignores-codegen-flags.md",
)


def check(doc):
    """0 if as wrap80 leaves it or not wrapped, 1 if it needs re-wrapping,
    2 if nothing could be checked -- which `wrap80 -i` would not fix, so the
    summary has to count it apart rather than call it a wrapping failure."""
    rel = os.path.normpath(doc)
    if rel in UNWRAPPED:
        flag, form = ["--unwrap"], "one line per paragraph"
    elif rel in WRAPPED:
        flag, form = [], "wrapped"
    else:
        print(f"FAIL {rel}: not listed as wrapped or as unwrapped —"
              f" classify it in {os.path.basename(__file__)} first")
        return 1
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
    if want == have:
        print(f"ok   {rel}: as wrap80 leaves it, {form}")
        return 0
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
    docs = sys.argv[1:] or list(WRAPPED) + list(UNWRAPPED)
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
