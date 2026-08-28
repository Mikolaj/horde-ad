#!/usr/bin/env python3
"""Check that the twin tools here and in the sibling repo have not drifted.

Usage: python3 tools/check-twin-sync.py [--self-test]
Run from the repo root.

The document checkers are kept as twin copies in the repos that adopted
them, identical apart from a per-repo configuration and their docstrings
(the non-vacuity prose and the examples are each repo's own). That claim
had no instrument: a fix landing in one copy only was invisible unless a
session happened to mount both repos and think of diffing them. This is
that diff, mechanized: for every tools/*.py present in both checkouts,
compare everything below the module docstring, with the marked per-repo
configuration block stripped from both sides and, for scripts that
predate the marker, the assignments to the names in CONFIG_NAMES.

TWIN_ROOT names the sibling's tools directory. Absent -- unmounted, or
hidden by the outer wrapper -- the run is BLOCKED with exit 2, the same
ruling as check-doc-refs.py's siblings: an unverified sync must not read
as a passing one. Exit 1 when a shared tool drifts, 0 when none does.
Files present in only one checkout are noted, not failed: a tool can be
legitimately unported.

Scope limits, deliberate: only single-line CONFIG_NAMES assignments are
stripped outside a marker block, so a script that grows a multi-line
config constant should grow the marker block instead; and a drift
verdict names the file, not the hunk -- the fix is to diff the two
copies and port, which no summary replaces.

Non-vacuity: run --self-test. It copies this repo's tools into a scratch
"twin", confirms the identical copies pass, then confirms that a
docstring-only change and a configuration-only change both still pass
while a mutated code line fails. The self-test was itself proved
non-vacuous by breaking the checker in a copy (2026-08-14): a
comparable() that returns the empty string for every script turns the
mutated-code case green and the self-test red.
"""
import ast
import glob
import os
import shutil
import sys
import tempfile

# --- per-repo configuration -----------------------------------------
TWIN_ROOT = "../LambdaHack/tools"
# --- end per-repo configuration --------------------------------------

MARKER_BEGIN = "# --- per-repo configuration"
MARKER_END = "# --- end per-repo configuration"
# Config constants of scripts that predate the marker block.
CONFIG_NAMES = ("SEARCH_ROOTS", "PUBLISHED_REF", "TWIN_ROOT")


def comparable(text):
    """The part of a script the twins must agree on."""
    lines = text.split("\n")
    try:
        tree = ast.parse(text)
    except SyntaxError:
        return text
    body = tree.body
    if (body and isinstance(body[0], ast.Expr)
            and isinstance(body[0].value, ast.Constant)
            and isinstance(body[0].value.value, str)):
        end = body[0].end_lineno
        lines = [""] * end + lines[end:]
    out, in_config = [], False
    for ln in lines:
        s = ln.strip()
        if s.startswith(MARKER_BEGIN):
            in_config = True
            continue
        if s.startswith(MARKER_END):
            in_config = False
            continue
        if in_config:
            continue
        if any(s.startswith(name + " =") or s.startswith(name + "=")
               for name in CONFIG_NAMES):
            continue
        out.append(ln)
    return "\n".join(l for l in out if l.strip())


def compare(root_a, root_b):
    """(drifted, only_a, only_b, same) basename lists for the two roots."""
    a = {os.path.basename(p) for p in glob.glob(os.path.join(root_a, "*.py"))}
    b = {os.path.basename(p) for p in glob.glob(os.path.join(root_b, "*.py"))}
    drifted, same = [], []
    for name in sorted(a & b):
        ta = open(os.path.join(root_a, name), encoding="utf-8").read()
        tb = open(os.path.join(root_b, name), encoding="utf-8").read()
        (drifted if comparable(ta) != comparable(tb) else same).append(name)
    return drifted, sorted(a - b), sorted(b - a), same


def self_test():
    """Scratch-twin controls; the module docstring records what each
    case proves."""
    here = os.path.dirname(os.path.abspath(__file__))
    myself = os.path.basename(__file__)
    bad = []
    with tempfile.TemporaryDirectory() as td:
        twin = os.path.join(td, "tools")
        shutil.copytree(here, twin,
                        ignore=shutil.ignore_patterns("__pycache__"))
        drifted, _, _, same = compare(here, twin)
        if drifted or not same:
            bad.append("identical twin read as drifted: %r" % drifted)
        victim = os.path.join(twin, myself)
        text = open(victim, encoding="utf-8").read()
        open(victim, "w").write(text.replace(
            "Check that the twin tools", "CHANGED docstring words", 1))
        drifted = compare(here, twin)[0]
        if drifted:
            bad.append("docstring-only change read as drift")
        open(victim, "w").write(text.replace(
            'TWIN_ROOT = "../LambdaHack/tools"',
            'TWIN_ROOT = "../horde-ad/tools"', 1))
        drifted = compare(here, twin)[0]
        if drifted:
            bad.append("configuration-only change read as drift")
        open(victim, "w").write(text.replace(
            '"""The part of a script the twins must agree on."""',
            '"""The part of a script the twins must agree on."""'
            '  # mutated', 1))
        drifted = compare(here, twin)[0]
        if myself not in drifted:
            bad.append("a mutated code line was not read as drift")
    for b in bad:
        print("FAIL: %s" % b)
    if not bad:
        print("ok:   every self-test case behaved as expected")
    return 1 if bad else 0


def main():
    if sys.argv[1:] == ["--self-test"]:
        return self_test()
    if sys.argv[1:]:
        print("usage: check-twin-sync.py [--self-test]", file=sys.stderr)
        return 2
    here = os.path.dirname(os.path.abspath(__file__))
    if not os.path.isdir(TWIN_ROOT):
        print(f"BLOCKED --- twin checkout not available: {TWIN_ROOT}")
        print("An unverified sync is not a passing one; mount the checkout"
              " and re-run.")
        return 2
    drifted, only_here, only_twin, same = compare(here, TWIN_ROOT)
    for name in same:
        print(f"ok   {name}: identical below docstring and configuration")
    for name in only_here:
        print(f"note {name}: no copy in {TWIN_ROOT}")
    for name in only_twin:
        print(f"note {name}: only in {TWIN_ROOT}")
    for name in drifted:
        print(f"FAIL {name}: the copies disagree below docstring and"
              f" configuration --- a fix landed in one repo only; diff the"
              f" two and port it")
    print(f"\n{len(drifted)} drifted")
    return 1 if drifted else 0


if __name__ == "__main__":
    sys.exit(main())
