"""What several scripts under tools/ share, kept once so a fix lands once.

Imported by its neighbours, never run: each puts its own directory first on
sys.path, which running it does anyway and importing it by path does not.

chdir_root serves the checkers whose configuration is root-relative, and
fence_scan the four that must tell fenced code from prose:
check-doc-examples.py, check-doc-refs.py, check-doc-wrap.py and
heading-outline.py. Each of the four once kept its own fence tracker, and
each tracker was fixed for the same defects separately (check-doc-refs-05,
check-doc-wrap-06, heading-outline-03), one of them never
(check-doc-examples-06).

The criterion reader serves ab-time.py, bench-baseline.py and
check-conv-bench-props.py, which each read a `--json` collection's
regressions against the iteration count. A file that is not such a
collection raises CriterionError, which each turns into its own exit 2, the
run not having happened; so does an estimate that is not a finite number,
criterion writing a NaN as null.
"""

import json
import math
import os
import re
import subprocess

# A fence: three or more backticks or tildes, indented at most three spaces;
# four make the line indented code (check-doc-wrap-08).
FENCE = re.compile(r"^( {0,3})(`{3,}|~{3,})(.*)$")


def chdir_root(paths=()):
    """Run from the repository root whatever the cwd -- the configuration's
    paths are root-relative -- and return PATHS rebased to it. Outside a
    repository nothing moves."""
    # answered dropped-status: an empty top is the failure, and the next line tests it
    top = subprocess.run(["git", "rev-parse", "--show-toplevel"],
                         capture_output=True, text=True).stdout.strip()
    if not top:
        return list(paths)
    paths = [os.path.relpath(os.path.abspath(p), top) for p in paths]
    os.chdir(top)
    return paths


def fence_scan(lines):
    """Each line of a Markdown document with its place in fenced code, as
    (line, kind, info). kind is "open" or "close" on a fence line, "in" on
    a line inside a block, which comes with the opening fence's indentation
    removed, and None outside; info is the opening fence's info string.

    CommonMark's rules: a block closes only on a fence of the same
    character at least as long with nothing after it, so a backtick fence
    shown inside a tilde block is content; a backtick fence's info string
    holds no backtick; and a block never closed runs to the end."""
    fence = indent = info = None
    for line in lines:
        m = FENCE.match(line)
        if fence is None:
            if m and not (m.group(2)[0] == "`" and "`" in m.group(3)):
                fence, indent, info = (m.group(2), len(m.group(1)),
                                       m.group(3).strip())
                yield line, "open", info
            else:
                yield line, None, None
        elif (m and m.group(2)[0] == fence[0]
              and len(m.group(2)) >= len(fence) and not m.group(3).strip()):
            fence = None
            yield line, "close", info
        else:
            yield re.sub(r"^ {0,%d}" % indent, "", line), "in", info


class CriterionError(ValueError):
    """A file that is not a usable criterion --json collection."""


def finite(v):
    """Is v a number, neither NaN nor infinite?"""
    return (isinstance(v, (int, float)) and not isinstance(v, bool)
            and math.isfinite(v))


def criterion_reports(path):
    """[(name, regressions, report)] of the criterion --json collection at
    path, regressions mapping each fitted responder to its regression."""
    try:
        with open(path) as f:
            reports = json.load(f)[2]
        if not isinstance(reports, list):
            raise TypeError("the third element is not a list of reports")
    except (OSError, ValueError, LookupError, TypeError) as e:
        raise CriterionError(f"{path}: not a readable criterion --json"
                             f" collection ({type(e).__name__}: {e})")
    out = []
    for r in reports:
        try:
            name = r["reportName"]
            regs = {g["regResponder"]: g
                    for g in r["reportAnalysis"]["anRegress"]}
        except (KeyError, TypeError) as e:
            raise CriterionError(f"{path}: a report without {e} is not"
                                 f" criterion's")
        out.append((name, regs, r))
    return out


def estimate(path, name, reg, *keys):
    """reg[keys[0]][keys[1]]... of benchmark name's regression, a finite
    number; CriterionError naming what is missing or what is there."""
    v = reg
    try:
        for k in keys:
            v = v[k]
    except (KeyError, TypeError) as e:
        # The regression's own fields, which a guard on the report does
        # not reach (bench-baseline-04, check-conv-bench-props-04).
        raise CriterionError(f"{path}: the regressions of {name} lack {e}")
    if not finite(v):
        raise CriterionError(f"{path}: {name} has {v!r} at"
                             f" {'/'.join(keys)}, not a finite number"
                             f" (criterion writes a NaN as null)")
    return v


def slope(path, name, reg):
    """The finite slope of a regression against the iteration count."""
    return estimate(path, name, reg, "regCoeffs", "iters", "estPoint")
