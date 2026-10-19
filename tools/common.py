"""What several scripts under tools/ share, kept once so a fix lands once.

Imported by its neighbours, never run: each puts its own directory first on
sys.path, which running it does anyway and importing it by path does not.

chdir_root serves the checkers whose configuration is root-relative;
require_readable the four that kept a copy of it each, check-doc-examples.py,
check-doc-refs.py, check-plan-citations.py and heading-outline.py; and
fence_scan those that must tell fenced code from prose:
check-doc-examples.py, check-doc-refs.py, check-doc-wrap.py,
heading-outline.py and check-plan-citations.py. The first four once kept a
fence tracker each, and each tracker was fixed for the same defects
separately (check-doc-refs-05,
check-doc-wrap-06, heading-outline-03), one of them never
(check-doc-examples-06). headings returns a document's headings, ATX and
Setext, for heading-outline.py and check-doc-refs.py, and blocks tells its
indented code from prose, measured from the content of the innermost list
item, for check-doc-refs.py and check-doc-wrap.py: each had a reader of
its own, and each lacked a case another had (heading-outline-07,
check-doc-refs-14, check-doc-wrap-11).

The criterion reader serves ab-time.py, bench-baseline.py and
check-conv-bench-props.py, which each read a `--json` collection's
regressions against the iteration count. A file that is not such a
collection raises CriterionError, which each turns into its own exit 2, the
run not having happened; so does an estimate that is not a finite number,
criterion writing a NaN as null.

GIT_LOCATION and git_env serve the git calls that must not answer for a
repository the caller set: check-doc-refs.py's, check-plan-citations.py's
into a foreign clone, loop-offsets.py's, pragma-calls.py's,
rewrite-check.py's and rewrite-fold.py's, which name theirs by -C, and
those of the self-tests that build a scratch one, check-doc-wrap.py's,
check-plan-citations.py's and pragma-calls.py's among them. git_out makes
the calls of rewrite-check.py and rewrite-fold.py, and scratch_repo the
scratch repository of check-doc-wrap.py's and check-plan-citations.py's
self-tests. github_repo returns the OWNER/REPO a remote names on GitHub,
by which check-doc-refs.py and check-plan-citations.py tell this
repository's links from others', and unwrapped puts a document's
paragraphs on one line each for both, a phrase a line break splits being
otherwise unread (check-plan-citations-16, -17).
"""

import json
import math
import os
import re
import subprocess
import sys

# Git's location variables. `git -C dir` does not override GIT_DIR, so a git
# call made with one inherited answers for whatever repository the caller
# had set (rewrite-check-13, rewrite-fold-03).
GIT_LOCATION = ("GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_COMMON_DIR",
                "GIT_OBJECT_DIRECTORY", "GIT_ALTERNATE_OBJECT_DIRECTORIES",
                "GIT_NAMESPACE", "GIT_CEILING_DIRECTORIES")


def git_env(**extra):
    """The environment with git's location variables removed, and EXTRA
    set."""
    env = {k: v for k, v in os.environ.items() if k not in GIT_LOCATION}
    env.update(extra)
    return env


def git_out(repo, *args, stdin=None, env=None, error=RuntimeError):
    """git's output in REPO, its bytes kept: decoded with surrogateescape,
    where text mode turned CR LF into LF (rewrite-check-12, rewrite-fold-02)
    and raised on a byte that is not UTF-8 (rewrite-check-10); git_env's
    environment, with ENV set. A git that cannot run, or fails, raises
    ERROR saying so."""
    try:
        r = subprocess.run(
            ["git", "-C", repo] + list(args), capture_output=True,
            input=None if stdin is None
            else stdin.encode("utf-8", "surrogateescape"),
            env=git_env(**(env or {})))
    except OSError as e:
        raise error(f"git {' '.join(args)}: {e}")
    if r.returncode != 0:
        raise error(f"git {' '.join(args)}: "
                    + r.stderr.decode("utf-8", "replace").strip())
    return r.stdout.decode("utf-8", "surrogateescape")


def scratch_repo(where="."):
    """Make WHERE a git repository a self-test can commit to whatever the
    user's configuration: an identity set, and signing off."""
    for args in (["init", "-q"], ["config", "user.email", "t@t"],
                 ["config", "user.name", "t"],
                 ["config", "commit.gpgsign", "false"]):
        subprocess.run(["git", "-C", where] + args, check=True,
                       capture_output=True, env=git_env())


def github_repo(remote):
    """OWNER/REPO, lower-cased, of the GitHub repository REMOTE names; None
    when that remote is absent or not on GitHub."""
    # answered dropped-status: a failed lookup prints no URL, which matches
    # nothing, and each caller handles the None that follows
    url = subprocess.run(["git", "remote", "get-url", remote],
                         capture_output=True, text=True).stdout.strip()
    m = re.search(r"github\.com[:/]([\w.-]+/[\w.-]+?)(?:\.git)?/?$", url)
    return m.group(1).lower() if m else None


def unwrapped(text):
    """(the document with each paragraph on one line, via `wrap80 --unwrap`,
    whether wrap80 ran).

    Shelled out to rather than reimplemented, so that what counts as a
    paragraph here is what counts as one everywhere else: the formatter that
    writes these documents is the only definition worth having. Without
    wrap80 the text is returned as it came, which loses nothing that a
    line-based read did not already lose -- so a caller degrades to that
    read and says so rather than failing.
    """
    try:
        return subprocess.run(["wrap80", "--unwrap"], input=text, text=True,
                              capture_output=True, check=True).stdout, True
    except (OSError, subprocess.CalledProcessError):
        return text, False


# A fence: three or more backticks or tildes, indented at most three spaces;
# four make the line indented code (check-doc-wrap-08).
FENCE = re.compile(r"^( {0,3})(`{3,}|~{3,})(.*)$")


def chdir_root(paths=(), outside=False):
    """Run from the repository root whatever the cwd -- the configuration's
    paths are root-relative -- and return PATHS rebased to it. Outside a
    repository, or with no git to ask, exit 2, the run not happening: where
    nothing moved, check-plan-citations failed each citation of a repository
    file as unresolved, and check-doc-refs under --without-siblings resolved
    no path and exited 0 (check-plan-citations-12, check-doc-refs-12). With
    OUTSIDE, for a checker whose verdict needs no repository, nothing moves
    there instead."""
    # answered dropped-status: an empty top is the failure, and the next line tests it
    try:
        top = subprocess.run(["git", "rev-parse", "--show-toplevel"],
                             capture_output=True, text=True).stdout.strip()
    except OSError:
        top = ""
    if not top:
        if outside:
            return list(paths)
        print("not inside a git repository, or no git on PATH; the paths"
              " this checker reads are root-relative, so nothing was checked",
              file=sys.stderr)
        sys.exit(2)
    paths = [os.path.relpath(os.path.abspath(p), top) for p in paths]
    os.chdir(top)
    return paths


def require_readable(paths):
    """Exit cleanly on a mistyped name, or a document that is not UTF-8,
    rather than with a traceback (check-doc-examples-08,
    check-doc-refs-11, check-plan-citations-11, heading-outline-06).

    Exit 2 means the run did not happen, as distinct from 1, which means
    it ran and found something.
    """
    for p in paths:
        if not os.path.isfile(p):
            print(f"no such document: {p}", file=sys.stderr)
            sys.exit(2)
        try:
            with open(p, encoding="utf-8") as fh:
                fh.read()
        except UnicodeDecodeError as e:
            print(f"not UTF-8: {p} ({e})", file=sys.stderr)
            sys.exit(2)


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


# A heading as CommonMark and GitHub take it: an ATX line indented at most
# three spaces, a closing run of `#` dropped only after a space; or a Setext
# underline of `=` or `-` under a line of paragraph text, which no heading,
# list item, blank line, fence or fenced line is.
ATX_HEADING = re.compile(r" {0,3}(#{1,6})(?:[ \t]+(.*?))?(?:[ \t]+#+)?[ \t]*$")
SETEXT = re.compile(r" {0,3}(=+|-+)[ \t]*$")
# A list item's marker and the spaces after it, its end the item's content
# column; behind five spaces or more the content starts after one, the rest
# opening code inside the item.
LIST_ITEM = re.compile(r" *(?:[-*+]|\d{1,9}[.)])(?: {1,4}(?! )| |$)")


def headings(lines):
    """[(index, level, text)] of the headings of a Markdown document's
    lines, a Setext heading indexed by its text's line. heading-outline
    took no ATX heading indented and check-doc-refs no Setext one, each
    with a reader of its own (heading-outline-07, check-doc-refs-14)."""
    out, prev = [], None
    for i, (line, kind, _) in enumerate(fence_scan(lines)):
        if kind:
            prev = None    # neither a fence nor its contents underlines
            continue
        atx, under = ATX_HEADING.match(line), SETEXT.match(line)
        if atx:
            out.append((i, len(atx.group(1)), atx.group(2) or ""))
        elif under and prev is not None:
            out.append((prev, 1 if under.group(1)[0] == "=" else 2,
                        lines[prev].strip()))
        prev = (i if line.strip() and not atx and not under
                and not LIST_ITEM.match(line) else None)
    return out


def blocks(lines):
    """Each line of a Markdown document as (line, kind, starts): kind is
    fence_scan's on a fence or a fenced line, "code" on a line of an
    indented code block and None elsewhere; starts says the line continues
    no paragraph, the line before it being blank, a heading, a fence line
    or code, or there being none.

    An indented block is taken as CommonMark takes one: four or more
    columns past the content of the innermost list item open there, after
    a blank line, a heading or more such code, never continuing a
    paragraph. Taken at four columns from the margin, a list item's
    paragraph was read as code (check-doc-refs-13, check-doc-wrap-11)."""
    # items: the content columns of the open list items, innermost last;
    # para: the line before continues a paragraph; code: it is code.
    items, para, code = [], False, False
    for line, kind, _ in fence_scan(lines):
        starts = not para
        if kind is not None:
            para = code = False
        elif not line.strip():
            para = False
        else:
            flat = line.expandtabs(4)
            ind = len(flat) - len(flat.lstrip(" "))
            if ind >= (items[-1] if items else 0) + 4 and (code or not para):
                code, kind = True, "code"
            else:
                code = False
                # A marker, a heading or a paragraph's first line closes the
                # items it is not inside; a heading continues no paragraph.
                m = LIST_ITEM.match(flat)
                heading = ATX_HEADING.match(flat)
                if m or heading or not para:
                    while items and items[-1] > ind:
                        items.pop()
                if m:
                    items.append(m.end())
                para = not heading
        yield line, kind, starts


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
