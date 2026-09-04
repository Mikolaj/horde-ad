#!/usr/bin/env python3
"""Diff a benchmark collection against recorded reference figures.

Usage: python3 tools/bench-baseline.py --baseline TSV JSON [JSON ...]
       python3 tools/bench-baseline.py --emit JSON [JSON ...]
       python3 tools/bench-baseline.py --self-test

The JSONs are one collection, collected as tools/check-conv-bench-props.py's
recipe collects them -- criterion --json, --regress allocated:iters and
+RTS -T. --emit writes the rows to stdout instead of diffing, under a
provenance header written by hand, which is how a baseline is regenerated.

--baseline is required and has no default on purpose. The references under
bench/ differ in which orthotope they link and in which suite they cover,
nothing in a criterion JSON records either, and the benchmark names match
across builds -- so a defaulted reference would let a checkout collection be
diffed against a released one and report the whole difference as movement.
Naming it is the only guard there is:

  baseline-convvjp.tsv             convVjpBench   sibling checkout, the diff
  baseline-prod.tsv                shortProdForCI  targets for an ordinary
  baseline-mnist.tsv               shortMnistForCI dev build
  baseline-convvjp-released.tsv    convVjpBench   released orthotope 0.1.8.0
  baseline-prod-released.tsv       shortProdForCI
  baseline-mnist-released.tsv      shortMnistForCI
  baseline-convvjp-2026-08-27.tsv  the preceding checkout build, kept as the
                                   evidence for the regression bench/CLAUDE.md
                                   records, not a diff target

The released three are the anchors that do not move while the orthotope PR
branch churns, and the only ones comparable with CI, which resolves orthotope
from Hackage. Nothing here is specific to convVjpBench: any criterion
collection carrying both regressions is recorded and diffed the same way.

For the two short suites the checkout and released references agree within
tolerance, so crossing them is harmless there -- but that is a measured fact
about this change, not a property of the scheme, and it is the reason those
pairs exist rather than an argument for dropping one.

This answers a different question from the property checker, and the two do
not substitute for each other. The fifteen properties are relations *inside*
a benchmark group, so a whole variant family that shifts together satisfies
every one of them -- orthotope's 2026-08-28 dispatch slowed the handwritten
dInp execution variants 6-18% in allocation with the suite green throughout,
and property 6 passed more easily for it. The properties say the cost model
still holds; this says whether the numbers moved.

Allocation is the instrument. The allocated-vs-iters slope fits at R2
1.000000 across the suite, does not depend on machine load or on which
benchmarks share the process, and moves only when the program does, so the
default 0.5% tolerance is far above its jitter (a few hundred bytes in tens
of megabytes, ~1e-5 relative) and anything it reports is real. Time is
reported alongside but gates nothing: the position effect alone moves a
time slope up to 10% without the program changing at all
(docs/position-effect.md), which is why --time-tol defaults there.

Exit 1 means figures moved, not that anything regressed -- an improvement
trips it just as a regression does, and the direction is in the output. Exit
2 is a usage, input or coverage error: a flag or file that cannot be read, a
collection that is not criterion's or does not partition the suite, or a
benchmark in one side and not the other, which is what a renamed or added
benchmark looks like, and which must be settled by refreshing the baseline
rather than by widening a tolerance.

Refresh a baseline only from a collection taken on a quiet machine,
and in the commit that explains what moved, so the file and the reason for
the move land together.

Non-vacuity, 2026-08-28, on real data rather than perturbed copies -- the
other collections are the live controls. Each of the four baselines is
silent at exit 0 against the collection it was cut from. Against the
preceding checkout build it exits 1 naming most of the suite, eleven past
10% in allocation: the handwritten dInp execution variants at the larger
sizes and all four fused-gather-* variants, the two families having moved
in opposite directions, which is the regression and the lost control
bench/CLAUDE.md records, recovered from the figures alone. That is also why
the output is ordered by magnitude rather than by name: the median mover
across that build change sat under 1% and buried both. Feeding a checkout
collection to the released baseline exits 1 with -90% on the two-gather
chains, which is the mismatched-reference hazard the required --baseline
exists to stop and what it looks like when it happens. Feeding one suite's
collection to another's baseline exits 2 on the coverage guard, as does
omitting --baseline or passing an unknown flag. --self-test (2026-08-28)
covers the rest of the usage table on synthetic collections: no argument
and a flag missing its value exit 2 rather than 1 or a traceback, --emit
round-trips through --baseline at exit 0, a baseline slope of 0
reports movement instead of dividing by it -- --emit used to write
allocation slopes as integers, so a slope under 0.5 became a 0 the next
diff crashed on -- and an unreadable or malformed baseline or collection
exits 2. That the self-test bites is mutants.py's to show.
"""
import json
import os
import subprocess
import sys
import tempfile


def usage_error(msg):
    print(msg, file=sys.stderr)
    sys.exit(2)


def parse_args(args):
    emit = "--emit" in args
    baseline_path = None
    alloc_tol, time_tol = 0.005, 0.10
    rest = []
    i = 0
    while i < len(args):
        a = args[i]
        if a in ("--baseline", "--alloc-tol", "--time-tol"):
            if i + 1 >= len(args):
                usage_error(f"{a} needs a value")
            i += 1
            try:
                if a == "--baseline":
                    baseline_path = args[i]
                elif a == "--alloc-tol":
                    alloc_tol = float(args[i])
                else:
                    time_tol = float(args[i])
            except ValueError:
                usage_error(f"{a} wants a number, not {args[i]!r}")
        elif a == "--emit":
            pass
        elif a.startswith("-"):
            usage_error(f"unknown flag: {a}")
        else:
            rest.append(a)
        i += 1
    if not rest:
        usage_error(__doc__.split("\n\n")[1])
    if not emit and baseline_path is None:
        usage_error(
            "--baseline is required and has no default: the references under"
            " bench/ differ in suite and in which orthotope they link, and"
            " nothing in a criterion JSON says which one a collection is,"
            " so naming the reference is the only guard against diffing"
            " across builds (see this script's docstring)")
    return emit, baseline_path, alloc_tol, time_tol, rest


def read_collection(paths):
    """Slopes by benchmark. Anything that is not a criterion --json
    collection partitioning the suite is a usage error, exit 2: a
    diff never ran, so 1 -- figures moved -- would be a false finding."""
    out = {}
    for p in paths:
        try:
            with open(p) as f:
                reports = json.load(f)[2]
            if not isinstance(reports, list):
                raise TypeError("the third element is not a list of reports")
        except (OSError, ValueError, LookupError, TypeError) as e:
            usage_error(f"{p}: not a readable criterion --json collection"
                        f" ({type(e).__name__}: {e})")
        for r in reports:
            try:
                name = r["reportName"]
                regs = {g["regResponder"]: g
                        for g in r["reportAnalysis"]["anRegress"]}
            except (KeyError, TypeError) as e:
                usage_error(f"{p}: a report without {e} is not criterion's")
            if name in out:
                usage_error(f"benchmark collected twice, the second time in"
                            f" {p} (the files must partition the suite):"
                            f" {name}")
            for want in ("time", "allocated"):
                if want not in regs:
                    usage_error(f"no {want}-vs-iters regression for {name}"
                                f" -- collect with --regress allocated:iters"
                                f" and +RTS -T")
            out[name] = (regs["time"]["regCoeffs"]["iters"]["estPoint"],
                         regs["allocated"]["regCoeffs"]["iters"]["estPoint"])
    return out


def fmt_t(s):
    return f"{s*1e3:.3f}ms" if s < 1 else f"{s:.3f}s"


def rel(new, old):
    """Relative movement; a zero reference moved iff the figure did."""
    if old == 0:
        return 0.0 if new == 0 else float("inf")
    return (new - old) / old


def main(argv):
    emit, baseline_path, alloc_tol, time_tol, rest = parse_args(argv)
    now = read_collection(rest)

    if emit:
        for name in sorted(now):
            t, a = now[name]
            print(f"{name}\t{t:.9g}\t{a:.9g}")
        return 0

    base = {}
    try:
        with open(baseline_path) as f:
            for n, line in enumerate(f, 1):
                if line.startswith("#") or not line.strip():
                    continue
                try:
                    name, t, a = line.rstrip("\n").split("\t")
                    base[name] = (float(t), float(a))
                except ValueError:
                    usage_error(f"{baseline_path}:{n}: not a baseline row"
                                f" (name, time, allocation, tab-separated):"
                                f" {line.rstrip()!r}")
    except OSError as e:
        usage_error(f"{baseline_path}: cannot be read ({e.strerror})")

    missing = sorted(set(base) - set(now))
    added = sorted(set(now) - set(base))
    if missing or added:
        for m in missing:
            print(f"  [C] in {baseline_path}, absent from the collection: {m}")
        for m in added:
            print(f"  [C] in the collection, absent from {baseline_path}: {m}")
        print(f"  refresh {baseline_path} from a full run; a partial"
              f" collection or a renamed benchmark looks exactly like this")
        return 2

    moved = []
    for name in sorted(base):
        bt, ba = base[name]
        nt, na = now[name]
        da = rel(na, ba)
        dt = rel(nt, bt)
        if abs(da) > alloc_tol or abs(dt) > time_tol:
            moved.append((name, bt, nt, dt, ba, na, da))
    # Largest allocation movement first: across a real build change the
    # median mover sits under 1%, so name order buries the few that matter.
    moved.sort(key=lambda m: (-abs(m[6]), -abs(m[3]), m[0]))

    print(f"-- {len(base)} benchmarks against {baseline_path}"
          f" (allocation {alloc_tol*100:g}%, time {time_tol*100:g}%) --")
    for name, bt, nt, dt, ba, na, da in moved:
        flag = "alloc" if abs(da) > alloc_tol else "time "
        print(f"  [{flag}] {name}")
        print(f"          time  {fmt_t(bt)} -> {fmt_t(nt)}  ({dt*100:+.1f}%)"
              f"   alloc {ba/1e6:.2f}MB -> {na/1e6:.2f}MB  ({da*100:+.1f}%)")
    if moved:
        n_alloc = sum(1 for m in moved if abs(m[6]) > alloc_tol)
        print(f"  {len(moved)} moved, {n_alloc} of them in allocation"
              f" -- real movement, not noise; explain it before recording it")
        return 1
    print("  nothing moved beyond tolerance  PASS")
    return 0


def self_test():
    """Synthetic collections for the usage table; the docstring says
    what each row proves."""
    script = os.path.abspath(__file__)
    bad = []

    def run(*argv):
        return subprocess.run([sys.executable, script] + list(argv),
                              capture_output=True, text=True)

    def expect(case, p, code, *needles):
        if p.returncode != code:
            bad.append(f"{case}: exit {p.returncode}, expected {code}"
                       f" ({p.stderr.strip()[-80:]})")
        for n in needles:
            if n not in p.stdout + p.stderr:
                bad.append(f"{case}: output lacks {n!r}")

    def collection(path, benches):
        reps = [{"reportName": n, "reportAnalysis": {"anRegress": [
            {"regResponder": "time",
             "regCoeffs": {"iters": {"estPoint": t}}},
            {"regResponder": "allocated",
             "regCoeffs": {"iters": {"estPoint": a}}}]}}
            for n, (t, a) in benches.items()]
        with open(path, "w") as fh:
            json.dump([None, None, reps], fh)

    with tempfile.TemporaryDirectory() as td:
        a = os.path.join(td, "a.json")
        b = os.path.join(td, "b.json")
        tsv = os.path.join(td, "base.tsv")
        collection(a, {"g/x": (0.001, 0.2), "g/y": (0.002, 4e6)})
        collection(b, {"g/x": (0.001, 3.0), "g/y": (0.002, 4e6)})
        expect("no argument", run(), 2, "Usage")
        expect("flag without value", run(a, "--baseline"), 2, "needs a value")
        expect("non-numeric tolerance", run(a, "--baseline", tsv,
                                            "--alloc-tol", "x"), 2, "number")
        p = run("--emit", a)
        expect("emit", p, 0, "g/x\t0.001\t0.2")
        open(tsv, "w").write("# header\n" + p.stdout)
        expect("round trip", run("--baseline", tsv, a), 0, "PASS")
        expect("small slope moved", run("--baseline", tsv, b), 1, "[alloc] g/x")
        open(tsv, "w").write("g/x\t0.001\t0\ng/y\t0.002\t4e6\n")
        expect("zero reference", run("--baseline", tsv, b), 1, "[alloc] g/x")
        # Inputs that are not what they claim exit 2, not 1: a traceback's
        # exit 1 read as figures moved (bench-baseline-03).
        expect("missing baseline", run("--baseline", tsv + ".no", a), 2,
               "cannot be read")
        open(tsv, "w").write("g/x\t0.001\n")
        expect("malformed baseline row", run("--baseline", tsv, a), 2,
               "not a baseline row")
        open(tsv, "w").write("# header\n" + p.stdout)
        expect("missing collection", run("--baseline", tsv, a + ".no"), 2,
               "not a readable criterion")
        for shape in ("[]", "{}", "[null, null, 5]"):
            open(b, "w").write(shape)
            expect(f"not a collection: {shape}", run("--baseline", tsv, b),
                   2, "not a readable criterion")
        expect("collected twice", run("--baseline", tsv, a, a), 2,
               "collected twice")
        collection(b, {"g/x": (0.001, 0.2), "g/y": (0.002, 4e6)})
        json.dump([None, None, [dict(r, reportAnalysis={"anRegress": [
            r["reportAnalysis"]["anRegress"][0]]})
            for r in json.load(open(b))[2]]], open(b, "w"))
        expect("no allocation regression", run("--baseline", tsv, b), 2,
               "no allocated-vs-iters regression")
    for x in bad:
        print(f"FAIL: {x}")
    if not bad:
        print("ok:   every self-test case behaved as expected")
    return 1 if bad else 0


if __name__ == "__main__":
    if sys.argv[1:] == ["--self-test"]:
        sys.exit(self_test())
    sys.exit(main(sys.argv[1:]))
