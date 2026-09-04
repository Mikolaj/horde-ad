#!/usr/bin/env python3
"""Verify the numbered properties of bench/ConvVjpBench.hs.

Usage: python3 tools/check-conv-bench-props.py [--allocation-only]
                                              JSON [JSON ...]
       python3 tools/check-conv-bench-props.py --self-test

Every property is checked twice, against two quantities: seconds per
iteration, and bytes allocated per iteration. The same fifteen relations
bound both --- what a rewrite costs in time and what it costs in allocation
are different questions whose answers happen to be bounded alike, so a
divergence between the two passes is itself a finding. Time is checked to
10%, allocation to 5%, allocation carrying no measurement noise.

JSON is criterion's --json output. One full run of the suite (no
benchmark filter) does, collected with a raised time limit and with the
allocation regression asked for:

    cabal bench convVjpBench --enable-optimization \\
      --benchmark-options='-L 90 --regress allocated:iters --json FILE \\
        +RTS -T'

The budget is cnn-24x24's, the only group that needs it, and one run at
it costs 107 benchmarks x 90s, near three hours. Several files are
accepted and merged, which buys almost all of that back: give the long
budget to the groups that need it and let the rest run at the default,
about 30 minutes. Criterion's bare arguments are prefix patterns on the
group/bench path, and these three sets are disjoint (`6x6` does not
match `inp-6x6`, `24x24` does not match `cnn-24x24`):

    cabal bench convVjpBench --enable-optimization --benchmark-options=\\
      '-L 30 --regress allocated:iters --json slow.json 192x192 \\
       inp-192x192 cnn-12x12 gather48 scatter48 +RTS -T'
    cabal bench convVjpBench --enable-optimization --benchmark-options=\\
      '-L 90 --regress allocated:iters --json cnn24.json cnn-24x24 \\
       +RTS -T'
    cabal bench convVjpBench --enable-optimization --benchmark-options=\\
      '--regress allocated:iters --json fast.json 6x6 24x24 48x48 96x96 \\
       inp-6x6 inp-24x24 inp-48x48 inp-96x96 cnn-6x6 pitfalls +RTS -T'
    python3 tools/check-conv-bench-props.py slow.json cnn24.json fast.json

All three carry `--regress allocated:iters` and `+RTS -T`, exactly as
the single-file recipe does: the time limit is the only thing the split
trades away. Omit them and collection still succeeds, but the check
aborts on its first report, the allocation pass having no slope to read.
These commands lacked both flags from 8c6367789, which added the split
and the allocation pass in one go, until 2026-07-30 -- found by reading
the requirement below against the recipe, then demonstrated by deleting
the 37 allocated regressions from a real slow.json: exit 1 on
192x192/S-fullpipe-honest, quoting the hint that names the two flags.

Together the files must partition the suite: a benchmark collected twice
aborts, and one missing from all of them aborts as before. The split must
also not cut across a property. gather48 and scatter48 take the long
budget together only because property 15 compares them, and splitting
them would weigh a converged slope against a ramp-biased one; the slow
set is otherwise just the groups that come up short of samples at the
default limit. cnn-24x24 took a file of its own because -L 30 left it at
eight samples, under the gate below, where -L 90 gave fifteen (measured
2026-08-22); separating it cuts across nothing, every property naming it
staying inside its own group. Since orthotope's toVectorListT rewrites that
group runs ~225ms rather than ~700ms and clears the gate at -L 30 too, at
fifteen (measured 2026-08-28), so its own file is now headroom. Keep it:
the partition fixes each file's roster, and a roster change moves the
numbers through the position effect, so collapsing the split would cost a
re-collection of every figure recorded against this recipe to save about
four minutes.

The times compared are the per-iteration OLS slopes criterion fits over
time against iteration count --- the estimate it prints on its "time"
line. Criterion's --csv output cannot serve here: it carries only the
mean, which every benchmark's warm-up ramp inflates by a per-benchmark
amount that does not cancel between two benchmarks. The raised time
limit is what makes the slope itself trustworthy: the default 5s leaves
a millisecond-scale benchmark too few samples for the ramp to regress
out cleanly.

The properties are stated and explained in the module haddock of
bench/ConvVjpBench.hs --- that list is canonical and this script is its
executable form; keep the two in sync. At tolerance tol, `a == b` stands
for `abs (a - b) <= max a b * tol`, and `a <= b` for `a <= (1 + tol) * b`.

The haddock also explains the categories echoed in the output:
properties 1-3 are accounting, so a failure there means the measurement
itself broke; property 4 records simplifier behavior; properties 5-6
are engine invariants, so a failure is an engine regression; properties
7-15 record the cost model of the current interpreted gather/scatter
kernels and are the ones to re-measure when those kernels change.

--allocation-only checks just the allocation pass, and gates only on the
allocation fit. That is what .github/workflows/lint-and-test-suites.yml
runs on every push, over a default-limit collection of the whole suite:
too short for the time slopes, but allocation is so nearly exact in the
iteration count that even the sparsest-sampled cnn-24x24 benchmarks fit
it at R2 1.000000, so the allocation verdict on such a run is as good as
on an hour-long one. Before the workflow was wired to it, the mode was
checked in CI's own configuration: a default-limit full run on 2026-08-02,
built from cabal.project alone so that orthotope resolved from Hackage as
it does there rather than from the sibling checkout, reported every
allocation fit usable and every property instance passing, the widest
equality gap 0.5% against the 5% tolerance and no inequality above ratio
1.00. The tradeoff is what allocation cannot see --- the
gather-against-scatter time gap being the standing example, ~9-12x against
released orthotope 0.1.8.0, and 1.12x under the checkout's strided-fallback
rewrites that replaced it, by which point gather's fastest orientation is
ahead of scatter (bench/CLAUDE.md).

Dash-arguments other than --allocation-only are refused (exit 2, nothing
checked, as is no argument at all) rather than read as JSON paths --- a mistyped mode flag would
otherwise select the full time+allocation run silently. Confirmed
2026-08-14: --allocation-onIy exits 2 naming itself.

Ahead of the properties, each fitted slope is gated on the regression it
came from: too few samples, too poor a time fit, or an allocation fit
below 0.999, and that benchmark is reported as a failure of its own. Such
a failure says re-collect with a longer time limit, not that anything
regressed, and every property naming that benchmark is unreliable in the
same run.

A benchmark missing from the JSON aborts with its name, and a benchmark
that no property touches is reported as a failure --- so a newly added
benchmark forces the property list to be re-normalized.

Exit status is nonzero if any check fails. Non-vacuity was demonstrated
on 2026-07-21, against the --csv input this script then read: inflating
48x48/S-exec by 30% in a CSV copy failed exactly properties 1 and 6,
and an extra CSV row failed the coverage guard, each with exit status
1. Re-demonstrated on 2026-07-29 against the --json input: inflating
48x48/S-exec's time-vs-iters slope by 30% added exactly the properties
1 and 6 failures; an extra report failed the coverage guard; dropping a
report aborted with its name; and blanking the "time" regression's
responder aborted naming the benchmark, each nonzero. That
run was collected at the default time limit rather than the -L 30 above,
so it also failed property 5 on cnn-24x24 on its own, before any
perturbation: at 300ms per iteration criterion fits the slope over four
ramp samples (R2 0.92), which is the very thing a raised limit buys off.
That 300ms was itself such a slope rather than the benchmark's cost: it
runs ~700ms, and CI's own series for it -- allocation flat at 3.628e9
bytes per iteration from 2026-08-03 on, time never near 300ms -- shows
nothing regressed in between, so the figure dated the instrument
(checked 2026-08-22).

The allocation pass and its gate were shown non-vacuous on 2026-07-30:
inflating 48x48/S-exec's allocated-vs-iters slope by 30% failed exactly
allocation properties 1 and 6 --- the same pair the time pass fails when its
own slope is inflated --- and dropping one allocation R2 to 0.99 failed the
gate naming that benchmark, each with exit status 1. That all fifteen
relations hold for allocation at all was established by measuring every
one of them over a full run before any was encoded: the tightest equality
came out at 1.7% against the 5% tolerance and no inequality exceeded ratio
1.00.

The merge and its partition guard were exercised on 2026-07-29 too, and
the split collection was shown to be enough rather than merely plausible:
feeding a real -L 30 collection of cnn-24x24 alongside a default-limit run
of the other 103 benchmarks reported all 107 slopes usable and every
property passing, where the default-limit run alone failed the gate three
times and property 5 once. Passing the same file twice, and passing files
that overlap in one benchmark, each aborted naming the benchmark.

The slope gate was shown non-vacuous the same day, and needed no
perturbation to fire: on that run it names exactly the three cnn-24x24
benchmarks and no others, a live control. Padding their sample counts
and R2 past both thresholds in a copy silenced it ("all 107 slopes
usable"), and lowering a 115-sample benchmark's R2 to 0.80 named that
one as well --- so each arm is known to fire alone, cnn-24x24/S-exec-raw
tripping only the sample count and 6x6/S-exec only the R2.

The fill that retired that live control cost the gate its cheapest
proof, so it was re-shown by perturbation on 2026-08-27 and again
on 2026-08-28, each time against a real
collection on the current build: truncating gather48/two-gathers-ad-orient
to 8 measurements, and separately setting its time R2 to 0.80 and its
allocated R2 to 0.99, each named that one benchmark and no other and each
exited 1, so all three arms still fire alone. Re-run that whenever the
suite outgrows the gate again -- a gate nothing trips is indistinguishable
from a gate that cannot.

Since 2026-08-28 the same proofs run on demand: --self-test builds a collection
from the property list itself -- the names the fifteen relations read, probed
rather than typed, so a benchmark added to the list is in the collection at
once -- at slopes satisfying every relation, and asserts the hand recipe above
(48x48/S-exec up 30% fails exactly properties 1 and 6, in both quantities), the
three arms of the gate each naming its own benchmark, the missing and extra
guards, the usage errors -- a collection unreadable, not criterion's, read
twice or lacking a regression is exit 2, a run that did not happen, and never a
finding -- and that a zero slope is reported rather than divided by, which it
was until then. The perturbations of real collections above stay as the record
that the relations hold on measurements; the self-test says the checker still
reads them, and that the self-test bites is mutants.py's to show.
"""
import contextlib
import io
import json
import os
import subprocess
import sys
import tempfile

MIN_R2 = 0.95
MIN_SAMPLES = 10
MIN_ALLOC_R2 = 0.999
TIME_TOL = 0.10
ALLOC_TOL = 0.05


def usage_error(msg):
    """Exit 2: the run did not happen, as distinct from 1, a finding."""
    print(msg, file=sys.stderr)
    sys.exit(2)


class Tracked(dict):
    """Records which benchmarks the properties touch, for the coverage
    guard, and turns a missing benchmark into a readable abort."""

    def __init__(self):
        super().__init__()
        self.used = set()

    def __getitem__(self, k):
        if k not in self:
            sys.exit(f"benchmark missing from the JSON (not a full run?): {k}")
        self.used.add(k)
        return super().__getitem__(k)


def regression(report, responder, hint):
    """The named regression against iteration count. criterion always fits
    "time"; the others have to be asked for at collection time."""
    for reg in report["reportAnalysis"]["anRegress"]:
        if reg["regResponder"] == responder:
            return reg
    usage_error(f"no {responder}-vs-iters regression for"
                f" {report['reportName']} --- {hint}")


def load(paths):
    """(time slopes, allocation slopes, fit quality) merged over PATHS,
    which must partition the suite."""
    t = Tracked()      # seconds per iteration
    alloc = Tracked()  # bytes allocated per iteration
    fit = {}
    for path in paths:
        # Not a collection is exit 2, nothing evaluated: the traceback's 1
        # read as a property failure (check-conv-bench-props-02), and so
        # does a collection that does not partition the suite.
        try:
            with open(path) as f:
                reports = json.load(f)[2]
            if not isinstance(reports, list):
                raise TypeError("the third element is not a list of reports")
        except (OSError, ValueError, LookupError, TypeError) as e:
            usage_error(f"{path}: not a readable criterion --json collection"
                        f" ({type(e).__name__}: {e})")
        for report in reports:
            try:
                name = report["reportName"]
                report["reportAnalysis"]["anRegress"]
                len(report["reportMeasured"])
            except (KeyError, TypeError) as e:
                usage_error(f"{path}: a report without {e} is not criterion's")
            if name in t:
                usage_error(f"benchmark collected twice, the second time"
                            f" in {path} (the files must partition the"
                            f" suite): {name}")
            treg = regression(report, "time", "criterion fits this one"
                              " always, so the file is not criterion"
                              " --json output")
            areg = regression(report, "allocated", "collect with"
                              " --regress allocated:iters and +RTS -T")
            t[name] = treg["regCoeffs"]["iters"]["estPoint"]
            alloc[name] = areg["regCoeffs"]["iters"]["estPoint"]
            fit[name] = (len(report["reportMeasured"]),
                         treg["regRSquare"]["estPoint"],
                         areg["regRSquare"]["estPoint"])
    return t, alloc, fit


def fmt_time(s):
    if s >= 1:
        return f"{s:.3f}s"
    if s >= 1e-3:
        return f"{s*1e3:.3f}ms"
    return f"{s*1e6:.1f}us"


def fmt_bytes(b):
    if b >= 1e6:
        return f"{b/1e6:.2f}MB"
    if b >= 1e3:
        return f"{b/1e3:.2f}kB"
    return f"{b:.0f}B"


# A slope is only as good as the regression it came from, and a
# benchmark whose single iteration outruns criterion's 30ms sample filter
# can spend the whole budget still inside its warm-up ramp. Both
# thresholds were sited in empty gaps of a measured full run at the
# default time limit, when the suite ran at -A1G: of its 107 benchmarks
# none fit between R2 0.927 and 0.978, and none collected between 6 and
# 10 samples. At -A32m (2026-08-22) both gaps filled up --
# inp-192x192's H-exec-raw and H-fullpipe collected 8 samples, its
# S-exec-raw fit at R2 0.946 -- so the thresholds cut through the
# distribution rather than through a hole in it, each still naming only
# benchmarks a longer budget fixes. Since orthotope's toVectorListT
# rewrites (2026-08-28) both gaps are clear again and by a wide margin:
# the worst of the 107 collects 21 samples and the worst fits at R2 0.994.
# That leaves the gate with no live control -- the arm-by-arm proof
# below is what stands in for one.

def gate(fit, alloc_only):
    """Slope quality; the number of unusable slopes."""
    print("-- slope quality (violation = re-collect, not a regression) --")
    if alloc_only:
        unusable = sorted(k for k, (_, _, ar2) in fit.items()
                          if ar2 < MIN_ALLOC_R2)
    else:
        unusable = sorted(k for k, (n, r2, ar2) in fit.items()
                          if n < MIN_SAMPLES or r2 < MIN_R2
                          or ar2 < MIN_ALLOC_R2)
    for k in unusable:
        n, r2, ar2 = fit[k]
        print(f"  [Q] {k} {n} samples, R2 {r2:.3f}, allocated R2 {ar2:.6f}"
              f"  (need >= {MIN_SAMPLES}, >= {MIN_R2}, >= {MIN_ALLOC_R2})"
              f"  FAIL")
    if unusable:
        print(f"  {len(unusable)} slope(s) unusable --- re-collect with a"
              f" longer")
        print("  time limit; every property below that names one is"
              " unreliable")
    else:
        what = "allocation fits" if alloc_only else "slopes"
        print(f"  all {len(fit)} {what} usable  PASS")
    return len(unusable)


SIZES = ["6x6", "24x24", "48x48", "96x96", "192x192"]
SWEEPS = SIZES + ["inp-" + s for s in SIZES]
CNNS = ["cnn-6x6", "cnn-12x12", "cnn-24x24"]

def properties(q, fmt, tol, label):
    """The numbered properties of bench/ConvVjpBench.hs, over one
    quantity. Both quantities take the same fifteen relations: what a
    rewrite does to the time a program takes and to the bytes it
    allocates are different questions, but the answers are bounded the
    same way, so a divergence between the two runs is itself a finding.
    Returns the number of failures."""
    fails = 0

    def eq(prop, an, bn, a, b):
        nonlocal fails
        ok = abs(a - b) <= max(a, b) * tol
        d = abs(a - b) / max(a, b) * 100 if max(a, b) else 0.0
        print(f"  [{prop}] {an} {fmt(a)} == {bn} {fmt(b)}  (diff {d:.1f}%)"
              f"  {'PASS' if ok else 'FAIL'}")
        if not ok:
            fails += 1

    def le(prop, an, bn, a, b):
        nonlocal fails
        ok = a <= (1 + tol) * b
        ratio = f"{a / b:.2f}" if b else "n/a, zero"
        print(f"  [{prop}] {an} {fmt(a)} <= {bn} {fmt(b)}  (ratio {ratio})"
              f"  {'PASS' if ok else 'FAIL'}")
        if not ok:
            fails += 1

    print(f"== {label}, to {tol*100:g}% ==")
    print("-- accounting (any engine; violation = broken measurement) --")
    print("1. S-fullpipe-honest == S-artifact + S-exec")
    for g in SWEEPS + CNNS:
        eq(1, f"{g}/S-fullpipe-honest", f"{g}/S-artifact + {g}/S-exec",
           q[f"{g}/S-fullpipe-honest"],
           q[f"{g}/S-artifact"] + q[f"{g}/S-exec"])

    print("2. H-exec-raw <= H-fullpipe <= H-term + H-exec-raw")
    for g in SWEEPS:
        le(2, f"{g}/H-exec-raw", f"{g}/H-fullpipe",
           q[f"{g}/H-exec-raw"], q[f"{g}/H-fullpipe"])
        le(2, f"{g}/H-fullpipe", f"{g}/H-term + {g}/H-exec-raw",
           q[f"{g}/H-fullpipe"], q[f"{g}/H-term"] + q[f"{g}/H-exec-raw"])

    print("3. 6x6/S-exec <= S-fullpipe-hoisted-6x6 <= 6x6/S-fullpipe-honest")
    le(3, "6x6/S-exec", "hoisted",
       q["6x6/S-exec"], q["pitfalls/S-fullpipe-hoisted-6x6"])
    le(3, "hoisted", "6x6/S-fullpipe-honest",
       q["pitfalls/S-fullpipe-hoisted-6x6"], q["6x6/S-fullpipe-honest"])

    print("-- simplifier recorder --")
    print("4. pitfalls/H-exec-const-48x48 == 48x48/H-exec")
    eq(4, "H-exec-const-48x48", "48x48/H-exec",
       q["pitfalls/H-exec-const-48x48"], q["48x48/H-exec"])

    print("-- engine invariants (violation = regression) --")
    print("5. S-exec <= S-exec-raw; H-exec <= H-exec-raw")
    for g in SWEEPS + CNNS:
        le(5, f"{g}/S-exec", f"{g}/S-exec-raw",
           q[f"{g}/S-exec"], q[f"{g}/S-exec-raw"])
    for g in SWEEPS:
        le(5, f"{g}/H-exec", f"{g}/H-exec-raw",
           q[f"{g}/H-exec"], q[f"{g}/H-exec-raw"])

    print("6. S-exec <= H-exec")
    for g in SWEEPS:
        le(6, f"{g}/S-exec", f"{g}/H-exec", q[f"{g}/S-exec"], q[f"{g}/H-exec"])

    print("-- cost model of the current kernels"
          " (re-measure on kernel change) --")
    G = "gather48/"
    print("7. two-gathers-ad-shm-sorted == two-gathers-ad-orient")
    eq(7, "shm-sorted", "ad-orient",
       q[G + "two-gathers-ad-shm-sorted"], q[G + "two-gathers-ad-orient"])
    print("8. two-gathers-ad-shn-sorted <= two-gathers-ad-orient")
    le(8, "shn-sorted", "ad-orient",
       q[G + "two-gathers-ad-shn-sorted"], q[G + "two-gathers-ad-orient"])
    print("9. two-gathers-vec-orient <= two-gathers-ad-orient")
    le(9, "vec-orient", "ad-orient",
       q[G + "two-gathers-vec-orient"], q[G + "two-gathers-ad-orient"])
    print("10. the four fused-gather-* pairwise equal")
    fused = ["fused-gather-ad-orient", "fused-gather-vec-orient",
             "fused-gather-shm-sorted-asc", "fused-gather-shm-sorted-desc"]
    for i in range(len(fused)):
        for j in range(i + 1, len(fused)):
            eq(10, fused[i], fused[j], q[G + fused[i]], q[G + fused[j]])
    print("11. two-gathers-ad-orient <= fused-gather-ad-orient")
    le(11, "two-gathers-ad", "fused-gather-ad",
       q[G + "two-gathers-ad-orient"], q[G + "fused-gather-ad-orient"])

    S = "scatter48/"
    print("12. two-scatters-ad-orient == two-scatters-vec-orient")
    eq(12, "ad-orient", "vec-orient",
       q[S + "two-scatters-ad-orient"], q[S + "two-scatters-vec-orient"])
    print("13. two-scatters-ad-orient <= two-scatters-ad-shn-sorted")
    le(13, "ad-orient", "shn-sorted",
       q[S + "two-scatters-ad-orient"], q[S + "two-scatters-ad-shn-sorted"])
    print("14. two-scatters-X <= fused-scatter-X, X in {ad, vec}")
    le(14, "two-scatters-ad", "fused-scatter-ad",
       q[S + "two-scatters-ad-orient"], q[S + "fused-scatter-ad-orient"])
    le(14, "two-scatters-vec", "fused-scatter-vec",
       q[S + "two-scatters-vec-orient"], q[S + "fused-scatter-vec-orient"])
    print("15. two-scatters-ad-orient <= two-gathers-ad-orient")
    le(15, "two-scatters-ad", "two-gathers-ad",
       q[S + "two-scatters-ad-orient"], q[G + "two-gathers-ad-orient"])

    return fails


def main(argv):
    alloc_only = "--allocation-only" in argv
    unknown = [a for a in argv if a.startswith("-") and a != "--allocation-only"]
    if unknown:
        usage_error("unknown flag(s): %s; only --allocation-only is understood"
                    % " ".join(unknown))
    paths = [a for a in argv if not a.startswith("-")]
    if not paths:
        usage_error(__doc__.split("\n\n")[1])
    t, alloc, fit = load(paths)
    fails = gate(fit, alloc_only)
    if not alloc_only:
        fails += properties(t, fmt_time, TIME_TOL, "time")
    fails += properties(alloc, fmt_bytes, ALLOC_TOL, "allocated bytes")
    untouched = sorted(set(alloc) - alloc.used)
    if untouched:
        print("\ncoverage: benchmarks untouched by any property --- extend"
              " the")
        print("numbered list in bench/ConvVjpBench.hs's module haddock:")
        for n in untouched:
            print(f"  {n}")
        fails += len(untouched)
    print(f"\n{fails} check(s) FAILED" if fails else "\nall checks PASS")
    return 1 if fails else 0


def property_names():
    """Every benchmark the properties read, taken from the properties
    themselves so a synthetic collection cannot drift from them."""
    class Probe(dict):
        def __getitem__(self, k):
            self[k] = 1.0
            return 1.0
    q = Probe()
    with contextlib.redirect_stdout(io.StringIO()):
        properties(q, fmt_time, TIME_TOL, "probe")
    return sorted(q)


def self_test():
    """Synthetic collections built from the property list; every guard
    and both perturbations of the docstring's hand recipe, asserted."""
    script = os.path.abspath(__file__)
    bad = []

    def expect(case, p, code, *needles):
        if p.returncode != code:
            bad.append(f"{case}: exit {p.returncode}, expected {code}")
        for n in needles:
            if n not in p.stdout + p.stderr:
                bad.append(f"{case}: output lacks {n!r}")

    def run(*argv):
        return subprocess.run([sys.executable, script] + list(argv),
                              capture_output=True, text=True)

    # A slope per benchmark that satisfies every relation: property 1 is
    # a sum, so the honest full pipeline costs two units, and the raw
    # execution 1.5 so that inflating S-exec by 30% fails 1 and 6 alone,
    # as it did on real data.
    def base(name):
        if name.endswith("/S-fullpipe-honest"):
            return 2.0
        if name.endswith("/S-exec-raw"):
            return 1.5
        return 1.0

    def report(name, t=None, a=None, n=20, r2=1.0, ar2=1.0):
        t = base(name) if t is None else t
        a = base(name) if a is None else a
        return {"reportName": name, "reportMeasured": [0] * n,
                "reportAnalysis": {"anRegress": [
                    {"regResponder": "time",
                     "regCoeffs": {"iters": {"estPoint": t}},
                     "regRSquare": {"estPoint": r2}},
                    {"regResponder": "allocated",
                     "regCoeffs": {"iters": {"estPoint": a}},
                     "regRSquare": {"estPoint": ar2}}]}}

    def write(path, reports):
        with open(path, "w") as fh:
            json.dump([None, None, reports], fh)

    names = property_names()
    with tempfile.TemporaryDirectory() as td:
        full = os.path.join(td, "full.json")
        other = os.path.join(td, "other.json")
        write(full, [report(n) for n in names])
        expect("no argument", run(), 2, "Usage")
        expect("unknown flag", run("--allocation-onIy", full), 2, "unknown")
        expect("all relations at equal slopes", run(full), 0,
               f"all {len(names)} slopes usable", "all checks PASS")
        expect("allocation only", run("--allocation-only", full), 0,
               "allocation fits usable", "all checks PASS")
        # The docstring's own perturbation: 48x48/S-exec up 30% fails
        # exactly properties 1 and 6, in both quantities.
        write(other, [report(n, t=1.3, a=1.3) if n == "48x48/S-exec"
                      else report(n) for n in names])
        p = run(other)
        expect("inflated slope", p, 1, "4 check(s) FAILED")
        failed = [ln for ln in p.stdout.splitlines() if ln.endswith("FAIL")]
        if sorted(ln.split("]")[0].strip(" [") for ln in failed) != \
                ["1", "1", "6", "6"]:
            bad.append("inflated slope failed other than 1 and 6 twice: %r"
                       % failed)
        write(other, [report(n) for n in names] + [report("extra/one")])
        expect("extra benchmark", run(other), 1, "untouched", "extra/one")
        write(other, [report(n) for n in names if n != "6x6/S-exec"])
        expect("missing benchmark", run(other), 1, "missing from the JSON",
               "6x6/S-exec")
        write(other, [report(n, n=8 if n == "6x6/S-exec" else 20,
                             r2=0.8 if n == "6x6/H-exec" else 1.0,
                             ar2=0.99 if n == "6x6/S-exec-raw" else 1.0)
                      for n in names])
        p = run(other)
        expect("slope gate", p, 1, "3 slope(s) unusable", "6x6/S-exec 8",
               "6x6/H-exec 20", "6x6/S-exec-raw 20")
        p = run("--allocation-only", other)
        expect("slope gate, allocation only", p, 1, "1 slope(s) unusable",
               "6x6/S-exec-raw")
        expect("collected twice", run(full, full), 2, "collected twice")
        expect("missing collection", run(os.path.join(td, "nope.json")), 2,
               "not a readable criterion")
        for shape in ("[]", "{}", "[null, null, 5]"):
            open(other, "w").write(shape)
            expect(f"not a collection: {shape}", run(other), 2,
                   "not a readable criterion")
        write(other, [dict(report(n), reportAnalysis={"anRegress": [
            report(n)["reportAnalysis"]["anRegress"][0]]}) for n in names])
        expect("no allocation regression", run(other), 2,
               "no allocated-vs-iters regression")
        write(other, [report(n, t=0.0, a=0.0) for n in names])
        expect("zero slopes", run(other), 0, "all checks PASS")
    for b in bad:
        print(f"FAIL: {b}")
    if not bad:
        print(f"ok:   every self-test case behaved as expected, over the"
              f" {len(names)} benchmarks the properties name")
    return 1 if bad else 0


if __name__ == "__main__":
    if sys.argv[1:] == ["--self-test"]:
        sys.exit(self_test())
    sys.exit(main(sys.argv[1:]))
