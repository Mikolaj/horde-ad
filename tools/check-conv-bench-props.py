#!/usr/bin/env python3
"""Verify the numbered properties of bench/ConvVjpBench.hs.

Usage: python3 tools/check-conv-bench-props.py [--allocation-only]
                                              JSON [JSON ...]

Every property is checked twice, against two quantities: seconds per
iteration, and bytes allocated per iteration. The same fifteen relations
bound both — what a rewrite costs in time and what it costs in allocation
are different questions whose answers happen to be bounded alike, so a
divergence between the two passes is itself a finding. Time is checked to
10%, allocation to 5%, allocation carrying no measurement noise.

JSON is criterion's --json output. One full run of the suite (no
benchmark filter) does, collected with a raised time limit and with the
allocation regression asked for:

    cabal bench convVjpBench --enable-optimization \\
      --benchmark-options='-L 30 --regress allocated:iters --json FILE \\
        +RTS -T'

Several files are accepted and merged, which buys back most of that
limit's cost: only the slow groups need the long budget, so give it to
them alone and let the rest run at the default, about 26 minutes against
54. Criterion's bare arguments are prefix patterns on the group/bench
path, and these two sets are disjoint (`6x6` does not match `inp-6x6`,
`24x24` does not match `cnn-24x24`):

    cabal bench convVjpBench --enable-optimization --benchmark-options=\\
      '-L 30 --regress allocated:iters --json slow.json 192x192 \\
       inp-192x192 cnn-12x12 cnn-24x24 gather48 scatter48 +RTS -T'
    cabal bench convVjpBench --enable-optimization --benchmark-options=\\
      '--regress allocated:iters --json fast.json 6x6 24x24 48x48 96x96 \\
       inp-6x6 inp-24x24 inp-48x48 inp-96x96 cnn-6x6 pitfalls +RTS -T'
    python3 tools/check-conv-bench-props.py slow.json fast.json

Both halves carry `--regress allocated:iters` and `+RTS -T`, exactly as
the single-file recipe does: `-L 30` is the only thing the split trades
away. Omit them and collection still succeeds, but the check aborts on
its first report, the allocation pass having no slope to read. These two
commands lacked both flags from 2dc4f8783, which added the split and the
allocation pass in one go, until 2026-07-30 -- found by reading the
requirement below against the recipe, then demonstrated by deleting the
37 allocated regressions from a real slow.json: exit 1 on
192x192/S-fullpipe-honest, quoting the hint that names the two flags.

Together the files must partition the suite: a benchmark collected twice
aborts, and one missing from all of them aborts as before. The split must
also not cut across a property. gather48 and scatter48 take the long
budget together only because property 15 compares them, and splitting
them would weigh a converged slope against a ramp-biased one; the slow
set is otherwise just the groups that come up short of samples at the
default limit, cnn-24x24 worst at four.

The times compared are the per-iteration OLS slopes criterion fits over
time against iteration count — the estimate it prints on its "time"
line. Criterion's --csv output cannot serve here: it carries only the
mean, which every benchmark's warm-up ramp inflates by a per-benchmark
amount that does not cancel between two benchmarks. The raised time
limit is what makes the slope itself trustworthy: the default 5s leaves
a millisecond-scale benchmark too few samples for the ramp to regress
out cleanly.

The properties are stated and explained in the module haddock of
bench/ConvVjpBench.hs — that list is canonical and this script is its
executable form; keep the two in sync. At tolerance tol, `a == b` stands
for `abs (a - b) <= max a b * tol`, and `a <= b` for `a <= (1 + tol) * b`.

The haddock also explains the categories echoed in the output:
properties 1-3 are accounting, so a failure there means the measurement
itself broke; property 4 records simplifier behavior; properties 5-6
are engine invariants, so a failure is an engine regression; properties
7-15 record the cost model of the current interpreted gather/scatter
kernels and are the ones to re-measure when those kernels change.

--allocation-only checks just the allocation pass, and gates only on the
allocation fit. That is what makes the set cheap enough to gate CI on: a
default-limit collection is too short for the time slopes, but allocation
is so nearly exact in the iteration count that even the four-sample
cnn-24x24 benchmarks fit it at R2 1.000000, so the allocation verdict on a
ten-minute run is as good as on an hour-long one. The tradeoff is what
allocation cannot see — the ~9-12x gather-against-scatter time gap being
the standing example.

Ahead of the properties, each fitted slope is gated on the regression it
came from: too few samples, too poor a time fit, or an allocation fit
below 0.999, and that benchmark is reported as a failure of its own. Such
a failure says re-collect with a longer time limit, not that anything
regressed, and every property naming that benchmark is unreliable in the
same run.

A benchmark missing from the JSON aborts with its name, and a benchmark
that no property touches is reported as a failure — so a newly added
benchmark forces the property list to be re-normalized.

Exit status is nonzero if any check fails. Non-vacuity was demonstrated
on 2026-07-21, against the --csv input this script then read: inflating
48x48/S-exec by 30% in a CSV copy failed exactly properties 1 and 6,
and an extra CSV row failed the coverage guard, each with exit status
1. Re-demonstrated on 2026-07-29 against the --json input: inflating
48x48/S-exec's time-vs-iters slope by 30% added exactly the properties
1 and 6 failures; an extra report failed the coverage guard; dropping a
report aborted with its name; and blanking the "time" regression's
responder aborted naming the benchmark, each with exit status 1. That
run was collected at the default time limit rather than the -L 30 above,
so it also failed property 5 on cnn-24x24 on its own, before any
perturbation: at 300ms per iteration criterion fits the slope over four
ramp samples (R2 0.92), which is the very thing -L 30 buys off.

The allocation pass and its gate were shown non-vacuous on 2026-07-30:
inflating 48x48/S-exec's allocated-vs-iters slope by 30% failed exactly
allocation properties 1 and 6 — the same pair the time pass fails when its
own slope is inflated — and dropping one allocation R2 to 0.99 failed the
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
that overlap in one benchmark, each aborted naming the benchmark, with
exit status 1.

The slope gate was shown non-vacuous the same day, and needed no
perturbation to fire: on that run it names exactly the three cnn-24x24
benchmarks and no others, a live control. Padding their sample counts
and R2 past both thresholds in a copy silenced it ("all 107 slopes
usable"), and lowering a 115-sample benchmark's R2 to 0.80 named that
one as well — so each arm is known to fire alone, cnn-24x24/S-exec-raw
tripping only the sample count and 6x6/S-exec only the R2.
"""
import json
import sys

ALLOC_ONLY = "--allocation-only" in sys.argv[1:]
paths = [a for a in sys.argv[1:] if not a.startswith("-")]
if not paths:
    sys.exit(__doc__.split("\n\n")[1])


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
    sys.exit(f"no {responder}-vs-iters regression for"
             f" {report['reportName']} — {hint}")


t = Tracked()      # seconds per iteration
alloc = Tracked()  # bytes allocated per iteration
fit = {}
for path in paths:
    with open(path) as f:
        # criterion writes ["criterion", version, [report, ...]]
        for report in json.load(f)[2]:
            name = report["reportName"]
            if name in t:
                sys.exit(f"benchmark collected twice, the second time in"
                         f" {path} (the files must partition the suite):"
                         f" {name}")
            treg = regression(report, "time", "criterion fits this one always,"
                              " so the file is not criterion --json output")
            areg = regression(report, "allocated", "collect with"
                              " --regress allocated:iters and +RTS -T")
            t[name] = treg["regCoeffs"]["iters"]["estPoint"]
            alloc[name] = areg["regCoeffs"]["iters"]["estPoint"]
            fit[name] = (len(report["reportMeasured"]),
                         treg["regRSquare"]["estPoint"],
                         areg["regRSquare"]["estPoint"])


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
# thresholds fall in empty gaps of a measured full run at the default
# time limit: of its 107 benchmarks none fit between R2 0.927 and 0.978,
# and none collect between 6 and 10 samples, the three ~300ms-per-
# iteration cnn-24x24 ones sitting alone below at 4-5 samples and R2
# 0.918-0.989. Both checks earn their place — that group's S-exec-raw
# fits at R2 0.989, so only its sample count gives it away.
MIN_R2 = 0.95
MIN_SAMPLES = 10
# Allocation is all but exactly linear in the iteration count, so its fit
# is held to a far tighter standard than time's: over a measured full run
# the worst of the 107 was 0.999997.
MIN_ALLOC_R2 = 0.999

fails = 0
print("-- slope quality (violation = re-collect, not a regression) --")
if ALLOC_ONLY:
    unusable = sorted(k for k, (_, _, ar2) in fit.items()
                      if ar2 < MIN_ALLOC_R2)
else:
    unusable = sorted(k for k, (n, r2, ar2) in fit.items()
                      if n < MIN_SAMPLES or r2 < MIN_R2 or ar2 < MIN_ALLOC_R2)
for k in unusable:
    n, r2, ar2 = fit[k]
    print(f"  [Q] {k} {n} samples, R2 {r2:.3f}, allocated R2 {ar2:.6f}"
          f"  (need >= {MIN_SAMPLES}, >= {MIN_R2}, >= {MIN_ALLOC_R2})  FAIL")
if unusable:
    print(f"  {len(unusable)} slope(s) unusable — re-collect with a longer")
    print("  time limit; every property below that names one is unreliable")
    fails += len(unusable)
else:
    what = "allocation fits" if ALLOC_ONLY else "slopes"
    print(f"  all {len(fit)} {what} usable  PASS")


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
        d = abs(a - b) / max(a, b) * 100
        print(f"  [{prop}] {an} {fmt(a)} == {bn} {fmt(b)}  (diff {d:.1f}%)"
              f"  {'PASS' if ok else 'FAIL'}")
        if not ok:
            fails += 1

    def le(prop, an, bn, a, b):
        nonlocal fails
        ok = a <= (1 + tol) * b
        print(f"  [{prop}] {an} {fmt(a)} <= {bn} {fmt(b)}  (ratio {a/b:.2f})"
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

TIME_TOL = 0.10
# Allocation carries no measurement noise, so it is held twice as tightly
# as time. 5% is three times the largest legitimate gap a measured full
# run shows — property 4's 1.7%, an embedded constant cotangent against a
# variable one — and every inequality in that run came out at ratio 1.00
# or below.
ALLOC_TOL = 0.05

if not ALLOC_ONLY:
    fails += properties(t, fmt_time, TIME_TOL, "time")
fails += properties(alloc, fmt_bytes, ALLOC_TOL, "allocated bytes")

# Keyed on the allocation pass, the one that runs in both modes; the two
# quantities carry the same benchmark names.
untouched = sorted(set(alloc) - alloc.used)
if untouched:
    print("\ncoverage: benchmarks untouched by any property — extend the")
    print("numbered list in bench/ConvVjpBench.hs's module haddock:")
    for n in untouched:
        print(f"  {n}")
    fails += len(untouched)

print(f"\n{fails} check(s) FAILED" if fails else "\nall checks PASS")
sys.exit(1 if fails else 0)
