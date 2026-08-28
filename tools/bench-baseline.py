#!/usr/bin/env python3
"""Diff a benchmark collection against recorded reference figures.

Usage: python3 tools/bench-baseline.py --baseline TSV JSON [JSON ...]
       python3 tools/bench-baseline.py --emit JSON [JSON ...]

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
2 is a usage or coverage error: a benchmark in one side and not the other,
which is what a renamed or added benchmark looks like, and which must be
settled by refreshing the baseline rather than by widening a tolerance.

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
omitting --baseline or passing an unknown flag.
"""
import json
import sys

args = sys.argv[1:]
emit = "--emit" in args
baseline_path = None
alloc_tol, time_tol = 0.005, 0.10
rest = []
i = 0
while i < len(args):
    a = args[i]
    if a == "--emit":
        pass
    elif a == "--baseline":
        i += 1
        baseline_path = args[i]
    elif a == "--alloc-tol":
        i += 1
        alloc_tol = float(args[i])
    elif a == "--time-tol":
        i += 1
        time_tol = float(args[i])
    elif a.startswith("-"):
        print(f"unknown flag: {a}", file=sys.stderr)
        sys.exit(2)
    else:
        rest.append(a)
    i += 1
if not rest:
    sys.exit(__doc__.split("\n\n")[1])
if not emit and baseline_path is None:
    print("--baseline is required and has no default: the references under"
          " bench/ differ in suite and in which orthotope they link, and"
          " nothing in a criterion JSON says which one a collection is,"
          " so naming the reference is the only guard against diffing"
          " across builds (see this script's docstring)", file=sys.stderr)
    sys.exit(2)


def read_collection(paths):
    out = {}
    for p in paths:
        with open(p) as f:
            for r in json.load(f)[2]:
                name = r["reportName"]
                if name in out:
                    sys.exit(f"benchmark collected twice, the second time in"
                             f" {p} (the files must partition the suite):"
                             f" {name}")
                regs = {g["regResponder"]: g
                        for g in r["reportAnalysis"]["anRegress"]}
                for want in ("time", "allocated"):
                    if want not in regs:
                        sys.exit(f"no {want}-vs-iters regression for {name}"
                                 f" -- collect with --regress allocated:iters"
                                 f" and +RTS -T")
                out[name] = (regs["time"]["regCoeffs"]["iters"]["estPoint"],
                             regs["allocated"]["regCoeffs"]["iters"]["estPoint"])
    return out


now = read_collection(rest)

if emit:
    for name in sorted(now):
        t, a = now[name]
        print(f"{name}\t{t:.9g}\t{a:.0f}")
    sys.exit(0)

base = {}
with open(baseline_path) as f:
    for line in f:
        if line.startswith("#") or not line.strip():
            continue
        name, t, a = line.rstrip("\n").split("\t")
        base[name] = (float(t), float(a))

missing = sorted(set(base) - set(now))
added = sorted(set(now) - set(base))
if missing or added:
    for m in missing:
        print(f"  [C] in {baseline_path}, absent from the collection: {m}")
    for m in added:
        print(f"  [C] in the collection, absent from {baseline_path}: {m}")
    print(f"  refresh {baseline_path} from a full run; a partial collection"
          f" or a renamed benchmark looks exactly like this")
    sys.exit(2)


def fmt_t(s):
    return f"{s*1e3:.3f}ms" if s < 1 else f"{s:.3f}s"


moved = []
for name in sorted(base):
    bt, ba = base[name]
    nt, na = now[name]
    da = (na - ba) / ba
    dt = (nt - bt) / bt
    if abs(da) > alloc_tol or abs(dt) > time_tol:
        moved.append((name, bt, nt, dt, ba, na, da))
# Largest allocation movement first: across a real build change the median
# mover sits under 1%, so name order buries the few that matter.
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
    sys.exit(1)
print("  nothing moved beyond tolerance  PASS")
sys.exit(0)
