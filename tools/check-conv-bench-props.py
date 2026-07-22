#!/usr/bin/env python3
"""Verify the numbered time properties of bench/ConvVjpBench.hs.

Usage: python3 tools/check-conv-bench-props.py CSV

CSV is criterion's --csv output from a full run of the suite (no
benchmark filter):

    cabal bench convVjpBench --enable-optimization \\
      --benchmark-options='--csv FILE'

The properties are stated and explained in the module haddock of
bench/ConvVjpBench.hs — that list is canonical and this script is its
executable form; keep the two in sync. Each property relates criterion
means and is checked up to 10% tolerance: `a == b` stands for
`abs (a - b) <= max a b / 10`, and `a <= b` for `a <= 1.1 * b`.

The haddock also explains the categories echoed in the output:
properties 1-3 are accounting, so a failure there means the measurement
itself broke; property 4 records simplifier behavior; properties 5-6
are engine invariants, so a failure is an engine regression; properties
7-15 record the cost model of the current interpreted gather/scatter
kernels and are the ones to re-measure when those kernels change.

A benchmark missing from the CSV aborts with its name, and a benchmark
that no property touches is reported as a failure — so a newly added
benchmark forces the property list to be re-normalized.

Exit status is nonzero if any check fails. Non-vacuity was demonstrated
on 2026-07-21: inflating 48x48/S-exec by 30% in a CSV copy failed
exactly properties 1 and 6, and an extra CSV row failed the coverage
guard, each with exit status 1.
"""
import csv
import sys

if len(sys.argv) != 2:
    sys.exit(__doc__.split("\n\n")[1])


class TrackedTimes(dict):
    """Records which benchmarks the properties touch, for the coverage
    guard, and turns a missing benchmark into a readable abort."""

    def __init__(self):
        super().__init__()
        self.used = set()

    def __getitem__(self, k):
        if k not in self:
            sys.exit(f"benchmark missing from the CSV (not a full run?): {k}")
        self.used.add(k)
        return super().__getitem__(k)


t = TrackedTimes()
with open(sys.argv[1]) as f:
    for row in csv.DictReader(f):
        t[row["Name"]] = float(row["Mean"])


def fmt(s):
    if s >= 1:
        return f"{s:.3f}s"
    if s >= 1e-3:
        return f"{s*1e3:.3f}ms"
    return f"{s*1e6:.1f}us"


fails = 0


def eq(prop, an, bn, a, b):
    global fails
    ok = abs(a - b) <= max(a, b) / 10
    d = abs(a - b) / max(a, b) * 100
    print(f"  [{prop}] {an} {fmt(a)} == {bn} {fmt(b)}  (diff {d:.1f}%)"
          f"  {'PASS' if ok else 'FAIL'}")
    if not ok:
        fails += 1


def le(prop, an, bn, a, b):
    global fails
    ok = a <= 1.1 * b
    print(f"  [{prop}] {an} {fmt(a)} <= {bn} {fmt(b)}  (ratio {a/b:.2f})"
          f"  {'PASS' if ok else 'FAIL'}")
    if not ok:
        fails += 1


SIZES = ["6x6", "24x24", "48x48", "96x96", "192x192"]
SWEEPS = SIZES + ["inp-" + s for s in SIZES]
CNNS = ["cnn-6x6", "cnn-12x12", "cnn-24x24"]

print("-- accounting (any engine; violation = broken measurement) --")
print("1. S-fullpipe-honest == S-artifact + S-exec")
for g in SWEEPS + CNNS:
    eq(1, f"{g}/S-fullpipe-honest", f"{g}/S-artifact + {g}/S-exec",
       t[f"{g}/S-fullpipe-honest"], t[f"{g}/S-artifact"] + t[f"{g}/S-exec"])

print("2. H-exec-raw <= H-fullpipe <= H-term + H-exec-raw")
for g in SWEEPS:
    le(2, f"{g}/H-exec-raw", f"{g}/H-fullpipe",
       t[f"{g}/H-exec-raw"], t[f"{g}/H-fullpipe"])
    le(2, f"{g}/H-fullpipe", f"{g}/H-term + {g}/H-exec-raw",
       t[f"{g}/H-fullpipe"], t[f"{g}/H-term"] + t[f"{g}/H-exec-raw"])

print("3. 6x6/S-exec <= S-fullpipe-hoisted-6x6 <= 6x6/S-fullpipe-honest")
le(3, "6x6/S-exec", "hoisted",
   t["6x6/S-exec"], t["pitfalls/S-fullpipe-hoisted-6x6"])
le(3, "hoisted", "6x6/S-fullpipe-honest",
   t["pitfalls/S-fullpipe-hoisted-6x6"], t["6x6/S-fullpipe-honest"])

print("-- simplifier recorder --")
print("4. pitfalls/H-exec-const-48x48 == 48x48/H-exec")
eq(4, "H-exec-const-48x48", "48x48/H-exec",
   t["pitfalls/H-exec-const-48x48"], t["48x48/H-exec"])

print("-- engine invariants (violation = regression) --")
print("5. S-exec <= S-exec-raw; H-exec <= H-exec-raw")
for g in SWEEPS + CNNS:
    le(5, f"{g}/S-exec", f"{g}/S-exec-raw",
       t[f"{g}/S-exec"], t[f"{g}/S-exec-raw"])
for g in SWEEPS:
    le(5, f"{g}/H-exec", f"{g}/H-exec-raw",
       t[f"{g}/H-exec"], t[f"{g}/H-exec-raw"])

print("6. S-exec <= H-exec")
for g in SWEEPS:
    le(6, f"{g}/S-exec", f"{g}/H-exec", t[f"{g}/S-exec"], t[f"{g}/H-exec"])

print("-- cost model of the current kernels (re-measure on kernel change) --")
G = "gather48/"
print("7. two-gathers-ad-shm-sorted == two-gathers-ad-orient")
eq(7, "shm-sorted", "ad-orient",
   t[G + "two-gathers-ad-shm-sorted"], t[G + "two-gathers-ad-orient"])
print("8. two-gathers-ad-shn-sorted <= two-gathers-ad-orient")
le(8, "shn-sorted", "ad-orient",
   t[G + "two-gathers-ad-shn-sorted"], t[G + "two-gathers-ad-orient"])
print("9. two-gathers-vec-orient <= two-gathers-ad-orient")
le(9, "vec-orient", "ad-orient",
   t[G + "two-gathers-vec-orient"], t[G + "two-gathers-ad-orient"])
print("10. the four fused-gather-* pairwise equal")
fused = ["fused-gather-ad-orient", "fused-gather-vec-orient",
         "fused-gather-shm-sorted-asc", "fused-gather-shm-sorted-desc"]
for i in range(len(fused)):
    for j in range(i + 1, len(fused)):
        eq(10, fused[i], fused[j], t[G + fused[i]], t[G + fused[j]])
print("11. two-gathers-ad-orient <= fused-gather-ad-orient")
le(11, "two-gathers-ad", "fused-gather-ad",
   t[G + "two-gathers-ad-orient"], t[G + "fused-gather-ad-orient"])

S = "scatter48/"
print("12. two-scatters-ad-orient == two-scatters-vec-orient")
eq(12, "ad-orient", "vec-orient",
   t[S + "two-scatters-ad-orient"], t[S + "two-scatters-vec-orient"])
print("13. two-scatters-ad-orient <= two-scatters-ad-shn-sorted")
le(13, "ad-orient", "shn-sorted",
   t[S + "two-scatters-ad-orient"], t[S + "two-scatters-ad-shn-sorted"])
print("14. two-scatters-X <= fused-scatter-X, X in {ad, vec}")
le(14, "two-scatters-ad", "fused-scatter-ad",
   t[S + "two-scatters-ad-orient"], t[S + "fused-scatter-ad-orient"])
le(14, "two-scatters-vec", "fused-scatter-vec",
   t[S + "two-scatters-vec-orient"], t[S + "fused-scatter-vec-orient"])
print("15. two-scatters-ad-orient <= two-gathers-ad-orient")
le(15, "two-scatters-ad", "two-gathers-ad",
   t[S + "two-scatters-ad-orient"], t[G + "two-gathers-ad-orient"])

untouched = sorted(set(t) - t.used)
if untouched:
    print("\ncoverage: benchmarks untouched by any property — extend the")
    print("numbered list in bench/ConvVjpBench.hs's module haddock:")
    for n in untouched:
        print(f"  {n}")
    fails += len(untouched)

print(f"\n{fails} check(s) FAILED" if fails else "\nall checks PASS")
sys.exit(1 if fails else 0)
