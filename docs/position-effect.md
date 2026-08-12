# The position effect: RTS pool state couples benchmarks in one process

A benchmark's measured time can depend on which benchmarks ran earlier
in the same criterion process — by 22% on this repo's `convVjpBench` gather
benchmarks — through state the predecessor leaves in GHC's block-level memory
pool and nothing ever resets.  This document is the full account: the mechanism
and the evidence for each link, what was ruled out, the relation to the warm-up
ramp, the consequences for measurement practice here and in orthotope's
`micro-regime3`, and the standalone reproducer behind the [GHC issue
draft][ghc-issue].  The files that used to carry pieces
of this (`bench/CLAUDE.md`, the root `CLAUDE.md`, the staged drafts,
`micro-regime3/README.md`) now hold one-line rules and link here.

Vocabulary: "position effect" here means dependence on *which benchmarks share
the process* (the roster).  It is not the slot a benchmark occupies within
a fixed roster — `micro-regime3`'s A/A controls measure that separately and find
it benign.

## The phenomenon

On the build linking the fixed orthotope, `gather48/fused-gather-ad-orient` runs
at 10.6–10.9 ms/iteration in a process where it is the only benchmark,
and at 13.10–13.18 ms/iteration — 22% slower — when
`gather48/two-gathers-ad-orient` runs before it.  The shift is flat
from the victim's very first sample (criterion per-iteration OLS slopes at R² ≥
0.9986, and the poisoned runs are the *more* linear ones), so within any single
run it is indistinguishable from a real difference.  It survives the major GC
criterion performs at every benchmark's start, and it is invisible
to interleaving and per-pair controls, because both arms of an A/B pair share
their roster: each run's numbers stay internally consistent to a few percent
while the ratio moves with the selection.  That is how it once manufactured
a phantom "~18% regression" on the fused-gather benchmarks in an interleaved,
controlled A/B of the orthotope strided-fallback fix (since retracted), and why
`bench/CLAUDE.md`'s A/B rules require the benchmark selection to be pinned
across compared runs.

## Mechanism

Each link below is measured; together they form a causal chain from one
benchmark's allocation profile to the next benchmark's cache behavior.

**Poisoning.**  One iteration of `two-gathers-ad-orient` materializes ~288
short-lived per-position gather-slice vectors of 3600 and 10368 bytes — all just
above GHC's 3276-byte large-object threshold, so each occupies its own 1–3-block
group outside the nursery and dies at the next GC.  Interleaved with only 9.4
MB/iteration of ordinary heap churn, this checkerboards the megablocks.  During
~7 s of the benchmark the RTS pool grows steadily from 1117 to 2180 MiB (RSS
timeline: growth from t≈1.8 s, plateau by t≈8.4 s) and then never shrinks
or defragments: `-I0` prevents idle collections, major GCs do not rebuild
free-list structure, and `-Fd1` changes neither the residency (page-fault counts
identical to ±1) nor the effect.  The poisoning saturates: one such predecessor
produces the full effect, and all four `two-gathers` variants together add
nothing (13.12 vs 13.14 ms).  Below saturation it is dose-dependent: a 5 s
predecessor leaves a 2043 MiB pool and a 12.73 ms victim.

**Victim.**  The fused-gather benchmark then runs its identical 83.2
MB/iteration workload 22% slower, entirely in mutator time: GC wall stays ~1.3
µs/iteration in both contexts, allocation is byte-identical (83.2076 MB), GC
counts and bytes copied match, and the poisoned fused phase takes essentially
no page faults (98 in the whole phase) — every page is resident; the memory
is simply laid out differently.

**Attribution.**  Hardware counters (root `perf stat` over fixed-iteration runs,
phases separated by differencing) close the chain exactly.  Per iteration, alone
→ poisoned: task-clock 10.81 → 13.21 ms (1.222×); instructions 133.55M → 133.48M
(0.9994×); dTLB-load-misses 22.1k → 22.9k (1.04×); clock 4.954 → 4.953 GHz;
cache-misses 120.0k → 343.5k (2.86×).  The extra 11.8M cycles divided
by the extra 223k LLC misses give ~53 cycles per miss — DRAM latency
with overlap — accounting for the full +2.40 ms; IPC falls 2.48 → 2.04
on an identical instruction stream.

**Reading.**  In a clean pool, the victim's per-iteration pinned and large
allocations (every Storable vector is pinned, at any size) recycle through
a short free list: the same few dozen MB of physical memory churn every GC cycle
and stay L3-resident, so writes hit warm lines.  Fragmentation shatters
that reuse chain — freed fragments coalesce into other size buckets, the next
allocation splits some other group — and the recycled working set cycles through
hundreds of MB before reuse: ~14 MB/iteration (223k lines × 64 B) that L3 used
to retain round-trips to DRAM.  The nursery itself is carved contiguously
at startup and reused in place, so ordinary heap allocation is unaffected
(this one link is from RTS-source reading, not measured here; everything
it explains is).

**Structure, not size.**  Pool size and residency are ruled out as the lever:
`-H2G` grows a fused-alone process to a comparable 2135 MiB contiguously,
touches it all (545k faults), and runs at full speed (10.51 ms); while
predecessors leaving even *larger* pools cause *smaller* effects —
`two-gathers-ad-shn-sorted` +9% at 2353 MiB, conv `48x48/S-exec` +7.5% at 2396
MiB, against `two-gathers-ad-orient`'s +22% at 2180 MiB.  What matters
is the granularity of the fragments a predecessor's allocation mix leaves,
and the ad-orient chain — whose smaller slice size sits 10% above
the large-object threshold — is nearly the worst case.

**Why it moved a cross-build A/B.**  Both orthotope builds' `two-gathers` spray
the same ~288 slice vectors per iteration, but the fallback fix cut
the allocation between sprays 4.7× and the iteration time 4× — a ~4× denser
checkerboard laid over ~4× more iterations per criterion budget.  Measured
on both builds: the fixed build's predecessor grows the pool to 2180 MiB
and costs its follower 22%; the released build's leaves 1165 MiB (timeline flat)
and costs +1.1%.  The identical fused code then reads as "18% slower
on the fixed build" exactly and only when two-gathers precede it: cross-build
ratios 1.188 after two-gathers, ~1.0 after a conv predecessor (+7.5% on both
sides, common-mode), 0.98 alone — reproducing the retracted A/B's 1.200 / 0.995
/ 0.98 triple.

## The warm-up ramp is the same mechanism's transient face

`inp-192x192/S-exec-raw`, the documented ramp exemplar, grows the pool itself:
RSS climbs 1.12 → 1.99 GiB during its own first ~1.5 s and plateaus, while
its early samples read 63 → 51 → 40 → 35 → 33 ms against a converged 22.4 ms.
A benchmark that pays for pool growth *inside its own early samples* shows
the ramp — transient, absorbed by criterion's OLS slope-with-intercept, which
is why converged `-A1G` and `-A64m` slopes agree.  A benchmark whose pool
was grown *by a predecessor* starts post-plateau: no faults, no decay, a flat
penalty the slope faithfully reports as real.  One mechanism, two faces —
and the suite's ramp defenses (slope-not-mean, long budgets) are exactly
the ones the persistent face slips past.

## Consequences for measurement practice

**There is no in-process cure.**  Criterion already separates benchmarks
with a major GC (`performGC` at each benchmark's start; minor GCs between
samples — a split that matters only at the object layer, resetting gen-1
accumulation).  No GC moves pinned data or re-carves free-list structure,
and no Haskell-callable RTS facility touches the pool: not the `performGC`
family, not `setNumCapabilities`, not allocation counters, not compact regions,
not `rts_clearMemory`.  Process exit is the only reset.  (A deliberate
*equalizer* — a standard saturating spray before every measured benchmark,
making the poisoned state common-mode — would work in principle; untested.)

**Pinning the selection is necessary but not sufficient.**  It equalizes
the roster, but when the compared builds change a predecessor's own allocation
profile — the fused-gather case — the same roster poisons one build and
not the other.  The red flag is a predecessor whose per-iteration allocation
moved between the builds.

**Decisive numbers come from one process per measured benchmark.**
The fixed-iteration differencing rule (`-n 200` minus `-n 100`, fresh processes)
already embodies this.  Isolation is cheap — `convVjpBench` startup is
under a second — and for benchmarks that do not poison themselves it also buys
budget: isolated fused converges at the default 5 s to within 1% of `-L 15`.
Self-poisoning benchmarks still need their long budgets, because the ramp
is their own: at default budget, isolated, `two-gathers` reads +8%
(and is bimodal across processes, 1.29 vs 1.40 ms clusters) and `S-exec-raw`
reads −15%.  The per-process floor is ±1% for clean benchmarks.  Migrating
the whole suite to per-bench processes (criterion supports it: `benchNames`
is exported, JSON files merge, `criterion-report` renders merged files) would
move position-affected benchmarks by up to ~20% and so requires recalibrating
the numbered properties, whose expectations have the in-process effects baked
in — a deliberate migration, not a drop-in.

**At the source level**, the spray is the interpreted gather's per-position
slice materialization; the C strided-copy path planned in [#123][123] would
write slices straight into the result buffer and remove the fragmentation source
outright — a benefit beyond the copy cost it was priced on.

## micro-regime3

Orthotope's `micro-regime3` suite shows the same physics at a different
operating point, and the comparison between its two harness generations
is the instructive part.

On the current harness, the floor is already sub-1% and isolation buys little:
the three A/A twin pairs, measured over six shapes three times in each regime,
give geomean ratios within ±0.5% of 1.0 both isolated and in-process,
and the full-group reference agrees.  Isolation removes one reproducible
in-process artifact — the scan pair's `cnn-L1-24x24-c1` cell reads −3.8%
in every shared-process run and 1.00 isolated — but introduces the per-process
lottery: one isolated process threw a single shape's cell 5% off.  Both effects
live at the scale the README's "trust the first digit only" per-shape caveat
already covers.

On the pre-`e96948e` harness the picture was different: the same-cell spread
across repeats reached 3.1% in shared-process runs against ≤1.3% isolated,
so the recorded ~2% floor belonged to that era's in-process behavior
and isolation genuinely helped then.  The `e96948e` rework smoothed the suite
to its present sub-1% floor (which of its changes did it is not separable
from these measurements).

The era-independent lesson: **within-process ratios are the sound instrument;
absolute numbers carry the process draw.**  The quasi-tie
`bq-expand-zf`/`bq-expand` ratio taken in-process is stable to a tenth
of a percent even on the noisy old harness, while the same ratio across isolated
processes wanders over a 2% range — two arms sharing a process ride the same
lottery draw and their ratio cancels it.  The suite's one-process,
ratio-to-`list` design was the right call in both eras.

`micro-regime3` never sees the 22% because nothing in it poisons:
its allocations are coarse-grained (whole result vectors and table scratch),
so the pool stays compact and the free lists short.

## Standalone reproducer

The pool doubling reproduces outside horde-ad in ~100 base-only lines:
a fixed-dose poison phase spraying 3600-byte pinned buffers takes the pool
from 1.02 to 2.17 GiB — identically on GHC 9.12.4, 9.14.1 and HEAD
(10.1.20260803, perf-flavour build) — and an identical victim loop then runs
a few percent slower, `-Fd1`-immune everywhere.  The program, its three-compiler
numbers, and the RTS-side analysis are in the [GHC issue draft][ghc-issue].
The repro's small effect size is expected: its victim only *places* fresh
allocations into the fragmented region, where convVjpBench's fused victim
*recycles* a hot ~14 MB/iteration working set through it — the strong form
of the penalty.  One trap the draft records: a quick-flavour GHC build
(unoptimized boot libraries) fails to reproduce either symptom — the inflated
per-allocation overhead triggers collections that cap the spray accumulation —
so only optimized builds arbitrate.

## Provenance

Everything above was measured 2026-08-03 on the development machine (Ryzen 7
5800X, 32 MB L3, 62 GB RAM, Linux 6.17), GHC 9.12.4 — the standalone reproducer
additionally on GHC 9.14.1 and on HEAD 10.1.20260803, perf-flavour build —
criterion 1.6.5.0 / criterion-measurement 0.2.5.0, `convVjpBench` built `-O1`
with `-A1G -I0`; the fixed build links the `speedup-strided-tovector` orthotope
checkout, the released build Hackage orthotope 0.1.8.0.  Instruments: criterion
per-iteration OLS slopes (all fits R² ≥ 0.99), `+RTS -s`, `/usr/bin/time -v`,
`/proc/<pid>` RSS/AnonHugePages timelines (transparent huge pages were 0
throughout — eliminated as a factor), and root `perf stat` (hardware counters
are blocked for unprivileged sessions on this machine by `perf_event_paranoid`).
Criterion's GC placement (major per benchmark, minor per sample) was read
from the criterion-measurement 0.2.5.0 source.

[ghc-issue]: ghc-issue-block-pool-fragmentation.md
[123]: https://github.com/Mikolaj/horde-ad/issues/123
