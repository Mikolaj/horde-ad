# Exposing overloaded unfoldings: which modules, which pragmas, at what cost

The question: in the modules that opt out of the package default
`-fexpose-overloaded-unfoldings`, which functions should get a pragma to improve
performance, and how large would each improvement be. During the work
the question widened to any change that improves the trade-off between run time
and horde-ad's own optimised compilation time, in either direction, under three
rules. Interpretation --- `AstInterpret` and everything it calls, the Concrete
instances, and, for the non-symbolic `cgrad` pipeline, the ADVal instances ---
may not get slower than the branch tip by more than 10% in wall time
or estimated cycles on any benchmark. Simplification --- the smart constructors,
the traversals, vectorisation and inlining --- is fair game for trade-offs,
which count only changes above 2%. And a light compile-time cost is acceptable
for a large speed gain, not the other way around. Where one module-level flag
and a dozen pragmas do the same job, the flag is preferred.

The outcome is the commit that adds this document, which also adds the opt-out
to five more modules, `OpsConcrete`, `CarriersConcrete`, `CommonRankedOps`,
`CommonShapedOps` and `ADEngine`: 5% off the whole package build, 22% off
the library's peak memory, no benchmark slower. In the nine existing opt-out
modules, exposure buys something in `AstSimplify` alone, so a pragma elsewhere
has nothing to recover; the gain in `AstSimplify` is blocked by GHC behaviour
recorded in `docs/ghc-issue-partial-specialisation-no-unfolding-comment.md`,
no pragma tried recovers it, and the only lever that does costs 1.8 times
the package build.

## Setup

GHC 9.14.1, the newest of the three CI builds with, and the only one measured;
ox-arrays 0.2.0.1 and orthotope 0.1.8.0 from Hackage, no sibling checkouts;
a 4-core, 15 GB cloud VM with no hardware performance counters. The baseline, R,
is the branch at `0f9d563`. Every build was optimised with exactly the `.cabal`
flags and a `cabal.project.local` of `tests: True` and `benchmarks: True` alone:
`jobs` and `semaphore` skew the timing, and early timings taken with them
were discarded and re-taken. Build times come from single builds in fresh build
directories on an otherwise idle machine; two library builds of the same tree,
in the discarded semaphore series, differed by 0.8%.

Speed was measured with three instruments, in this order of trust; the last two
are `tools/cachegrind-per-call.py` and `tools/ab-time.py`, and the attribution
below used `tools/ticky-diff.py` and `tools/core-diff.py`:

1. Allocation per iteration, from criterion's `--regress allocated:iters`
   with `+RTS -T`, on all four suites: `shortProdForCI`, `convVjpBench`,
   `inlineMicroBench` and `shortMnistForCI`. Exact: an unmodified control build
   reproduced R's figures to the byte. Unrelated edits can still move a row
   by up to 1.5%, so 0.5% is the noise margin.
2. Estimated cycles per call, from cachegrind with cache simulation, Ir + 10 *
   (I1mr + D1mr + D1mw) + 100 * (ILmr + DLmr + DLmw), as the difference
   of an `--iters 2N` and an `--iters N` run divided by N. It replaces
   `perf stat`, which the VM does not support, and is deterministic.
3. Wall time, only as interleaved A/B pairs, one benchmark per process, reading
   criterion's per-iteration slope and taking the median of the per-pair ratios.
   Single pairs scatter from 0.42 to 1.36 on this VM, so only medians are read.

## The nine existing opt-outs

X is R with all nine opt-out blocks removed. On `shortProdForCI` it allocates
less on four rows and the same elsewhere; `convVjpBench` moves within 0.2%
and `inlineMicroBench` not at all:

| Benchmark | R bytes/iteration | X / R | AstSimplify alone / R |
|---|---|---|---|
| `100/grad k list` | 5,796,093 | 0.9729 | 0.9729 |
| `100/grad k L` | 8,841,658 | 0.9822 | 0.9822 |
| `1000/grad k L` | 752,940,160 | 0.9753 | 0.9755 |
| `100/grad s L` | 28,072,211 | 0.9943 | 0.9940 |

Removing only `AstSimplify`'s block reproduces all of it. The costs, in fresh
build directories without the semaphore:

| Build | Library wall | Library user | Library peak | Rest wall | Rest user | Rest peak | `.hi` bytes |
|---|---|---|---|---|---|---|---|
| R | 628 s | 625 s | 3.70 GB | 1858 s | 2274 s | 3.59 GB | 8.33 MB |
| AstSimplify's block removed | 1446 s | 1428 s | 4.96 GB | 3069 s | 3536 s | 4.89 GB | 13.38 MB |

That is 1.8 times the whole package build for 2 to 3% less allocation on four
simplification-heavy rows, so the lever is rejected. X itself, timed
with the semaphore, cost 2.1 times the library build and ran out of memory
building the test library at four jobs.

Two of the nine blocks do nothing on this compiler: `CarriersAst`'s interfaces
with and without it differ only in source line numbers, and `AstMethodLet`'s
only through `AstSimplify`'s hash. They cost nothing either, so they stay.

The dump diff shows where the cost goes. With `AstSimplify` exposed, its own
Core does not change, but its consumers' does: `AstVectorize`'s grows 37-fold,
`AstTraverse`'s 9-fold, `OpsAst`'s 4.5-fold and the MNIST example modules'
3-fold, 2.3-fold over the package. The specialisations fix a smart constructor's
element type or span at every call site; `AstTraverse` alone gets 168 copies
of `astTransposeS`.

## Where the gain comes from, and why no pragma recovers it

A ticky-ticky profile of 200 iterations of `100/grad k L` in R and
in the `AstSimplify`-only build attributes the whole difference, 31.5 MB, to one
function. In R, `AstSimplify.$w$w$sastTimesK` is entered 2.18 million times
and allocates 106 MB; in the other build, a copy that `OpsAst` specialises
further, `$w$w$s$w$w$sastTimesK`, takes over those calls and allocates 63 MB.
`AstSimplify`'s copy is specialised on the span but still takes the `NumScalar`
dictionary; `OpsAst`'s is specialised on both, at `Double` and `PrimalStepSpan`.

`astTimesK` already has an `INLINABLE` pragma, so its unfolding is exported
in R. What blocks the importer is a rule: with `-fkeep-auto-rules`,
`AstSimplify` exports `SPEC astTimesK @_ @(PrimalStepSpan FullSpan)`, which
fires in the importer while the element type is still unknown and sends the call
to the partial specialisation, whose worker has no unfolding. R's one
`-Wmissed-specialisations` warning names it. The mechanism, with a two-module
reproducer, is recorded as a comment on GHC
[#23050](https://gitlab.haskell.org/ghc/ghc/-/work_items/23050); the missing
unfolding is intended by GHC.

These remedies were tried and measured, and none recovers the gain:

| Lever | Effect on the four rows |
|---|---|
| `SPECIALISE` at `Double`, 24 entry points of `AstSimplify` | none; 0.1 to 1.5% more allocation, these rows included |
| `SPECIALISE` at `FullSpan`, 49 entry points | none |
| `SPECIALISE astTimesK @Double` at each of the four span forms | none; up to 0.9% more allocation |
| `SPECIALISE` at `Int` and `PlainSpan`, one or five functions | none, or 0.5% on one row |
| `INLINABLE` on `astTimesK` and its cluster | already present on `astTimesK` and `astPlusK` |
| `-fno-keep-auto-rules` on `AstSimplify` | none |
| `-fno-keep-auto-rules` on all nine opt-out modules | 2 to 8% more allocation |

A `SPECIALISE` rule in the defining module cannot match the hot call:
the element type is known at the call site only after the importer has
specialised the chain above it, which needs exactly the unfolding the opt-out
withholds. The auto-rules help more than the one dead end costs, which the last
row shows. The workaround GHC's own design leaves is to expose the defining
module's overloaded unfoldings, the rejected lever above.

## Extending the opt-out

Y, the opt-out in all 32 library modules that lack it, regresses badly:
`cgrad k` allocates 17 to 23% more, the fused gathers 17.5%, MNIST VTO up
to 38%. The fourteen of the 32 whose interfaces Y shrinks by more than 2 KB
were bisected in groups, then singly where a group failed; the other eighteen
barely change under the flag and cannot save compile time. Allocation, all four
suites:

| Modules | Result | Verdict |
|---|---|---|
| `OpsConcrete`, `CarriersConcrete` | within 0.13% | kept |
| `CommonRankedOps`, `CommonShapedOps` | within 0.4% | kept |
| `ADEngine` | within 0.25% | kept |
| `AstInterpret` (with `ADEngine`; `ADEngine` alone is clean) | MNIST VTO up to 38% more, exec rows 1% | rejected |
| `OpsADVal` | ADVal `tsize` 33% more, 2.2 times the time | rejected |
| `DeltaEval` | `cgrad` up to 10% more, MNIST VTA 2.3 to 2.6% | rejected |
| `Unwind`, `UnwindNum` | `cgrad` 1.6 to 5.9% more | rejected |
| `Adaptor`, `AstTools`, `Conversion` | `cgrad` 2 to 6% more | rejected |
| `Delta` | within 0.13% | neutral, but no measurable saving |

The five kept modules together, Z, allocate within 0.39% of R on every
benchmark. Build costs:

| Build | Library wall | Library user | Library peak | Rest wall | Rest user | Rest peak | `.hi` bytes |
|---|---|---|---|---|---|---|---|
| R | 628 s | 625 s | 3.70 GB | 1858 s | 2274 s | 3.59 GB | 8.33 MB |
| Z | 603 s | 587 s | 2.90 GB | 1760 s | 2142 s | 3.38 GB | 7.85 MB |
| Z and `Delta` | 594 s | 587 s | 3.00 GB | 1779 s | 2157 s | 3.41 GB | 7.82 MB |

Wall time on 65 interpreting and evaluating benchmarks --- the 13 `cgrad` rows,
the exec rows of four conv sizes, `gather48` and `scatter48`, four MNIST rows
and the 19 Concrete and ADVal micro-benchmarks --- five interleaved pairs each:
medians of Z / R between 0.90 and 1.06. The four highest conv medians, 1.05
to 1.06, were checked with estimated cycles: Z / R is 0.9997 to 1.0050,
the instruction counts equal to 0.003%. So the wall-time spread is the VM's
noise, and the change is neutral for speed.

The build and both `minimalTest` (75 tests) and `CAFlessTest` (672 tests) pass
optimised on the committed tree; Haskell-CI passed on it for all three
compilers.

`OpsConcrete`'s opt-out was dropped again on 2026-10-02, together with 43
of the pragmas that the change in `docs/pragmas-and-flags.md` removed from
it, for CAFlessTest's allocation; that document has the measurements.

## Pitfalls met

- `ghc --make` does not recompile a module when only `-fkeep-auto-rules`
  or `-fpolymorphic-specialisation` changes, though both change what it exports;
  it does for `-fspecialise-aggressively`. A reproducer built with `--make` gave
  wrong answers until each module was compiled with `-c`.
- `-ddump-simpl -dsuppress-all` drops the per-binding size comments;
  the module's "Result size of Tidy Core" line still gives the total.
- A ticky build needs `--ghc-options=-ticky` for the library and the executable
  both; its per-closure names differ between builds only in unique suffixes,
  which normalise away.
- The container here was restarted several times, killing background jobs; every
  result above comes from a run that completed.

## Not measured

- GHC 9.12.4 and 9.10.3. On 9.10.3 the flag does not exist and the blocks do
  nothing.
- `longProdBench`, `longMnistBench` and the test suites other than the two
  above; `parallelTest` is never run from a session.
- `hlint`, which no released binary parses here; the change adds header pragmas
  only. stylish-haskell 0.15.1.0, the version CI pins, leaves the five files
  unchanged.
- The effect on a user's own code beyond the benchmarks, which the `ADEngine`
  opt-out could reach, since user code calls `grad` and its kin. The benchmarks
  that call them show no difference.
