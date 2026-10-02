# Pragmas and optimisation flags: which ones pay for their compile time

The question: which of horde-ad's inlining and specialisation pragmas, and which
of the package-wide optimisation flags in the `.cabal` file, are worth what they
cost in compile time, under the rules in `CLAUDE.md` (Pragmas and optimisation
flags). In short: run time is traded against the optimised build of every
component of the package; the speed of computing on concrete values ---
interpretation, `interpretAst` and the `Concrete` instances it calls,
and the non-symbolic pipeline, `cgrad` and its kin with the `ADVal` instances
and the delta evaluation --- may not drop, with 10% as the noise margin
for that verdict; the speed of simplification may be traded, counting only
changes above 2%; every pragma is itself a cost; and a pragma that is dead only
at today's inliner thresholds stays.

The change this document reports removes 165 pragmas and the flag
`-flate-dmd-anal`. The whole package builds in 1086 s instead of 2485 s, 56%
less, nearly all of it outside the library, which drops from 624 s to 510 s.
No benchmark allocates 2% more than before, and on the rows measured
with cachegrind no benchmark executes 3% more instructions. Every other pragma
examined and every other flag stays, each for a measured reason given below,
except where the only reason is the threshold rule.

## Setup

GHC 9.14.1, the newest of the three CI builds with, and the only one measured;
ox-arrays and orthotope from Hackage, no sibling checkouts; a 4-core, 15 GB
cloud VM with no hardware performance counters, restarted several times during
the work on hosts whose kernel changed. The baseline is the tree at `5535dee`,
whose code the branch still carried. Every build was optimised with exactly
the `.cabal` flags and a `cabal.project.local` of `tests: True`
and `benchmarks: True` alone.

The instruments are those of `docs/overloaded-unfoldings.md`, in the same order
of trust, plus one:

1. Allocation per iteration on the four suites `shortProdForCI`, `convVjpBench`,
   `inlineMicroBench` and `shortMnistForCI`. Exact, and host independent ---
   but blind to some changes, below.
2. Instructions and estimated cycles per call
   from `tools/cachegrind-per-call.py`, on eight fixed rows: `gather48`
   and `scatter48`, `cnn-6x6` and `cnn-12x12` execution, `100/cgrad k list`,
   and three MNIST rows. Instructions decide: on `gather48` the cycle estimate
   moved by up to 9% between two builds whose instruction counts agreed
   to 0.03%, the cache simulation being sensitive to code layout.
3. Build time: `/usr/bin/time -v` around `cabal build lib:horde-ad`
   and then `cabal build all`, in a fresh `--builddir`, one build at a time
   on an otherwise idle machine, without `jobs` or `semaphore`. Two builds
   of the unmodified baseline differed by 3.4% in total (2444 s and 2526 s),
   and the baseline figure below is their mean; a third build of the baseline
   library, the one in the example-`SPECIALISE` row below, took 6% longer still,
   so a difference under about 6% is not read as one.
4. `tools/pragma-calls.py`, new with this work, which sorts the pragmas a diff
   removes into those whose removal leaves every module's Core mentioning
   the target the same number of times (DEAD) and those whose removal does
   not (MOVED), naming the modules that moved.

## Method

Pragmas were taken in groups, by module and role. For each group:

1. Remove every pragma of the group and build with `-ddump-simpl` dumps.
2. Run `tools/pragma-calls.py` against the baseline dumps. A DEAD pragma stays
   whatever else happens, by the threshold rule: its target is inlined anyway,
   or not inlined anyway, only at today's thresholds.
3. Build the MOVED subset alone and screen its allocation. A regression above
   the margins is bisected until the pragmas carrying it are found; those stay.
4. Measure instructions on the rows allocation cannot see.
5. Combine the survivors, repeat 3 and 4 on the combination, and time its build.

Flags were each removed, or for `-O2`, `-fspec-constr` and `-fliberate-case`
added, one at a time over the whole package, and screened the same way; the two
that looked removable were then re-priced on top of the pragma removals, which
changed the verdict on one of them.

## What goes

| Module | Pragmas | What removing them does |
|---|---|---|
| `Core/OpsConcrete.hs` | 115 `INLINE` | Core 0.36, the test libraries' 0.28 and the library's 0.73; see below |
| `Core/Ops.hs` | 21 `INLINE` | Core 0.92 with `OpsTensor`'s two; allocation unchanged, instructions within 0.1% |
| `OpsTensor.hs` | 2 `INLINE` (`rfold`, `rscan`) | as above |
| `ADEngine.hs` | 12 `INLINE` | Core 0.83; allocation unchanged |
| `Core/AstInterpret.hs` | 3 `INLINE` (`interpretAstDual`, `interpretAstR1`, `interpretAstR2`) | Core 0.99; allocation unchanged, instructions within 0.03% |
| `example/MnistData.hs` | 8 `SPECIALISE` | Core 0.96 with `MnistFcnnRanked1`'s four, `MnistData`'s own 0.59; rank-1 VTA MNIST −1.7% allocation |
| `example/MnistFcnnRanked1.hs` | 4 `SPECIALISE` on `afcnnMnistLoss1`, plus a commented-out one | as above |

"Core" is the size of the optimised Core summed over every module
of the package, in terms, as a ratio against the baseline
(`tools/core-diff.py`).

The `OpsConcrete` pragmas removed are of two kinds. 105 are on the `Concrete`
instance methods and helpers whose removal changed the Core, minus the index,
gather and scatter family: every test, benchmark and example module
that computes at `Concrete` had inlined them at each call site, which is where
most of the build time went. The other ten are on the dispatchers
of that family, `tindexZR`, `tindex0R`, `tscatterZR`, `tgatherZR`
and `tgatherZ1R` and their shaped twins, which choose a specialised kernel
by the element type through `contFromTKAllNum` and `contFromTypeable`. Those two
keep their `INLINE`, which the specialisation needs: removing it costs
`gather48` 2.5% allocation and 6.8% instructions. With the dispatchers inlined
too, though, each user call site received the whole case over the element types,
and that cost 309 s of package build (1380 s against 1071 s in the build-time
table below); without their `INLINE` the case expands once, in `OpsConcrete`,
and `gather48` and `scatter48` stay within 0.1% of the baseline in allocation.

The `ADEngine` pragmas are on the artifact-building and artifact-interpreting
functions (`gradArtifact`, `gradInterpretArtifact`, `vjpInterpretArtifact`,
`revArtifactAdapt`, `revInterpretArtifact`, `revArtifactAdaptDt`,
`revInterpretArtifactDt`, `revArtifactDelta`, `forwardPassByApplication`,
`fwdArtifactAdapt`, `fwdInterpretArtifact`, `fwdArtifactDelta`).

One printed-AST test, `4S0rmapAccumRD01SN531b0PP` in CAFlessTest, now fails
on 9.14.1 in variable numbers only. Its expectation is not refreshed, per
`test/CLAUDE.md`: fresh-variable numbers are the compiler's, and move between
GHC versions and optimisation settings anyway.

## What stays, and why

| Pragmas | Without them |
|---|---|
| `grad2`, `vjp2`, `jvp2` in `ADEngine` | `pitfalls/S-fullpipe-hoisted` +67%: full laziness no longer hoists the artifact out of the loop |
| `simplifyUserCode`, `simplifyInlineContract` (`AstEngine`), `forwardPassByInterpretation` (`OpsAst`) | `grad` +1 to +4.4% allocation, Core unchanged |
| `cgrad` and the rest of the entry points in `ADEngine` and `OpsADVal` | DEAD by count; the group as a whole costs `cgrad` 12--17% |
| `tappend`, `tunravelToListShare`, `rsize`, `ssize`, `xsize` in `Ops` | the `tsize` default reaches `rsize` and its kin through a dictionary; `inlineMicroBench` +78% |
| the index, gather and scatter kernels in `OpsConcrete`, with `contFromTKAllNum` and `contFromTypeable` | `gather48` +5.5% allocation |
| `interpretAstHFun` in `AstInterpret` | nothing on 9.14.1, but its comment records up to 43% more allocation on GHC HEAD |
| the helpers in `AstEnv`, `AstFreshId`, `AstMethod*`, `AstSimplify`, `PP*`, `Types` and the rest | Core unchanged, so nothing to gain; `grad k MapAccum` up to 6.6 times the allocation when all go |
| `INLINABLE interpretAst` | MNIST VTO up to +10% |
| `SPECIALIZE instance` in `Adaptor` | rank-2 VTC compilation 1.8--2.3 times the allocation |
| `afcnnMnistLoss2`'s three `SPECIALISE`s | rank-2 VTA training +2.1--2.5% allocation, +5.8% instructions |
| `mnistTrainBench2VTOGradient` and its `X` sibling's `SPECIALISE`s, and those in tests and benchmarks | they carry the VTC figure above too |
| the cold-path `NOINLINE`s (`*Slow`, three in `CarriersConcrete`) | DEAD by count |

`INLINE [1]` on the `tscatterZ*Dict` functions could become plain `INLINE`
for 2% less Core with no allocation change; it stays, the phase having
been chosen for robustness rather than speed.

## Flags

| Flag | Change | Effect |
|---|---|---|
| `-flate-dmd-anal` | removed | instructions unchanged on every row, allocation unchanged, wall time over all 204 rows −0.3%; package build −9% on the baseline and −5.6% on top of the pragma removals |
| `-fworker-wrapper-cbv` | kept | without it `gather48` +3.8% instructions, `scatter48` +2.2%, `cnn-6x6` +2.1%, `100/cgrad k list` +3.8%, at unchanged allocation; its build cost, 17% on the baseline, is within noise once the pragmas go |
| `-fspecialise-aggressively` | kept | `cgrad` +48% without it |
| `-fpolymorphic-specialisation` | kept | `grad k MapAccum` +41% without it |
| `-fdicts-cheap` | kept | `grad k MapAccum` 6.4 times without it |
| `-fkeep-auto-rules` | kept | `grad` +2--8% without it |
| `-O2` | not added | `cgrad k MapAccum` −1.1 to −1.4%, micro-benchmarks up to −5%: under 2% on everything but micro-benchmarks, so its constituents were not bisected |
| `-fspec-constr` | not added | the same −1.1% on `cgrad` |
| `-fliberate-case` | not added | no effect |

`-fworker-wrapper-cbv` makes workers take strict arguments evaluated, which
saves evaluation checks and allocates nothing either way; allocation screening
passed its removal, and only the instruction counts caught the cost. On GHC HEAD
it also stops importers from specialising what a worker calls, GHC
[#27874](https://gitlab.haskell.org/ghc/ghc/-/work_items/27874), where the fix
makes a CAFlessTest build with the flag 25% faster than one without it;
on 9.14.1 CAFlessTest's mutator time does not move with this commit.
`-flate-specialise` was not measured; the `.cabal` file's comment on it stands.

`-flate-dmd-anal` was measured again on top of the pragma removals,
with interleaved builds and interleaved wall-time pairs. Four builds
in the order without, with, with, without put its cost at 5.9% of the package
build (library +5.0%, the rest +6.5%), so removing it saves 5.6%, not the 8%
of the single build in the table below. Its wall time over every row of the four
suites, the median of four palindromic pairs per row, has a geometric mean
of +0.3%, the rows ranging from −10% to +14%. CAFlessTest, a test suite rather
than a benchmark, ran 12% slower with it: the flag exposes GHC
[#27885](https://gitlab.haskell.org/ghc/ghc/-/work_items/27885), which makes
the loop of the backward pass non-tail recursive, and every `unsafePerformIO`
drawing a fresh identifier then walked the deep stack in the runtime's
`threadPaused`. Drawing them under `unsafeDupablePerformIO` instead (the module
header of `HordeAd.Core.AstFreshId`) brings the flag's cost on CAFlessTest
to 1%, and the fix proposed in that issue removes the stack growth itself.
On GHC HEAD (commit `234bab0816` with the fixes of #27873 and #27874) the flag
costs 8.7% of the build and its wall time over the 204 rows has a geometric mean
of +0.2%.

## Build time

| Build | Library | Rest of package | Total | Library peak memory |
|---|---|---|---|---|
| baseline, mean of two | 624 s | 1861 s | 2485 s | 3.07 GB |
| this commit | 510 s | 576 s | 1086 s | 3.01 GB |
| this commit with `-fworker-wrapper-cbv` dropped too | 504 s | 568 s | 1071 s | 3.14 GB |
| this commit with the ten dispatchers still `INLINE`, and `-fworker-wrapper-cbv` dropped | 510 s | 870 s | 1380 s | 2.99 GB |
| this commit with `-flate-dmd-anal` kept | 555 s | 622 s | 1177 s | 2.95 GB |
| `OpsConcrete`'s 105 method removals alone | 610 s | 1297 s | 1907 s | 3.10 GB |
| the example `SPECIALISE` removals alone | 662 s | 1976 s | 2638 s | 3.18 GB |
| `-fworker-wrapper-cbv` removed alone | 580 s | 1485 s | 2066 s | 2.61 GB |
| `-flate-dmd-anal` removed alone | 566 s | 1701 s | 2266 s | 3.03 GB |

Times are wall clock; user time is within 1% of it for the library and 20% above
it for the rest, where cabal builds components in parallel. The build
of this commit was taken before `interpretAstHFun` got its `INLINE` back, which
changes 0.01% of the Core. The example `SPECIALISE`s go for the Core
and the allocation they save, not for build time, which does not move beyond
the noise.

## Speed of this commit

Allocation against the baseline, every row of the four suites: nothing above 2%.
The largest are `cnn-6x6` execution +1.4 to +1.6%, rank-2 VTA MNIST training
+1.0 to +1.2%, `100/cgrad k list` +0.9% and `cnn-12x12` +0.7%; `gather48`
and `scatter48` within 0.1%.

Instructions and estimated cycles per call, as ratios against the baseline:

| Row | Instructions | Cycles |
|---|---|---|
| `gather48/fused-gather-ad-orient` | 1.000 | 1.058 |
| `scatter48/fused-scatter-ad-orient` | 1.000 | 0.999 |
| `cnn-6x6/S-exec` | 1.012 | 1.012 |
| `cnn-12x12/S-exec` | 1.006 | 1.007 |
| `100/cgrad k list` | 1.008 | 1.009 |
| rank-1 VTA MNIST training, 30\|10 | 1.015 | 1.005 |
| rank-2 VTA MNIST test, 30\|10 | 0.997 | 0.984 |
| rank-2 VTA MNIST training, 30\|10 | 1.027 | 1.019 |

`gather48`'s cycle figure is the layout wobble of the Setup section:
its instruction count is the baseline's to 0.02%. The rank-2 training row
is the only one above 2%; it comes from the pragma removals, not the flags,
the builds with and without `-fworker-wrapper-cbv` agreeing on it to 0.4%,
and is far inside the 10% margin.

CAFlessTest, once through, allocates 6.4% more than the baseline (407 GB against
383 GB); its mutator time did not move over three interleaved pairs
with `-fworker-wrapper-cbv` dropped, and is lower in the one run with it.

## Pitfalls met

- Allocation screening is blind to `-fworker-wrapper-cbv`: removing it left
  every allocation figure but one unchanged while adding up to 3.8%
  to the instructions of the gather and `cgrad` rows. Price a flag that changes
  evaluation rather than allocation with instructions.
- A flag's build cost is not a constant: `-fworker-wrapper-cbv` cost 17%
  of the baseline's build and nothing measurable after the pragma removals,
  which took away most of the Core it worked on.
- A DEAD verdict from `tools/pragma-calls.py` is weaker than identical Core.
  The `rsize` family read DEAD and still cost a micro-benchmark 78%: the `tsize`
  default method calls it through a dictionary, and what changed
  was the unfolding the default carried, not any call site the count sees.
- A name filter over `OpsConcrete`'s pragmas, meant to keep the gather family,
  missed `contFromTKAllNum` and `contFromTypeable`, which specialise
  it under other names; only the benchmark showed it.
- A pragma can be live on another GHC: `interpretAstHFun`'s `INLINE` does
  nothing measurable on 9.14.1 and was removed by the screen until its comment
  was read.
- Multi-line `SPECIALISE` pragmas defeat a line-based `sed`, leaving a parse
  error; they were removed whole, with a regular expression over the file.
- Screening builds run side by side ran the machine out of memory twice; every
  figure above comes from a run that completed, and every build time
  from a build run alone.

## Not measured

- GHC 9.12.4 and 9.10.3, and GHC HEAD.
- Wall time as interleaved A/B pairs on the benchmarks: allocation
  and instructions settled every row, none coming near the 10% margin.
- `longProdBench`, `longMnistBench`, and the test suites beyond `minimalTest`
  and `CAFlessTest`; `parallelTest` is never run from a session.
- `hlint`, which is not installed in the container this ran in; the change
  deletes lines and edits one `.cabal` comment. stylish-haskell likewise, and CI
  runs it.
- `-flate-specialise`, by instruction for this work.
- The pragmas the earlier study of `docs/overloaded-unfoldings.md` settled:
  `INLINABLE` on `astPlusK` and `astTimesK`, and the modules' opt-outs.
