# Comment 1 for #123 (draft): the measurements, redone with criterion

*(First of three consecutive comments planned for
https://github.com/Mikolaj/horde-ad/issues/123: measurements, diagnosis,
design. Benchmark numbers and source references are from the drafting
sessions and will be refreshed just before posting.)*

First, a note on instruments, because it changes what the ticket's headline
number means. The ticket's 0.23s vs 0.07s (the 3.3x) are tasty poor man's
benchmark totals: wall-clock over 100 QuickCheck runs, including per-run
random data generation and the `allClose` check, on a coarse ~10ms timer.
That is a different quantity from a per-call time, and it is not portable
across machines, GHC versions or commits, so it is treated as anecdotal
below. Every figure in these comments comes from criterion (the diagnostic
benchmark `bench/ConvVjpBench.hs`, added in #128 and fixed up in #129):
per call, GHC 9.12.4, `-O1`, single-threaded. (Besides the `conv2dPreservingS`
variants analysed here, the same benchmark carries `cnn-*` groups timing a
real shaped two-layer CNN gradient — see the design comment for the fix's
effect there.)

The benchmark separates the cost of the symbolic pipeline (tracing + AD +
simplification, paid on every `vjp` call) from the cost of executing the
resulting gradient program, at several image sizes
(`nImgs = nCinp = nCout = 3`, `nKh = nKw = 3`, `nAh = nAw` varying). The
table is the baseline *before* the fix designed in the follow-up comments;
findings 1-3 analyse it, and finding 4 covers the input gradient, measured
the same way.

| nAh=nAw | S-exec | S-exec-raw | H-exec  | H-exec-contracted | H-exec-var | S-fullpipe | H-fullpipe |
|---------|--------|-----------|---------|-------------------|------------|------------|------------|
| 6       | 192µs  | 217µs     | 215µs   | 192µs             | 217µs      | 393µs      | 475µs      |
| 24      | 1.84ms | 1.95ms    | 1.64ms  | 1.54ms            | 1.55ms     | 2.02ms     | 1.94ms     |
| 48      | 7.30ms | 7.62ms    | 6.31ms  | 5.75ms            | 5.68ms     | 7.43ms     | 6.47ms     |
| 96      | 32.1ms | 34.7ms    | 26.1ms  | 22.6ms            | 23.1ms     | 32.3ms     | 26.3ms     |
| 192     | 133ms  | 148ms     | 105ms   | 97.1ms            | 97.2ms     | 132ms      | 105ms      |

Variant key:
- **S-fullpipe** — `vjp f arrK dt` per call with only `dt` varying. Since
  the artifact depends on `f` and `arrK` but not `dt`, and the `vjp` stack
  is `INLINE`, GHC floats the artifact construction out of the timed loop —
  so this column is a *lower bound* that under-measures the true per-call
  cost. See `S-fullpipe-honest` in finding 2 for the number the tasty
  `Symbolic` test actually reports.
- **S-exec** — artifact produced and simplified once, only
  `vjpInterpretArtifact` per call (the intended usage pattern of symbolic AD).
- **S-exec-raw** — same, but the artifact is not simplified.
- **H-fullpipe** — `interpretAstFull emptyEnv (conv2dPreserving_dKrn …)` per call,
  i.e., what the `HandwrittenVectorized` QuickCheck test measures. Here the
  varying input feeds term construction, so nothing floats out and this is
  an honest per-call measurement (which is why H-fullpipe and S-fullpipe are
  not directly comparable — only S-fullpipe is hoisted).
- **H-exec** — the handwritten term built once, only interpreted per call.
- **H-exec-contracted** — ditto after `simplifyInlineContract`.
- **H-exec-var** — the handwritten term with the incoming cotangent kept as
  a *variable* (like in the artifact) rather than an embedded constant,
  contracted, interpreted with an environment binding. This is the
  apples-to-apples comparison against S-exec.

## Findings

1. **Under the intended usage — build the derivative artifact once,
   interpret it many times — the symbolic gradient is already at least as
   fast as the handwritten-vectorized code** (S-exec 192µs vs H-exec 215µs
   at 6×6). The 3.3× the ticket reports is real, but it measures a
   *different quantity*: the tasty poor man's benchmark calls full `vjp` on
   every run with the per-run random input baked into the objective
   function, so it rebuilds and re-simplifies the derivative artifact each
   time. That artifact construction is a roughly size-independent tax
   (~370µs, measured in finding 2) which symbolic AD is designed to pay
   once and amortize — a per-call benchmark defeats the amortization. At
   the ticket's small size the fixed tax roughly doubles the symbolic time
   and is essentially the whole gap, while handwritten-vectorized builds a
   trivial term and barely pays it. So the poor man's benchmark was
   accurate, not noisy; it just measures rebuild-every-call, a usage
   pattern no real code employs.

2. **The artifact-build tax is ~370µs per call and roughly
   size-independent.** A controlled experiment (`S-fullpipe-honest` vs
   `S-fullpipe-hoisted` in `bench/ConvVjpBench.hs`): one criterion
   benchmark rebuilds the artifact every call by baking the per-call input
   into the objective, exactly as the tasty benchmark does; the other
   varies only the cotangent `dt`, on which the artifact does not depend,
   so GHC's full-laziness floats the (INLINE'd) construction out of the
   timed loop. The gap between them is the build+simplify cost:

   | nAh=nAw | honest rebuild | artifact floated out | difference |
   |---------|---------------|----------------------|------------|
   | 6       | 767µs         | 393µs                | 374µs      |
   | 24      | 2.39ms        | 2.02ms               | 373µs      |
   | 48      | 7.84ms        | 7.43ms               | 407µs      |

   The build cost stays ~370µs because the derivative *term* has the same
   structure at every size (only the embedded shape constants change); it
   dominates at 6×6 (doubling the time), is ~5% at 48×48, and disappears
   into the noise at 96 and 192 (where honest and hoisted differ by less
   than run-to-run variance). The honest ~770µs is the real per-call cost of
   the rebuild-every-call pattern; a tasty `Symbolic` total corroborates it
   only anecdotally (~0.09s / 100 runs, the rest being per-run random
   generation and `allClose` on a coarse timer — not a like-for-like). Under
   build-once usage this tax is paid once and vanishes.

   This puts the ticket's headline 3.3× in context. Measured here with
   criterion, the honest rebuild-every-call ratio is only ~1.6× at 6×6
   (symbolic honest 767µs vs H-fullpipe 475µs) — a ratio of the form
   `(build_tax + interp) / (build_hw + interp)`, dominated at 6×6 by the
   build tax and vanishing entirely under build-once usage. The ticket's
   3.3× is a *tasty* number and so anecdotal only: a different instrument
   (wall-clock / 100 runs, including per-run generation and `allClose`) and
   from ~11 months / 717 commits earlier, hence not a like-for-like with the
   criterion ~1.6× here. It is not a machine, GHC, or ranked-vs-shaped
   difference — the ticket's `Bench dKrn Symbolic` property at the
   referenced commit (a21d3abf, 2025-08-05) is byte-for-byte the same shaped
   `vjp (\`conv2dPreservingS\` sconcrete arrA) …` measured here. The residual gap
   between the two figures is attributable to the intervening engine work:
   the artifact/simplify pipeline was substantially reworked (the v0.3.0.0
   "extensive performance rework" and everything since), which is exactly
   where a build-tax-dominated per-call ratio shrinks, while
   interpretation-dominated execution — the bulk of the handwritten cost — is
   unchanged over that period. A criterion GC-nursery experiment rules out
   allocation-area effects (a 250× smaller `-A4m` nursery leaves the ~1.6×
   unchanged).

3. **A real execution-cost gap exists, grows with size, then levels off**:
   at 48×48 the symbolic gradient runs ~29% slower than the handwritten one
   (S-exec 7.30ms vs H-exec-var 5.68ms), reaching ~1.39× at 96×96 and holding
   there (~1.37× at 192×192, 133ms vs 97.2ms). It *converges* rather than
   diverging because both programs scale ~linearly in image area at these
   sizes (≈×4 per ×4 area), so their ratio tends to a constant. Where the
   gap physically lives — and why the plateau sits at ~1.37× — is the
   subject of the next comment.

4. **For the input gradient (`dInp`, the `sscatter` path) the symbolic
   artifact is already well ahead of the handwritten gradient**, and — as in
   the kernel case — the ratio converges as size grows:

   | nAh=nAw | S-exec  | H-exec-var | S/H   |
   |---------|---------|------------|-------|
   | 6       | 76µs    | 163µs      | 0.46× |
   | 24      | 374µs   | 1.00ms     | 0.37× |
   | 48      | 1.09ms  | 3.58ms     | 0.30× |
   | 96      | 3.66ms  | 13.96ms    | 0.26× |
   | 192     | 14.74ms | 56.95ms    | 0.26× |

   The symbolic gradient is 2–4× *faster*, the lead growing then plateauing
   at ~3.8× by 96×96; the next comment explains why the plateau sits there.

## The poor man's benchmarks, made honest

To make the tasty suite itself non-misleading, `TestConvQuickCheck` now
carries size-scaled `SymbolicPerCall` / `SymbolicAmortized` /
`HandwrittenVectorized` poor man's benchmarks, and the matching deterministic
correctness checks live in the companion module `TestConvCorrect`. These tasty
"Bench" properties are noisy (100 runs each on a coarse ~10ms timer) and their
totals are anecdotal only — every per-call figure quoted here comes from
criterion — but the cost *shape* they expose is the point:

- `SymbolicPerCall` reproduces the original misleading measurement, calling
  full `vjp` every run and so rebuilding the derivative artifact each time.
- `SymbolicAmortized` builds the artifact once, shared across all runs, and
  only interprets it — the intended usage, and (as the criterion S-exec
  numbers confirm) genuinely built once.
- `HandwrittenVectorized` is the handwritten-vectorized baseline.

The gap `SymbolicPerCall − SymbolicAmortized` is the build tax quantified in
finding 2: it makes per-call symbolic look ~1.6× slower than handwritten at
6×6 and level by 24×24, while the amortized cost — the one that reflects real
usage — is the fastest at both sizes.

The next comment diagnoses where the finding-3 gap physically lives and why
both plateaus sit where they do; the comment after it designs the fix.
