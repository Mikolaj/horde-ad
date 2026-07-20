# PR description (draft): Sort gather slice dimensions in the contraction pass

*(Body for the PR from branch `123-sort-gather-slice-dims`; the proposed PR
title is the header above, matching the commit title. Benchmark numbers to
be refreshed together with the issue comments before publishing.)*

Closes #123. The analysis lives there in three comments — measurements,
diagnosis, design — and this description only states the rule and reports
what the implementation measured. The follow-up that neither this PR nor
any term rewrite can cover (the interpreted-gather kernel itself, ~65% of
runtime for symbolic and handwritten gradients alike) is tracked upstream
in <ox-arrays ticket link>.

## The rule

`contractAst` now sorts the `shn` (slice) dimensions of every gather
ascending: the sorting permutation is applied as a transpose below the
gather and its inverse, on the `shn` part of the output, as a transpose
above it. Both transposes are metadata-only on the concrete backend and
merge with neighboring transposes of producer and consumer. With the
largest dimension innermost, each slice copy's inner loop is as long as
possible, amortizing the interpreter's per-loop-step overhead — worth
~1.36× on the gather chains that dominate convolution gradients (see the
diagnosis comment). No new AST constructor or backend primitive is
involved, and the rule is confined to the contraction phase, whose
existing phase-gating also keeps the sorted gathers from being re-fused.

## Measured effect

Per call, exec-only, criterion (`bench/ConvVjpBench.hs`), GHC 9.12.4,
`-O1`, single-threaded:

| nAh=nAw | S-exec before | S-exec after | H-exec-var after |
|---------|--------------|--------------|------------------|
| 6       | 192µs        | 180µs        | 220µs            |
| 24      | 1.84ms       | 1.50ms       | 1.57ms           |
| 48      | 7.30ms       | 5.62ms       | 5.75ms           |
| 96      | 32.1ms       | 22.3ms       | 22.8ms           |
| 192     | 133ms        | 95.7ms       | 97.5ms           |

The symbolic kernel gradient is now at least on par with the
handwritten-vectorized one at every size measured: the pre-fix gap that
grew to ~1.37–1.39× (finding 3 of the measurements comment) is closed to
~1.0× across the whole range, including 96×96 and 192×192, so this is not
a small-size-only win (vs the handwritten gradient: ~18% faster at 6×6, a
few percent faster from 24×24 up). The input gradient (`dInp`, the
`sscatter` path) is unaffected — confirmed neutral in an A/B run; it was
already 2–4× ahead.

## Scope: conv-only, no non-conv impact

The effect is confined to programs with multi-dimensional-slice gathers —
among the MNIST nets, convolution only — and the printed-AST regression
tests pin this down: the churn falls in the synthetic conv/gather tests and
the CNN artifacts, while the FCNN and RNN artifacts are byte-identical
with and without the rule. Non-conv programs are therefore neither sped
up nor slowed down — the FC-MNIST `shortMnistForCI` deltas sit within
cross-binary noise (the concrete `VTA` control, which `contractAst`
cannot touch, drifts as much) — and gather-free programs are untouched
(the new case matches only `AstGatherS`). In the CNN artifacts it
does touch, `sgather` count is unchanged (no fusion) and the compensating
transposes either merge away (4 of 6 artifacts) or leave a single
metadata-only transpose (2 of 6), negligible beside the gather it reorients.
A real convolutional net is now timed directly, by the `cnn-*` groups of
`bench/ConvVjpBench.hs` (a shaped two-layer CNN, each layer with maxpool,
differentiated w.r.t. its full parameters), and it confirms a win that *grows
with image size* as the im2col gathers come to dominate: the exec-only
gradient is ~2% faster at 6×6, ~1.7% at 12×12, and **~18% faster at 24×24**
(the artifact-build time is unaffected). So on an actual CNN the rule is a
clear win at realistic sizes, not merely neutral — approaching the synthetic
`dKrn` win above as convolution dominates.

## Validation

- All conv QuickCheck vjp/jvp properties (symbolic vs concrete vs
  handwritten gradients on random shapes, all three conv variants) and the
  deterministic `TestConvCorrect` checks.
- CAFlessTest 670/670, minimalTest 74/74, full parallelTest.
- The printed-AST regression tests are refreshed; the diffs only re-shuffle
  transpose permutations around gathers (metadata-only; most artifacts gain
  none or one extra transpose, one maxpool artifact gains two), and only in
  the conv, gather and CNN tests.
- A real shaped CNN gradient is now benchmarked (the `cnn-*` groups of
  `convVjpBench`), not only the synthetic conv2dSame chains; an A/B confirms
  the exec win grows to ~18% at 24×24.
- Re-validated with GHC 9.14.1 (fresh dependency store, same protocol):
  parity reproduces (S-exec 5.45ms vs H-exec-var 5.37ms at 48×48 with the
  rule); the mechanism-level revalidation is in the diagnosis comment.

🤖 Generated with [Claude Code](https://claude.com/claude-code)
