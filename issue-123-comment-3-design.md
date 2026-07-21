# Comment 3 for #123 (draft): the fix — sort gather slice dims in contraction

*(Third of three consecutive comments planned for #123. This is the
general design, in principle ignorant of its implementation; the PR carries
a terse version of it plus implementation-level details and findings.
Benchmark numbers and source references to be refreshed just before
posting.)*

## Design

The diagnosis leaves exactly one free parameter that matters: the order of a
gather's `shn` (slice) dimensions. Semantically it is free — any permutation
of `shn` can be compensated by transposes around the gather — but on the
concrete backend it decides the loop nest of every slice copy, worth ~1.36×
on the operation that dominates both programs. So treat it as a normal form
and let the contraction pass establish it:

**For every gather whose `shn` is not sorted ascending, sort it: apply the
sorting permutation as a transpose *below* the gather and the inverse
permutation, on the `shn` part of the output, as a transpose *above* it.**

Sorting ascending puts the largest dimension innermost, so each slice
copy's inner loop is as long as possible and the per-loop-step interpretive
overhead is amortized (the mechanism established in the previous comment).
The transpose below is what changes the physical copies — `shn` is the tail
of the *source* shape, so reordering the source reorders the copy's loop
nest — while the transpose above merely restores the logical output order.
Both transposes are metadata-only on the concrete backend and merge with
neighboring transposes of producer and consumer, so the rewrite carries no
residual cost of its own.

## Why the contraction pass

- `contractAst` is the backend-recognition phase, documented as ad-hoc and
  benchmark-driven — a rule whose only justification is a measured property
  of the interpreter belongs there, not in the semantic simplifier.
- It runs just before interpretation, so no later rewrite can un-sort the
  gathers.
- The same phase-gating that keeps gather-through-transpose fusion out of
  the contraction phase (shown a 2–3× pessimization in the previous
  comment) protects the sorted form from being re-fused.

## Predicted effect

The isolated-chain prototype measures the ceiling: sorting `shn` takes the
artifact chain from 5.69ms to 4.27ms, matching the handwritten chain's
4.17ms. Since the profile places the entire symbolic-vs-handwritten gap in
the gathers, whole-program parity at every size is the expected outcome.
On a real convolutional net this is borne out: the `cnn-*` groups of
`convVjpBench` (a shaped two-layer CNN with maxpool, differentiated w.r.t.
its full parameters) show the exec-only gradient speeding up ~2% at 6×6 and
**~18% at 24×24**, the win growing with image size as the gathers come to
dominate.

The rule is shape-generic, not convolution-specific, but it rewrites only
gathers whose slice dims are not already sorted, so it is inert on programs
that produce no such gathers — among the nets here only convolution does,
leaving fully-connected and recurrent paths unaffected (neither sped up nor
slowed down). `dInp` (the `sscatter` path) needs no fix — it is
already 2–4× ahead. No new AST constructor or backend primitive is needed.

## Alternatives considered and rejected

1. **Rewrite the summation structure** (fuse `ssum`/`ssumN` into the
   `sdot1In` via a generalized contraction, commute
   `stranspose`/`sreplicate` through `sdot1In` operands, or recognize a
   matmul-like broadcasting contraction à la `AstMatmul2S` to avoid
   expanding the cotangent). This was the ticket's favored avenue and where
   this work started; the profile prices the whole family at ~1% of
   runtime, so it is dropped.
2. **Fuse the two gathers into one** — measured a 2–3× pessimization
   (per-output-position overhead dominates `mgenerate`; see the previous
   comment).
3. **Reorder `shm` (the output positions) instead** — a no-op in principle
   and in measurement: a compensating, metadata-only rewrite wrapped around
   an unchanged gather cannot change what is physically copied.
4. **Make the interpreted gather itself cheaper** — the right long-term
   lever (~65% of runtime for *both* programs) but upstream: filed as an
   ox-arrays ticket (drafted alongside these comments). Only a cheaper
   gather kernel can remove the residual linear `mgenerate` term; at the
   sizes measured, both gradients scale ~linearly in image area and their
   ratio has converged, so no contraction-pass rewrite can touch what
   remains.

## Validation plan

- Correctness: the QuickCheck conv properties (symbolic vs concrete vs
  handwritten gradients on random shapes, all three conv variants, plus
  jvp/vjp consistency) and the deterministic `TestConvCorrect` checks;
  then `minimalTest`, `CAFlessTest`, `parallelTest`.
- Performance: before/after criterion runs of `ConvVjpBench` at all sizes
  and of the MNIST benchmarks (`shortMnistForCI`), since `contractAst`
  runs on every symbolic program. Success criterion: S-exec on par with
  H-exec-var at every size, no MNIST regression.
- Expected churn: printed-AST regression tests will re-shuffle transpose
  permutations around gathers — mechanical.

## Risks and fallbacks

- **Rule fragility**: the gather/transpose chains differ across
  `Preserving`/`Shrinking`/`Padded` × `dInp`/`dKrn` — hence one small,
  shape-generic, compositional rule rather than a mega-pattern that matches
  only the benchmark.
- **A benchmark-coupled pass**: tuning contraction for conv can pessimize
  other paths — hence the mandatory MNIST before/after runs.
- If term-level normalization proves insufficient elsewhere, the ticket's
  other two avenues remain open: emitting fused contractions directly from
  delta evaluation (avenue 2), or convolution primitives with post-AD
  recovery (avenue 3, a separate ticket — the handwritten
  `conv2dPreserving_dInp`/`_dKrn` and the `flip42` identities in
  `TestConvQuickCheck` already spell out the conv-algebra such a
  primitive's VJP rules would encode). Neither is needed for the gap
  measured here.
