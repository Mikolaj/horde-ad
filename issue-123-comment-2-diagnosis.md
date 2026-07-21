# Comment 2 for #123 (draft): root cause — gather chains and slice loop order

*(Second of three consecutive comments planned for #123. Benchmark
numbers and source references to be refreshed just before posting.)*

## Where the time goes

Cost-centre profiles show both programs spend ~65% of their time in
`mgenerate` (ox-arrays), i.e., in the interpreted `sgather` chains that
materialize the im2col patch array — with boxed `Integer` index arithmetic
per element (`integerMul`, `withSomeSNat`, `shxEnum'` are the next cost
centres). The dot kernel and the sum passes are noise by comparison (~4% and
~1%), and they slightly *favor* the symbolic term. Normalized per call at
48×48 (profiled build): gathers S 12.2ms vs H 10.5ms; dot+sums S 0.69ms vs
H 0.87ms. The whole gap is in the gathers.

That profile also disposes of the mechanisms one would suspect first:

- *The summation structure* — the ticket's "three summing constructs", i.e.
  the symbolic term's rank-7 `sdot1In` contraction plus two further sum
  passes over an 8×-replicated cotangent, against the handwritten term's
  single product-and-`ssumN`. The effect is real (`tssumN` on the concrete
  backend is iterated `tssum`: one full pass and one allocation per summed
  dimension), but it acts on already-reduced small arrays and totals ~1% of
  runtime.
- *Materialized broadcasts* — refuted from source alone: ox-arrays'
  `X.replicate` is a stride-0 view and the dot and elementwise kernels are
  stride-aware, so the `sreplicateN dret` and `stranspose` wrappers feeding
  the contraction do not materialize anything.
- *Constant folding of the embedded cotangent* — H-exec-var keeps the
  cotangent symbolic, exactly like the artifact does, and is as fast as
  H-exec-contracted.

## The two gather chains differ only in orientation

Both gather chains are identical except for orientation: the AD-produced
artifact has `sgather @[48,3] (stranspose … (sgather @[48,3] …))`
(window position first) where the vectorized handwritten term has
`sgather @[3,48] (stranspose … (sgather @[3,48] …))` (kernel offset
first). The orientation of the *first* gather fixes the shape of the
materialized intermediate and, through the transpose between the
gathers, the slice shape of the *second* one. A micro-benchmark of the
isolated chains at 48×48 reproduces the entire gap:

| chain | time |
|-------|------|
| two gathers, artifact orientation `@[48,3]` | 5.69ms |
| two gathers, handwritten orientation `@[3,48]` | 4.17ms |
| single fused gather (either orientation) | 12.0ms |

## The mechanism: `shm` is a dead knob, `shn` is the live one

The concrete backend executes `sgather @shm src ix` (output shape
`shm ++ shn`, source shape `shp ++ shn`) via ox-arrays' `mgenerate`,
which enumerates every position of `shm`; for each one it evaluates the index
function to locate a point in `shp` and copies the whole remaining slice
of shape `shn` from the (possibly strided) source view into the
contiguous output. So a gather has two independent cost knobs: `shm`
fixes *how many* slice copies happen and `shn` fixes *the shape of each
copied slice*.

**Why flipping `shm` (with compensating transposes) cannot help.**
`@[48,3]` and `@[3,48]` both mean 144 copies of the same slices, so the
gather's own work is unchanged; the `fused-gather-ad-orient` vs
`fused-gather-vec-orient` benchmarks confirm this independently — they
differ only in `shm` order and time identically. The layout argument
("the flip changes the physical layout of the materialized output,
which the next gather then reads more coherently") defeats itself: the
compensating transpose required to preserve semantics composes into the
very view through which the next gather reads, re-scrambling the
strides by exactly the amount the flip fixed. A metadata-only rewrite
wrapped *around* an unchanged gather permutes strides but cannot change
what is copied. This was the first hypothesis tested; the refutation is
kept in the benchmark as `two-gathers-ad-shm-sorted` (5.59ms vs the
original 5.69ms).

**Why sorting `shn` does help.** `shn` is the tail of the *source*
shape, so a transpose *below* the gather reorders it — this changes the
gather itself (the loop nest of every slice copy), not merely the views
around it; the transpose above only restores the logical output order.
Each slice copy is a nested loop over the `shn` dimensions with a
per-loop-step interpretive overhead (the boxed-index cost centres seen
in the profiles). Both orientations copy the same 1296 elements per
slice, but with the 48-sized dimension innermost the overhead is
amortized over 48-iteration inner runs, while with a 3-sized dimension
innermost the per-level setup is paid 16× more often. Note the mechanism
is loop-overhead amortization, not cache locality — a cache story
predicts the same symptom but a different fix, and only the
discriminating pair (`two-gathers-ad-shm-sorted` vs
`two-gathers-ad-shn-sorted`) separates the two.

The follow-up micro-benchmarks that pin this down (isolated chains at
48×48):

| chain | time |
|-------|------|
| artifact orientation (`shn` = [3,48,3,3]) | 5.69ms |
| handwritten orientation (`shn` = [3,3,3,48]) | 4.17ms |
| artifact chain with `shm` flipped (compensated) | 5.59ms |
| artifact chain with `shn` sorted ascending (compensated) | **4.27ms** |

(These micro-benchmarks were run in isolation, separately from the per-call
tables of the previous comment; absolute times carry ~10–15%
session/thermal variance, so comparisons are meaningful within a table
rather than against the per-call numbers. The hand-built variant chains
were verified not to be normalized away by the smart constructors at
construction time — there is no transpose-into-gather rewrite — so each
row measures the term it names.)

## Gather fusion is a pessimization

Fusing the two gathers into one (e.g., enabling the gather-through-transpose
rules of `astGatherKnobsS` during the contraction phase) makes things 2–3×
**slower**: `mgenerate`'s cost is dominated by per-output-position overhead,
and the fused gather has 20736 positions with 9-element slices where the
chain has 144 positions with ~1300-element slices (12.0ms fused vs
4.17–5.69ms chained, either orientation). The current phase-gating that
avoids this fusion is empirically right.

## Why the plateaus sit where they do

**`dKrn` at ~1.37× (finding 3 of the previous comment).** The interpreted
im2col gathers are ~two thirds of both programs and grow to dominate, and
the isolated two-gather chains differ by ~1.36× on gather orientation alone
(5.69ms vs 4.17ms) — so once the gathers dominate, the whole-program ratio
converges to essentially theirs. The same conv-dominates-at-scale logic is
visible under the fix in a real net: the `cnn-*` benchmark groups (a shaped
two-layer CNN) speed up ~2% at 6×6 but ~18% at 24×24 — negligible on a small
net where dense layers and overhead dominate, sizeable once the im2col
gathers do.

**`dInp` at ~0.26×, i.e. symbolic ~3.8× faster (finding 4).** The
handwritten `dInp` is itself a gather-heavy convolution (the input gradient
in adjoint-conv form), so interpreting it re-runs an im2col gather + dot,
whereas the AD artifact is a direct `sscatter` — and an isolated scatter
chain is far cheaper than the isolated gather (scatter48 ~0.55ms vs gather48
~4–6ms at 48×48). The symbolic path thus skips the expensive im2col gather,
and the ratio settles near how much cheaper scatter is than that gather.

## Robustness

The mechanism reproduces across compiler versions: with GHC 9.14.1 (fresh
dependency store, same protocol) the isolated chains show the same
`shn`-ordering effect (4.94ms vs 3.75ms, `shn`-sorted 3.88ms), and gather
fusion remains a ~2× pessimization (~10ms).

A methodology note: most of the mechanisms suspected above are real
effects — source reading settles which effects exist, not their
coefficients — so each hypothesis got its own discriminating measurement
rather than another end-to-end timing: the cost-centre profile splits the
gathers from the dot and sums, and the `two-gathers-ad-shm-sorted` /
`two-gathers-ad-shn-sorted` pair splits intermediate layout from slice loop
shape (and with it the cache-locality story from the loop-overhead one).
