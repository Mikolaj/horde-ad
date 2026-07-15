# Issue description for ox-arrays (draft): the strided-normalize fallbacks

*(Draft of a new ox-arrays issue; the design goes into its single comment,
drafted in `oxarrays-issue-comment-design.md`. The numbers come from
horde-ad's `bench/ConvVjpBench.hs` and a late-cost-centre profile; they and
the links will be refreshed when filing. Code claims were verified against
the ox-arrays 0.2.0.1 quickfix checkout and orthotope 0.1.8.0. Companion
analysis: https://github.com/Mikolaj/horde-ad/issues/123.)*

Proposed title: **`toVectorListT`'s strided fallbacks dominate gather-heavy
programs (~two thirds of runtime)**

## The pattern

horde-ad executes its `gather` array operation through `mgenerate`: the
output shape is split as `shm ++ shn`; every position of the outer part
`shm` is enumerated, and for each one an index function computes a source
position and the slice of shape `shn` — in general a strided view, with the
source's transposes merged into it — is written into the contiguous output.
Convolution gradients build their im2col patch arrays this way, and in both
AD-generated and hand-vectorized gradient programs this single operation is
about two thirds of total runtime (~65% in the profile) — the hot cost
centres are boxed index arithmetic and per-position shape machinery
(`integerMul`, `withSomeSNat`, `shxEnum'`).

The slice write (`mvecsWritePartialLinear` in `Data.Array.Nested.Mixed`,
marked with a TODO in the source) already has the right structure: it
decomposes the strided slice into contiguous runs via orthotope's
`toVectorListT` and `VS.copy`s each run. The cost lives in the
decomposition's three regimes:

1. fully normal strides — the slice is one run: a single memcpy;
2. a normal stride suffix — a lazy Haskell loop conses up one vector slice
   per contiguous run: memcpy per run, but boxed per-run overhead;
3. **innermost dimension strided — a fully per-element fallback**
   (`vFromListN l (toListT sh a)`): every element goes through boxed
   Haskell index arithmetic.

The im2col gathers read transposed views, so they sit in regimes 2–3; and
`mtoVector`/`stoVector` (normalization, via orthotope's `toVectorT` =
`toVectorListT` + concat) has exactly the same three regimes. In a compiled
array language none of this would matter — the loops would fuse and
compile — but in an interpreted setting the granularity of these
implementations is a first-order cost.

## What measurements say about the cost structure

(criterion, GHC 9.12.4, `-O1`, single-threaded; the effects reproduce with
GHC 9.14.1 on a fresh dependency store)

1. **The cost is per output position, not per copied element.** Two
   programs that copy exactly the same elements: 144 positions ×
   ~1300-element slices run in 4.17–5.69ms, while the fused equivalent
   with 20736 positions × 9-element slices takes 12.0ms — 2–3× slower for
   identical output.
2. **Within a slice copy, the cost is per loop step, not per element.**
   The same 1296-element slices with dimensions ordered `[3,48,3,3]` vs
   `[3,3,3,48]`: 5.69ms vs 4.17ms (~1.36×). A long innermost run amortizes
   a per-step interpretive overhead; a short one pays the per-level setup
   16× more often — the per-run and per-element machinery of regimes 2–3
   above. (GHC 9.14.1: 4.94ms vs 3.75ms.)
3. **The headroom is large.** On the same operands, the stride-aware
   `Data.Array.Strided.Arith` kernels (dot, elementwise) are ~4% of the
   profile where the gathers are ~65% — an order of magnitude between the
   interpretive per-element path and a tight kernel over comparable data
   volumes.

## Why `scatter48` (~0.55ms) is so much cheaper than `gather48` (~4–6ms)

The clearest demonstration of that headroom is horde-ad's own *scatter*,
whose concrete implementation already routes essentially all data movement
through those kernels; `gather48` and `scatter48` are the isolating benchmark
groups in `bench/ConvVjpBench.hs`.

Both benchmarks traverse the same index incidences and the same
strided-read workload: the `scatter48` chains are the exact adjoints
(transposes) of the `gather48` im2col chains, verified at startup via the
adjoint law — for all index functions `f`, sources `x` and cotangents `y`,
`sdot0 (sgather x f) y == sdot0 x (sscatter y f)`. So both perform the same
number of element transfers along the same index map, structured as one
strided slice per output position (their *outputs* differ: gather
materializes the large patch array, scatter the small summed source-shaped
one). And scatter, if anything, does *more* work: where the index map is
many-to-one (the overlapping im2col windows) it also sums, where gather
only copies. The faster op is the one doing the extra arithmetic, so the
~8–10× gap cannot be a data-volume effect — it is purely about which code
path each transfer takes.

For concreteness, the pair in horde-ad surface syntax (`shm` = the
enumerated output dims, `shn` = the copied slice dims, `shp` = the source
index space; a gather's shapes are `shp ++ shn -> shm ++ shn` and its
adjoint scatter's the reverse):

```haskell
-- The first im2col step: 48 window positions × 3 kernel offsets, each
-- selecting a [3,3,50] slice of the [50,3,3,50] source.
windows :: ADReady target
        => target (TKS '[50, 3, 3, 50] Double)
        -> target (TKS '[48, 3, 3, 3, 50] Double)
windows u =
  sgather @'[48, 3] @'[3, 3, 50] @'[50] u
          (\case [i, k] -> [i + k]
                 _ -> error "windows")
  -- (windows u)[i, k, a, b, c] = u[i + k, a, b, c]

-- Its exact adjoint: overlapping windows sum back into source positions.
unWindows :: ADReady target
          => target (TKS '[48, 3, 3, 3, 50] Double)
          -> target (TKS '[50, 3, 3, 50] Double)
unWindows dy =
  sscatter @'[48, 3] @'[3, 3, 50] @'[50] dy
           (\case [i, k] -> [i + k]
                  _ -> error "unWindows")
  -- (unWindows dy)[p, a, b, c] = Σ dy[i, k, a, b, c] over all i + k == p
```

Concrete **gather** ([`tgatherZSScalar` → `tbuildS`][tgatherZSScalar]) is
[`Nested.sgenerate` over the outer positions with `Shaped shn` slices as
elements][tbuildS], and each slice is a *strided view* (`sindexPartial` of
a source whose transposes merged into the view) — so the ~250k elements the
two-gather chain copies go through `toVectorListT`'s regimes 2–3: the boxed
per-run and per-element machinery of the profile above, i.e. the
per-loop-step overhead behind point 2.

Concrete **scatter** ([`tscatterZSScalar`, general case][tscatterZSScalar])
keeps its element traffic out of the boxed path: per outer position (144 of
them) it only evaluates the index function and does an
`IntMap.insertWith (+)`, where `(+)` consumes the strided 1296-element
slice views directly through the stride-aware `NumElt` kernels
(`Data.Array.Strided.Arith`) and accumulates *dense* results, so the final
write-out is at most 50 `VS.copy` calls of dense vectors — plain memcpys —
into a mutable vector at linear offsets. The interpreted Haskell does ~144
cheap steps and all the element traffic runs in C. (One exception: a cell
hit exactly once stores its strided view unsummed and pays the Haskell
normalize at write-out — a negligible edge fraction of the overlap-heavy
im2col map.)

In short: with the current implementations, scatter's element traffic lands
in vectorized kernels while gather's lands in the boxed decomposition — an
asymmetry of the implementations, not of the adjoint pair. Notably,
gather's write path already has the per-slice structure; what it lacks is a
fast kernel for the copy itself.

The benchmark pair is [`gatherBenches`] / [`scatterBenches`], with the
adjoint check in [`checkAdjoint`].

## What the client can and cannot do

horde-ad now sorts each gather's slice dimensions ascending at the term
level (compensated by metadata-only transposes; the contraction-pass fix
from horde-ad#123), which buys the ~1.36× loop-order factor of point 2 and
brings its AD-generated gradients on par with hand-vectorized ones — worth
~18% on a real shaped CNN gradient at 24×24 image size, growing with size
as the gathers dominate. Past that, term rewriting is exhausted: the
per-call ratios of all program variants converge and everything scales
~linearly in data size, so the residual is a linear `mgenerate` term that
only a cheaper kernel can remove.

A client-side implementation fix was also considered and rejected, for two
reasons. First, the current gather already *is* slice-based — `mgenerate`
writes one `shn`-slice per output position — so reimplementing that loop in
horde-ad would reproduce the same `toVectorListT` work. Second, gather
cannot borrow the trick that makes scatter fast: scatter's strided reads
are folded into the C `(+)` kernel by the accumulation, and a sum-free
gather has nothing to fold them into — its strided reads must go through
normalize. The missing piece is a fast strided copy, upstream either way.

A concrete two-stage fix is designed in the comment below.

[tgatherZSScalar]: https://github.com/Mikolaj/horde-ad/blob/bc0f1e9d4a55d7caf46b47d3869b07304933e4ed/src/HordeAd/Core/OpsConcrete.hs#L1654-L1665
[tbuildS]: https://github.com/Mikolaj/horde-ad/blob/bc0f1e9d4a55d7caf46b47d3869b07304933e4ed/src/HordeAd/Core/OpsConcrete.hs#L1776-L1789
[tscatterZSScalar]: https://github.com/Mikolaj/horde-ad/blob/bc0f1e9d4a55d7caf46b47d3869b07304933e4ed/src/HordeAd/Core/OpsConcrete.hs#L1581-L1619
[`gatherBenches`]: https://github.com/Mikolaj/horde-ad/blob/bc0f1e9d4a55d7caf46b47d3869b07304933e4ed/bench/ConvVjpBench.hs#L248-L348
[`scatterBenches`]: https://github.com/Mikolaj/horde-ad/blob/bc0f1e9d4a55d7caf46b47d3869b07304933e4ed/bench/ConvVjpBench.hs#L350-L444
[`checkAdjoint`]: https://github.com/Mikolaj/horde-ad/blob/bc0f1e9d4a55d7caf46b47d3869b07304933e4ed/bench/ConvVjpBench.hs#L58-L66
