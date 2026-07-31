# Issue description for ox-arrays (draft): the strided-normalize fallbacks

*(Draft of a new ox-arrays issue; the design goes into its single comment, drafted in `oxarrays-issue-comment-design.md`. The numbers come from horde-ad's `bench/ConvVjpBench.hs` (criterion means of four interleaved full runs, 2026-07-22) and a late-cost-centre profile from the drafting sessions; the links will be finalized when filing. Code claims were verified against the ox-arrays 0.2.0.1 quickfix checkout and orthotope 0.1.8.0. Companion analysis: https://github.com/Mikolaj/horde-ad/issues/123.)*

Proposed title: **`toVectorListT`'s strided fallbacks carry the slice transfer of gather-heavy programs (whose gather is ~two thirds of runtime)**

**The ask, up front:** a strided-copy kernel in ox-arrays' cbits — the walk the `_sv_strided` arith kernels already do, without the arithmetic — so that materializing a strided view does not go through boxed Haskell. The design is in the comment below. Two things to say plainly before the evidence: a pure-Haskell fix to the orthotope side has since been written and will be offered as a PR, and it has already taken most of the gap this issue was first drafted around, from ~10× down to ~1.3–2.5×. So this is a request for the residue, on a path that is still per-element in Haskell no matter how the fallback is written — not the order-of-magnitude win the original numbers implied. The rest of this issue is the measurement, including the part that argues against the ask.

## The pattern

horde-ad executes its `gather` array operation through `mgenerate`: the output shape is split as `shm ++ shn`; every position of the outer part `shm` is enumerated, and for each one an index function computes a source position and the slice of shape `shn` — in general a strided view, with the source's transposes merged into it — is written into the contiguous output. Convolution gradients build their im2col patch arrays this way, and in both AD-generated and hand-vectorized gradient programs this single operation is about two thirds of total runtime (~65% in the profile) — the hot cost centres are boxed index arithmetic and per-position shape machinery (`integerMul`, `withSomeSNat`, `shxEnum'`).

The slice write (`mvecsWritePartialLinear` in `Data.Array.Nested.Mixed`, marked with a TODO in the source) already has the right structure: it decomposes the strided slice into contiguous runs via orthotope's `toVectorListT` and `VS.copy`s each run. The cost lives in the decomposition's three regimes:

1. fully normal strides *and* the slice spanning its whole backing vector — that vector is returned as is. A contiguous slice of a *larger* array, which is what a gather takes, misses this guard and falls into regime 2's loop, whose first step emits one `vSlice`: a single memcpy either way;
2. a normal stride suffix — a lazy Haskell loop conses up one vector slice per contiguous run: memcpy per run, but boxed per-run overhead;
3. **innermost dimension strided — a fully per-element fallback** (`vFromListN l (toListT sh a)` in orthotope 0.1.8.0; the fix offered below replaces it with a `vGenerate` over precomputed run base-offsets — cheaper, still per-element): every element goes through boxed Haskell index arithmetic.

Not every im2col gather reads a transposed view: in the two-gather chain below only the second does, landing in regime 3, while the chain's first gather and the fused single gather read dense sources and so copy canonical slices — yet the fused variant, on that cheapest path throughout, is the slowest gather variant measured here, which is point 1 below. `mtoVector`/`stoVector` (normalization, via orthotope's `toVectorT` = `toVectorListT` + concat) has exactly the same three regimes. In a compiled array language none of this would matter — the loops would fuse and compile — but in an interpreted setting the granularity of these implementations is a first-order cost.

## What measurements say about the cost structure

(criterion except where a profile is named, GHC 9.12.4, `-O1`, single-threaded, against orthotope 0.1.8.0 — i.e. the regime-3 fallback as released, not as the fix below leaves it; old runs with GHC 9.14.1 did not produce radically different results and were abandoned)

1. **The cost is per output position, not per copied element.** The two-gather chain — 144 positions × 1296-element slices over a 144 × 450 intermediate, ~250k elements copied — runs in 4.92–6.67ms, while the same im2col computation as one fused gather, 20736 positions × 9-element slices, copies a quarter fewer elements and takes 13.6ms: 144× the positions, less traffic, 2–3× slower.
2. **Within a slice copy, the cost is per loop step, not per element.** The same 1296-element slices with dimensions ordered `[3,48,3,3]` vs `[3,3,3,48]`: 6.67ms vs 4.92ms (~1.36×). Both land in regime 3 — their innermost strides are 450 and 1350, so neither has a contiguous run at all — and the difference is the interior of the per-element walk: `toListT` recurses a level per dimension, so the two pay 579 and 39 interior index steps on top of the 1296 leaf visits they share.
3. **The headroom is large.** On the same operands, the stride-aware `Data.Array.Strided.Arith` kernels (dot, elementwise) take ~4% of the profile where the gathers take ~65%, over comparable data volumes — two shares of one profile rather than a measured per-element ratio, so read it as where the time sits, not as how much a kernel would win.

## Why `scatter48` (~0.5ms) was so much cheaper than `gather48` (~5ms), and how much of that the orthotope fix has since taken

The clearest demonstration of that headroom is horde-ad's own *scatter*, whose concrete implementation already routes essentially all data movement through those kernels; `gather48` and `scatter48` are the isolating benchmark groups in `bench/ConvVjpBench.hs`.

Both benchmarks traverse the same index incidences: the `scatter48` chains are the exact adjoints (transposes) of the `gather48` im2col chains, verified at startup via the adjoint law — for all index functions `f`, sources `x` and cotangents `y`, `sdot0 (sgather x f) y == sdot0 x (sscatter y f)`. So both perform the same number of element transfers, 251424, along the same index map, one `shn`-slice per enumerated outer position — that outer space is `shm` on both sides, though it indexes gather's *output* and scatter's *input*, and their outputs differ likewise: gather materializes the large patch array, scatter the small summed source-shaped one. The transposed read sits at opposite ends of the two chains, so the *strided* halves of that traffic are not equal: gather reads its 1296-element slices strided and its 450-element ones dense, its adjoint scatter the mirror image, which puts ~2.9× more of gather's traffic through the strided path. And scatter, if anything, does *more* work: where the index map is many-to-one (the overlapping im2col windows) it also sums, where gather only copies. The faster op is the one doing the extra arithmetic on equal total traffic, and a 2.9× asymmetry cannot account for a ~9–12× gap, so the gap is not a data-volume effect — it is about which code path each transfer takes.

For concreteness, the pair in horde-ad surface syntax (`shm` = the enumerated output dims, `shn` = the copied slice dims, `shp` = the source index space; a gather's shapes are `shp ++ shn -> shm ++ shn` and its adjoint scatter's the reverse):

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

Concrete **gather** ([`tgatherZSScalar` → `tbuildS`][tgatherZSScalar]) is [`Nested.sgenerate` over the outer positions with `Shaped shn` slices as elements][tbuildS], and each slice is a *strided view* (`sindexPartial` of a source whose transposes merged into the view) — so the ~250k elements the two-gather chain copies go through `toVectorListT`'s regimes 2–3: the boxed per-run and per-element machinery of the profile above, i.e. the per-loop-step overhead behind point 2.

Concrete **scatter** ([`tscatterZSScalar`, general case][tscatterZSScalar]) keeps its element traffic out of the boxed path: per outer position (144 per scatter) it only evaluates the index function and does an `IntMap.insertWith (+)`, where `(+)` consumes the slice views directly through the stride-aware `NumElt` kernels (`Data.Array.Strided.Arith`) — strided wherever the chain feeds a transposed view in, which here is the 450-element slices, dense for the 1296-element ones read straight off the cotangent — and accumulates *dense* results, so each scatter's write-out is at most 50 `VS.copy` calls of dense vectors — plain memcpys — into a mutable vector at linear offsets. The interpreted Haskell does ~144 cheap steps per scatter, 288 over the timed two-scatter chain, and all the element traffic runs in C. (One exception: a cell hit exactly once stores its strided view unsummed and pays the Haskell normalize at write-out — a negligible edge fraction of the overlap-heavy im2col map.)

In short: with the current implementations, scatter's element traffic lands in vectorized kernels while gather's lands in the boxed decomposition — an asymmetry of the implementations, not of the adjoint pair. Notably, gather's write path already has the per-slice structure; what it lacks is a fast kernel for the copy itself.

**How much of this gap survives the orthotope fix.** Three interleaved A/B pairs over these two groups, the builds differing only in which orthotope they link (criterion, GHC 9.12.4, `-O1`, per-iteration OLS slope, every fit R² ≥ 0.99; the released side lands inside the figures above rather than reproducing them benchmark for benchmark — 5.09ms against the 4.9–6.7ms band, 0.508ms against ~0.55ms). The two-gather chain drops from 5.09ms to 1.29ms in its natural orientation and 3.82ms to 0.69ms in its vectorized one, scatter is unmoved at 0.504ms against 0.508ms, and dividing each gather by the scatter of the *same* orientation the ratio falls from 10.0× to 2.55× natural, and from 7.3× to 1.32× vectorized. The control moves 0.7%, against the 2–5% a two-build A/B shifts benchmarks it cannot affect. So the order-of-magnitude asymmetry this section documents is mostly a property of the *released* fallback: the pure-Haskell fix takes it to between ~1.3× and ~2.5×, and what a C strided copy could still win is that much and not more. The remaining case for the kernel is that this is where the residue lives, not that it is worth an order of magnitude.

One qualifier: scatter is this fast in its *natural* orientation only. Re-orienting its slices the way that pays on gather (sorting the `shn` dims via compensating transposes) measures ~4.7× *slower* (`two-scatters-ad-shn-sorted`, 2.59ms vs 0.55ms as first recorded; the A/B above puts it at 5.0× against released orthotope and 4.1× with the fix, which does reach this variant — its compensating transposes are what leave the views strided): each slice is added as one flat vector, so a sorted `shn` has no per-`shn`-dim loop to amortize, while the compensating transposes strid-ify the very views the accumulating `(+)` consumes. So the ~0.55ms is the bound for slice traffic through the C kernels on naturally-oriented views, not a number any orientation reaches.

The benchmark pair is [`gatherBenches`] / [`scatterBenches`], with the adjoint check in [`checkAdjoint`].

## What the client can and cannot do

horde-ad now sorts each gather's slice dimensions ascending at the term level (compensated by metadata-only transposes; the contraction-pass fix from horde-ad's [#123]), which buys the ~1.36× loop-order factor of point 2 and brings its AD-generated gradients on par with hand-vectorized ones — worth ~17% on a real shaped CNN gradient at 24×24 image size, growing with size as the gathers dominate. Past that, term rewriting is exhausted: the per-call ratios of all program variants converge and everything scales ~linearly in data size, so the residual is a linear `mgenerate` term that only a cheaper kernel can remove.

A client-side reimplementation of the slice loop alone was considered and rejected: the current gather already *is* slice-based — `mgenerate` writes one `shn`-slice per output position — so redoing that loop in horde-ad would reproduce the same `toVectorListT` work. There was, until the orthotope fix, a client-side *interim* that would have captured most of the headroom with no upstream change, by making gather borrow the trick that makes scatter fast: rebuild gather on the scatter model (per output position, take the strided `shn`-slice view; no accumulation map is needed, a gather's output positions being disjoint) and densify each view through the existing arith kernels by adding a replicated scalar zero. The scalar⊕strided-array dispatch (`wrapBinarySV` and the `_sv_strided` C kernels) walks arbitrary strides in C and writes densely — it already is normalize-in-C with one redundant add fused in. The scatter numbers priced that detour at ~9–12× when they were taken against the released fallback; at the ~1.3–2.5× measured above it no longer earns its own implementation, so it is recorded here as what the upstream fix displaced rather than as work anyone should do. The clean permanent home for the missing piece — a fast strided copy — is upstream, which is what this issue asks for: the add-zero detour shows the kernel effectively exists, and exposing it without the arithmetic (or fixing the fallbacks it routes around) benefits every consumer.

The pure-Haskell rewrite of that fallback has been implemented and benchmarked on orthotope branch `speedup-strided-tovector`, and will be offered as a PR: it compares twenty-odd strategies over thirty-odd shapes, and beats the original list fallback on every one of them with no regression, at a geomean of 0.173× its time ([micro-regime3 README][readme]; a first attempt, one `quotRem` per dimension per element, went the other way — 1.121× on the same replica, and ~1.5–2.1× slower on the gather chains measured here — and was dropped). Of the strategies benchmarked there the fastest of all is only ~1.5× beyond what shipped, and it needs orthotope's `Vector` class to grow a mutable fill. So the pure-Haskell space is explored, and every strategy in it leaves the transfer per-element in Haskell, regime 3 having no contiguous runs to slice. That is what this issue asks to move into C; the design is in the comment below.

[#123]: https://github.com/Mikolaj/horde-ad/issues/123
[readme]: https://github.com/Mikolaj/orthotope/blob/22f100aaa40344e23fc7b7dfc74f3db7843e1a8f/micro-regime3/README.md
[tgatherZSScalar]: https://github.com/Mikolaj/horde-ad/blob/e1bd5f5e22e38960958dbe2c7ba40ffca1a1b081/src/HordeAd/Core/OpsConcrete.hs#L1654-L1665
[tbuildS]: https://github.com/Mikolaj/horde-ad/blob/e1bd5f5e22e38960958dbe2c7ba40ffca1a1b081/src/HordeAd/Core/OpsConcrete.hs#L1776-L1789
[tscatterZSScalar]: https://github.com/Mikolaj/horde-ad/blob/e1bd5f5e22e38960958dbe2c7ba40ffca1a1b081/src/HordeAd/Core/OpsConcrete.hs#L1581-L1619
[`gatherBenches`]: https://github.com/Mikolaj/horde-ad/blob/e1bd5f5e22e38960958dbe2c7ba40ffca1a1b081/bench/ConvVjpBench.hs#L392-L547
[`scatterBenches`]: https://github.com/Mikolaj/horde-ad/blob/e1bd5f5e22e38960958dbe2c7ba40ffca1a1b081/bench/ConvVjpBench.hs#L578-L741
[`checkAdjoint`]: https://github.com/Mikolaj/horde-ad/blob/e1bd5f5e22e38960958dbe2c7ba40ffca1a1b081/bench/ConvVjpBench.hs#L549-L576
