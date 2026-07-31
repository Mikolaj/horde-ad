# PR description for orthotope (draft): the regime-3 strided fallback

*(Draft of the pull request against [orthotope][repo] for the `bq-expand` fallback on branch `speedup-strided-tovector`. Unwrapped by destination convention — one line per paragraph — since it is pasted into a PR body. Measured results belong here rather than in the issue material; the benchmark that produced the strategy ranking stays on the branch, linked rather than merged, as its predecessor was. Links to be finalized when filing.)*

## What this changes

`toVectorListT` decomposes a strided array into contiguous runs. When the innermost dimension is strided there is no run longer than one element, and that case fell back to `vFromListN l (toListT sh a)` — a lazy cons-list with a thunk per element, streamed into a vector.

This replaces it. The outer-base grid is separable (`o0 + sum idx_d * stride_d`), so the base offset of each innermost run is precomputed once by iterated `concatMap`/`enumFromStepN` expansion — no division and no cons-list — and the result is then filled by a single `vGenerate` doing one `quotRem` per element, against the innermost extent rather than one per dimension:

```haskell
runBaseOffsetsT o0 osh oats = foldl' expand (VU.singleton o0) (zip osh oats)
  where expand !acc (!nd, !sd) = VU.concatMap (\a -> VU.enumFromStepN a sd nd) acc
```

The run base-offsets live in an unboxed `Int` vector — index scratch, independent of the abstract element storage `v` — so the only new dependency is a qualified `Data.Vector.Unboxed` import, already a library dependency. No `Vector` class method is added and no instance changes.

The bang patterns on the hot loop are performance-essential rather than stylistic: unbanged, the odometer and the output accrete thunks, and they were worth ~2× on their own in the benchmark this was ported from. They should survive review as they are.

## Why not the obvious version

A first attempt did the direct thing — `vGenerate` over a per-element `quotRem` *per dimension* — and was a mixed picture: faster on large, many-channel shapes, up to ~2× slower on the small, shallow, high-rank shapes that convolution actually produces, and 1.121× the original as a geomean. It is `gen-quotrem` in the benchmark below, kept so the result is not rediscovered. Splitting off the innermost dimension is what turns that into a uniform win: the per-dimension division becomes one division, and the outer multi-index is priced once per run instead of once per element.

## Measurements

**On the path itself.** A standalone replica of `toVectorListT`'s regime 3, comparing twenty-odd strategies over thirty-odd shapes — most derived from a shaped `conv2d`'s im2col patch tensors and per-position slices, kernels 3×3 to 11×11, channels 1–512, spatial 6–224, the rest non-convolutional stretch shapes reaching past those ranges. Criterion, GHC 9.12.4, `-O1`, with a hardened harness (`env`, `NOINLINE` on the benchmark-facing functions, agreement checked in a separate mode so it cannot share a computation via CSE). `bq-expand` beats the original list fallback on every shape with no regression, at a geomean of 0.173× its time. Full table and reading in the [micro-regime3 README][readme].

**In a real client.** horde-ad's convolution-gradient benchmark, `gather48`/`scatter48`, run as three interleaved A/B pairs — two builds differing only in which orthotope they link — reading the per-iteration OLS slope, every fit at R² ≥ 0.99:

| benchmark | released | this branch | |
|---|---:|---:|---:|
| `two-gathers-ad-orient` | 5.091ms | 1.286ms | 3.96× |
| `two-gathers-vec-orient` | 3.824ms | 0.687ms | 5.57× |
| `two-gathers-ad-shn-sorted` | 4.005ms | 0.771ms | 5.20× |
| `two-scatters-ad-orient` (control) | 0.508ms | 0.504ms | 1.01× |

Allocation falls with it, 4.7–7.1× on those chains. The control is a scatter, whose element traffic already runs through the stride-aware C kernels and so does not reach this fallback; it moves 0.7%, against the 2–5% two builds differing by a toggle are expected to shift a benchmark they cannot affect. The one scatter variant that does move is the one whose compensating transposes leave its slice views strided — the only one reaching regime 3 at all.

**On the real workload.** The same client's convolution-gradient sweep, the `S-exec` stage at image sizes 6 to 192, run the same way:

| size | released | this branch | | allocation |
|---|---:|---:|---:|---:|
| `6x6` | 0.179ms | 0.109ms | 1.6× | 2.1× |
| `24x24` | 1.494ms | 0.430ms | 3.5× | 4.4× |
| `48x48` | 5.531ms | 1.308ms | 4.2× | 5.4× |
| `96x96` | 21.437ms | 5.221ms | 4.1× | 6.1× |
| `192x192` | 88.387ms | 25.290ms | 3.5× | 6.5× |

The gain is smallest where the patch slices are smallest and the per-position overhead dominates, and settles between 3.5× and 4.2× once they are not.

## Validation

The test suite exercises this path heavily — `toVector`, `normalize`, `transpose`, `stretch`, `stride`, `rev` and `reduce` over strided arrays — and all 407 cases pass. Non-vacuity was checked by deliberately dropping the `r * tInner` term, which fails 63 cases, among them `transpose_2/4/5/6`, `stride_1` and `rev_1/2`; and the benchmark asserts every strategy produces byte-identical vectors on every shape, and that each shape really does take regime 3.

## What this does not do

It does not close the gap to the stride-aware C kernels, and no pure-Haskell rewrite of regime 3 can: with the innermost dimension strided there are no contiguous runs to hand a bulk kernel, so the transfer stays per-element in Haskell however the fallback is written. The benchmarked strategies bound that — the fastest of all is only ~1.5× beyond what is proposed here.

That fastest one is a direct mutable result buffer, and it was **deliberately not taken**. Filling a buffer across runs cannot be expressed through the per-element `vGenerate`; it needs a new `Vector` class method exposing a fill, and a prototype of exactly that (`vBuild :: Int -> (forall s. (Int -> a -> ST s ()) -> ST s ()) -> v a`) matches the hand-written mutable loop on every shape, so the method would be free at runtime. It was rejected on API grounds — orthotope's `Vector` interface stays pure and minimal, and ~1.5× did not justify a new method across all four instances. The measurements for it are in the README so the option is not re-proposed without new evidence. If you would rather have the speed than the smaller API, that ruling is yours to reverse and the code is already benchmarked.

[repo]: https://github.com/augustss/orthotope
[readme]: https://github.com/Mikolaj/orthotope/blob/22f100aaa40344e23fc7b7dfc74f3db7843e1a8f/micro-regime3/README.md
