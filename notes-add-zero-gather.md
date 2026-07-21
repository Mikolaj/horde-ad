# Notes analysis: a C-speed strided gather via the add-zero arith kernel

*(Analysis of chat notes from 2026-07-21, about
the planned ox-arrays feature request; the background section makes it
self-contained for a reader who knows horde-ad, ox-arrays and orthotope
but not the horde-ad #123 branch. Code claims were verified against
ox-arrays-0.2.0.1 as unpacked from the cabal store; horde-ad links are
pinned to master `bc0f1e9d4`.)*

## Background: what the #123 branch established

horde-ad executes its concrete `sgather` through `mgenerate`
([`tgatherZSScalar` → `tbuildS`][tgatherZSScalar], which is
[`Nested.sgenerate` over the outer positions][tbuildS]). The output
shape splits as `shm ++ shn`: every position of the outer part `shm` is
enumerated; for each one the index function computes a source position,
and an `shn`-shaped slice — in general a strided view, the source's
transposes having merged into it — is written into the contiguous
output. Convolution gradients build their im2col patch arrays
this way, and interpreted `sgather` is ~65% of their runtime. The slice
write decomposes the strided view into contiguous runs via orthotope's
`toVectorListT` and copies each run; the boxed Haskell per-run machinery,
with a fully per-element fallback when the innermost dimension is
strided, is the hot loop.

Scatter is the exact adjoint of gather: for all index functions `f`,
sources `x` and cotangents `y`,
`sdot0 (sgather x f) y == sdot0 x (sscatter y f)`. Yet on the same
index map and the same strided-read workload the concrete scatter is
~8–10× faster: ~0.52–0.55ms vs ~3.7–5.6ms in the `gather48`/`scatter48`
isolating benchmark groups of `bench/ConvVjpBench.hs` (criterion, GHC
9.12.4, `-O1`, single-threaded; the scatter chains are the gather
chains' adjoints, checked at startup via the law above). The gap is
code path, not data volume: [`tscatterZSScalar`][tscatterZSScalar]
does, per outer position, only an index evaluation and an
`IntMap.insertWith (+)` whose `(+)` consumes the strided slice views
directly through the stride-aware C kernels of
`Data.Array.Strided.Arith`, accumulating dense buffers that a handful
of `VS.copy` calls write out. The interpreted Haskell is per
*position*; all element traffic runs in C.

The branch's own fix (`contractAst` sorts each gather's `shn` slice
dimensions ascending, compensated by metadata-only transposes) buys the
~1.36× loop-order factor of the Haskell copy path and ~18% on a real
shaped CNN gradient at 24×24; past that, term rewriting is exhausted and
the residual is the kernel itself. The staged upstream drafts therefore
propose an ox-arrays issue naming `toVectorListT`'s strided fallbacks
as the cost, with a two-stage design: stage 1, a pure orthotope fix
(replace the per-element fallback with `vGenerate` over a
linear-index-to-offset computation); stage 2, a C strided-copy kernel
in ox-arrays' cbits, only if a measured gap remains.

Crucially for what follows, the drafted issue *rejects* a client-side
implementation fix, on two grounds: reimplementing `mgenerate`'s slice
loop in horde-ad would reproduce the same `toVectorListT` work, and
gather cannot borrow scatter's trick because a sum-free gather has
nothing to fold its strided reads into — "the missing piece is a fast
strided copy, upstream either way".

## The notes, reconstructed

The notes consist of two chat fragments.

**Fragment 1 — the asymmetry, compressed, and what the feature request
really asks for.** Scatter never needed a fast strided copy because
horde-ad's scatter knows it is scattering big sub-arrays and ox-arrays
happens to have a C routine for *adding* strided sub-arrays — so the
strided traversal of the source elements happens in C implicitly, as a
side effect of the accumulation. Gather needs the same traversal
*without* a subsequent arithmetic operation, which ox-arrays does not
offer; and since materializing a strided view of a partially-indexed
array is exactly `normalize`, the feature request distills to
**"normalize in C"**. This matches the branch's measured story point for
point. The one thing the compression elides is that per-position index
evaluation stays in interpreted Haskell on both sides — but the scatter
numbers already show that cost is affordable (144 positions of Haskell
around C slice traffic land at ~0.55ms).

**Fragment 2 — the add-zero workaround.** Implement gather in horde-ad
on the scatter model: per output position, evaluate the index function
and take the strided `shn`-slice view (`sindexPartial`); no `IntMap` is
needed, because a gather's output positions are disjoint and enumerable
in order (duplicated *reads* of source slices are fine); collect the
slices and `VS.concat` them. The one missing piece — densifying each
strided view — is done by an ox-arrays `NumElt` **add with a replicated
scalar zero**. The author's initial worry was that their own
`Arith.hs` wrappers might catch the zero-add as a noop and hand back the
still-strided view; on checking, the opposite holds — it is detected as
the *scalar (op) vector* special case, which is exactly the wanted
kernel. They estimate >90% that the redundant per-element add is free,
hidden by instruction-level parallelism under the memory-access latency.

## Verification against the sources

Every load-bearing claim checks out in ox-arrays-0.2.0.1
([`Arith/Internal.hs`][arith-internal], [`cbits/arith.c`][arith-c]):

1. **The dispatch is structural, so the zero is not elided.**
   `liftOpEltwise2` (`Internal.hs`, lines 79–114) classifies each operand
   with `stridesDense` and never inspects values; a fully replicated
   (all-strides-0) array reports a one-element dense block, i.e. is
   classified as a scalar. The case *scalar ⊕ arbitrarily-strided array*
   (line 94) dispatches to `wrapBinarySV`. So `sreplicate`d 0 + strided
   view takes the `sv` path no matter the view's strides, and no noop
   shortcut exists — confirming the author's self-correction.
2. **The `sv` kernel is normalize-in-C with a fused add.** `wrapBinarySV`
   (line 299) allocates a *dense* output of `product sh` elements and
   passes the input's shape, strides and offset to
   `oxarop_op_add_*_sv_strided` (`cbits/arith.c`, line 387), whose
   `TARRAY_WALK_NOINNER` loop walks arbitrary strides — including a
   strided innermost dimension — entirely in C and writes the output
   densely. With the scalar 0, the kernel computes precisely the strided
   normalize that orthotope's `toVectorListT` regimes do in boxed
   Haskell, plus one register add per element.
3. **The horde-ad precedent is already in the tree.** Scatter's
   `IM.insertWith (+) i2 (Nested.sindexPartial @shm @shn v ix)`
   ([`tscatterZSScalar`][tscatterZSScalar]) is the same
   view-into-C-arith move; the proposed gather sits next to it, replacing
   today's [`tbuildS`][tbuildS]/`mgenerate` path.

## The proposal is already priced by `scatter48`

The >90%-free-add estimate does not need to be trusted, because the
branch's scatter measurements already *include* the add: scatter performs
the identical per-position Haskell work (index evaluation), moves the
same element traffic through the same C kernels, and on top of that pays
the `IntMap` that a gather would not need. So `scatter48`'s ~0.52–0.55ms
against `gather48`'s ~3.7–5.6ms is a direct empirical bound: expect up to
~7–10× on the isolated gather chains, and — with interpreted gathers at
~65% of convolution-gradient runtime — roughly 2× on whole conv gradients
by Amdahl. This is the constructive counterpart of the branch's
observation that scatter in its natural orientation is the empirical
bound for a fast gather path.

## Consequences for the staged material (flagged, not yet applied)

1. **The issue draft's client-side rejection is refuted on both
   grounds.** Reimplementing the slice loop does *not* reproduce the
   `toVectorListT` work once the copy goes through the `sv` kernel, and
   the sum-free gather *can* borrow scatter's trick — by forcing a sum
   with a replicated zero. The drafted section should be rewritten: the
   upstream request remains "normalize in C" as the clean permanent fix
   (drops the redundant add, benefits every ox-arrays consumer), and the
   add-zero gather becomes the client-side interim that needs no upstream
   release.
2. **Stage 2 already exists in spirit.** The drafted stage-2 C
   strided-copy kernel is the `sv_strided` add minus the add; the design
   comment can present it as "expose the existing walk without the
   arithmetic" rather than as new kernel work.
3. **Stage 1 (orthotope `vGenerate` fallback fix) loses urgency for
   horde-ad** if gather leaves the `mgenerate` path entirely; it remains
   worthwhile upstream for other `toVectorT`/`mgenerate` users.
4. **Whether the branch's `shn`-sort remains a win over an `sv`-kernel
   gather is an open measurement, not a prediction.** The sort amortizes
   the Haskell copy path's per-loop-step overhead, which the C kernel
   mostly removes; the C walk still has per-dimension structure, but far
   cheaper steps. (Two source-derived predictions on this branch were
   already refuted by measurement — the sorted-scatter ~4.4×
   pessimization among them — so this one gets benchmarked, not argued.)

## Open questions

- **Bit-level semantics of `+ 0` on floats.** Under IEEE round-to-nearest
  `(-0.0) + 0.0 == +0.0`, so an add-zero copy flips negative zeros — a
  bit-level change no plain gather would make, though invisible to `(==)`
  and to every epsilon comparison. Multiplying by 1 instead preserves
  `-0.0` and quiet NaNs, and hits the same `sv` dispatch (`BO_MUL` has
  the same `_sv_strided` kernel shape). Worth deciding before
  implementing; integral types are unaffected either way.
- **One extra copy per slice.** `wrapBinarySV` allocates a fresh dense
  buffer per slice, which `VS.concat` then copies again into the output.
  Scatter pays an analogous write-out, so the `scatter48` bound already
  absorbs this; a later refinement could write slices straight into a
  preallocated output buffer, but that needs the copy-with-offset kernel
  — i.e. the real stage-2/normalize-in-C work.
- **Tiny slices.** Per-position overhead dominates when slices are small
  (the fused-gather measurements of the issue draft), for the add-zero
  gather exactly as for the current one — the drafts' argument that one
  code path degrades gracefully carries over unchanged.

[tgatherZSScalar]: https://github.com/Mikolaj/horde-ad/blob/bc0f1e9d4a55d7caf46b47d3869b07304933e4ed/src/HordeAd/Core/OpsConcrete.hs#L1654-L1665
[tbuildS]: https://github.com/Mikolaj/horde-ad/blob/bc0f1e9d4a55d7caf46b47d3869b07304933e4ed/src/HordeAd/Core/OpsConcrete.hs#L1776-L1789
[tscatterZSScalar]: https://github.com/Mikolaj/horde-ad/blob/bc0f1e9d4a55d7caf46b47d3869b07304933e4ed/src/HordeAd/Core/OpsConcrete.hs#L1581-L1619
[arith-internal]: https://hackage.haskell.org/package/ox-arrays-0.2.0.1/src/ops/Data/Array/Strided/Arith/Internal.hs
[arith-c]: https://hackage.haskell.org/package/ox-arrays-0.2.0.1/src/cbits/arith.c
