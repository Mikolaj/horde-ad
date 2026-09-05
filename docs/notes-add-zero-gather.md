# The add-zero gather: refuted by the measurement that was meant to price it

**Ruling, 2026-07-31: do not build this.** The design was priced entirely off
the ~9--12x gap between the concrete gather and its adjoint scatter.
An interleaved A/B against orthotope's strided-fallback fix puts that gap
at 2.55x at matched natural orientation and 1.32x at matched vectorized
orientation, so the upstream fix has taken the headroom this design existed
to capture, and it no longer earns its own implementation. Reviving it needs
a fresh argument and fresh numbers, not this document.

What follows is kept because the analysis is sound and the mechanism is worth
knowing --- the `sv` dispatch really is normalize-in-C with a fused add,
and that fact still underwrites the upstream ask. Read it as the record
of a design and of what killed it.

*(Analysis of chat notes from 2026-07-21, about the planned ox-arrays feature
request; the background section makes it self-contained for a reader who knows
horde-ad, ox-arrays and orthotope but not the horde-ad [#123] branch. Code
claims were verified against ox-arrays-0.2.0.1 as unpacked from the cabal store;
horde-ad links are pinned to master `e1bd5f5e2`, which predates the `shn`-sort
rule this document also describes --- that landed on master a day later,
in `fa508caa4`, and the pinned links all point at `OpsConcrete.hs`, none of them
at the rule. The ox-arrays citations were re-checked on 2026-07-29 against
the `../ox-arrays` checkout, which agrees with that store tarball byte for byte;
the `liftOpEltwise2` range was three lines short and is corrected. The orthotope
claims were re-checked on 2026-07-31 against `speedup-strided-tovector`
at `5e4ece1`, where the fallback fix had shipped, superseding what consequence 3
first said.)*

## Background: what the [#123] branch established

horde-ad executes its concrete `sgather` through `mgenerate` ([`tgatherZSScalar`
-> `tbuildS`][tgatherZSScalar], which is [`Nested.sgenerate` over the outer
positions][tbuildS]). The output shape splits as `shm ++ shn`: every position
of the outer part `shm` is enumerated; for each one the index function computes
a source position, and an `shn`-shaped slice --- in general a strided view,
the source's transposes having merged into it --- is written into the contiguous
output. Convolution gradients build their im2col patch arrays this way,
and interpreted `sgather` is ~65% of their runtime. The slice write decomposes
the strided view into contiguous runs via orthotope's `toVectorListT` and copies
each run; the boxed Haskell per-run machinery, with a fully per-element fallback
when the innermost dimension is strided --- as orthotope 0.1.8.0 released it,
consequence 3 below being the rewrite that has since replaced that fallback ---
is the hot loop.

Scatter is the exact adjoint of gather: for all index functions `f`, sources `x`
and cotangents `y`, `sdot0 (sgather x f) y == sdot0 x (sscatter y f)`. Yet
on the same index map, moving the same number of elements, the concrete scatter
is ~9--12x faster: ~0.55ms vs ~4.9--6.7ms in the `gather48`/`scatter48`
isolating benchmark groups of `bench/ConvVjpBench.hs` (criterion, GHC 9.12.4,
`-O1`, single-threaded, against orthotope 0.1.8.0 --- i.e. before the fallback
fix of consequence 3 below; the scatter chains are the gather chains' adjoints,
checked at startup via the law above). The gap is code path, not data volume:
[`tscatterZSScalar`][tscatterZSScalar] does, per outer position, only an index
evaluation and an `IntMap.insertWith (+)` whose `(+)` consumes the strided slice
views directly through the stride-aware C kernels of `Data.Array.Strided.Arith`,
accumulating dense buffers that a handful of `VS.copy` calls write out.
The interpreted Haskell is per *position*; essentially all element traffic runs
in C --- a target hit exactly once keeps its strided view unsummed and pays
the Haskell normalize at write-out.

The `shn`-sort fix (`contractAst` sorts each gather's `shn` slice dimensions
ascending, compensated by metadata-only transposes) buys the ~1.36x loop-order
factor of the Haskell copy path (the `gather48` chains) and ~17% on a real
shaped CNN gradient at 24x24 (the `cnn-24x24` group); past that, term rewriting
is exhausted and the residual is the kernel itself. The staged upstream drafts
therefore propose an ox-arrays issue naming `toVectorListT`'s strided fallbacks
as the cost, with a two-stage design: stage 1, a pure orthotope fix
to the per-element fallback; stage 2, a C strided-copy kernel in ox-arrays'
cbits. Stage 1 has since shipped on a branch (consequence 3 below), and what
it leaves behind is what stage 2 is asked for.

Crucially for what follows, the issue draft as it then stood *rejected*
a client-side implementation fix, on two grounds: reimplementing `mgenerate`'s
slice loop in horde-ad would reproduce the same `toVectorListT` work, and gather
cannot borrow scatter's trick because a sum-free gather has nothing to fold
its strided reads into, the missing piece being a fast strided copy upstream
either way. Consequence 1 below is what became of that rejection, so the draft
no longer reads this way.

## The notes, reconstructed

The notes consist of two chat fragments.

**Fragment 1 --- the asymmetry, compressed, and what the feature request really
asks for.** Scatter never needed a fast strided copy because horde-ad's scatter
knows it is scattering big sub-arrays and ox-arrays happens to have a C routine
for *adding* strided sub-arrays --- so the strided traversal of the source
elements happens in C implicitly, as a side effect of the accumulation. Gather
needs the same traversal *without* a subsequent arithmetic operation, which
ox-arrays does not offer; and since materializing a strided view
of a partially-indexed array is exactly `normalize`, the feature request
distills to **"normalize in C"**. This matches the branch's measured story point
for point. The one thing the compression elides is that per-position index
evaluation stays in interpreted Haskell on both sides --- but the scatter
numbers already show that cost is affordable (a two-scatter chain of Haskell
around C slice traffic lands at ~0.55ms).

**Fragment 2 --- the add-zero workaround.** Implement gather in horde-ad
on the scatter model: per output position, evaluate the index function and take
the strided `shn`-slice view (`sindexPartial`); no `IntMap` is needed, because
a gather's output positions are disjoint and enumerable in order (duplicated
*reads* of source slices are fine); collect the slices and `VS.concat` them.
The one missing piece --- densifying each strided view --- is done
by an ox-arrays `NumElt` **add with a replicated scalar zero**. The author's
initial worry was that their own `Arith/Internal.hs` wrappers might catch
the zero-add as a noop and hand back the still-strided view; on checking,
the opposite holds --- it is detected as the *scalar (op) vector* special case,
which is exactly the wanted kernel. They estimate >90% that the redundant
per-element add is free, hidden by instruction-level parallelism
under the memory-access latency.

## Verification against the sources

Every load-bearing claim checks out in ox-arrays-0.2.0.1
([`Arith/Internal.hs`][arith-internal], [`cbits/arith.c`][arith-c]):

1. **The dispatch is structural, so the zero is not elided.** `liftOpEltwise2`
   (`Arith/Internal.hs`, lines 79--117) classifies each operand
   with `stridesDense` and never inspects values; a fully replicated
   (all-strides-0) array reports a one-element dense block, i.e. is classified
   as a scalar. The case *scalar + arbitrarily-strided array* (line 94)
   dispatches to `wrapBinarySV`. So `sreplicate`d 0 + strided view takes
   the `sv` path, and no noop shortcut exists --- confirming the author's
   self-correction.
2. **On that dispatch branch the `sv` kernel is normalize-in-C with a fused
   add.** `wrapBinarySV` (line 299) allocates a *dense* output of `product sh`
   elements and passes the input's shape, strides and offset
   to `oxarop_op_add_*_sv_strided` (`cbits/arith.c`, line 387), whose
   `TARRAY_WALK_NOINNER` loop walks arbitrary strides --- including a strided
   innermost dimension --- entirely in C and writes the output densely.
   With the scalar 0, the kernel computes precisely the strided normalize
   that orthotope's `toVectorListT` regimes do in boxed Haskell, plus one
   register add per element. Two kinds of view escape that, and a gather built
   on this design has to exclude them. When `stridesDense` reports the operand
   dense --- as it does for any covering *permutation*, e.g. shape `[50,3]`
   with strides `[1,50]` --- line 89's *scalar + dense* branch fires instead,
   runs the kernel over the flat block and re-wraps the result
   with the operand's own strides, so nothing is reordered. And `wrapBinarySV`
   runs under `simplifyArray` (line 202), which strips stride-0 dimensions
   with `unreplicateStrides` and re-inserts them into the result, so a view
   carrying a replicated dimension comes back replicated, over a buffer shorter
   than `product sh` of the original shape. Neither arises in the chains
   measured here --- each `shn` slice of `gather48` is either canonical already
   or has its smallest stride above 1, so it either needs no reordering or takes
   line 94 --- but the `VS.concat` of fragment 2 is only correct where
   that holds.
3. **The horde-ad precedent is already in the tree.** Scatter's
   `IM.insertWith (+) i2 (Nested.sindexPartial @shm @shn v ix)`
   ([`tscatterZSScalar`][tscatterZSScalar]) is the same view-into-C-arith move;
   the proposed gather sits next to it, replacing today's
   [`tbuildS`][tbuildS]/`mgenerate` path.

## The proposal was priced by `scatter48`, and the re-measurement unpriced it

The >90%-free-add estimate does not need to be trusted, because the branch's
scatter measurements already *include* the add: scatter performs the identical
per-position Haskell work (index evaluation), moves the same element traffic
through the same C kernels, and on top of that pays the `IntMap` this gather
would not need. So `scatter48`'s ~0.55ms against `gather48`'s ~4.9--6.7ms
is a direct empirical bound on its element work --- the larger output it must
allocate is the one cost scatter does not pay, and is the extra copy per slice
below: expect up to ~9--12x on the isolated gather chains, and ---
with interpreted gathers at ~65% of convolution-gradient runtime --- roughly 2x
on whole conv gradients by Amdahl. This is the constructive counterpart
of the branch's observation that scatter in its natural orientation
is the empirical bound for a fast gather path.

Both sides of that ratio were measured against orthotope 0.1.8.0,
and the fallback fix of consequence 3 rewrites the path gather's side runs
through. **That re-measurement has now been done, and it removes most
of this section's headroom.** Three interleaved A/B pairs
over `gather48`/`scatter48` (criterion, GHC 9.12.4, `-O1`, per-iteration OLS
slope, every fit R2 >= 0.99; the two builds differ only in which orthotope they
link. The released side lands inside the figures above rather than reproducing
them benchmark for benchmark --- 5.09ms against the quoted 4.9--6.7ms band,
0.508ms against ~0.55ms --- except the sorted scatter, which comes back
at 2.53ms against the 2.59ms recorded):

| | released 0.1.8.0 | with the fix | gather / scatter |
|---|---:|---:|---:|
| `two-gathers-ad-orient` | 5.091ms | 1.286ms | 10.0x -> 2.55x |
| `two-scatters-ad-orient` (control) | 0.508ms | 0.504ms | --- |
| `two-gathers-vec-orient` | 3.824ms | 0.687ms | 7.3x -> 1.32x |
| `two-scatters-vec-orient` (control) | 0.526ms | 0.521ms | --- |

Each ratio divides a gather by the scatter of the *same* orientation; scatter's
own fastest is `ad-orient` throughout. The controls move 0.7%, against the 2--5%
a two-build A/B is expected to shift benchmarks it cannot affect, so the gather
column is the fix and not the rebuild. The one scatter variant that does move,
`two-scatters-ad-shn-sorted` (2.53 -> 2.04ms), is the one whose compensating
transposes leave its slice views strided, i.e. the only one reaching
this fallback at all --- which is the corroboration, not an anomaly.

So the ~9--12x that priced the add-zero gather is now ~2.55x at matched natural
orientation and ~1.32x at matched vectorized orientation, and the upstream fix
took that headroom without any of this design's work. What remains does
not justify building it on these numbers; anyone reviving it needs a fresh
argument, not this section.

## Consequences for the staged material (now applied)

1. **The issue draft's client-side rejection is refuted on both grounds**,
   and the drafts have been rewritten accordingly: the upstream request
   is "normalize in C" as the clean permanent fix (drops the redundant add,
   benefits every ox-arrays consumer), and the add-zero gather
   is the client-side interim that needs no upstream release. Reimplementing
   the slice loop does *not* reproduce the `toVectorListT` work once the copy
   goes through the `sv` kernel, and the sum-free gather *can* borrow scatter's
   trick --- by forcing a sum with a replicated zero.
2. **The C strided-copy kernel already exists in spirit.** It
   is the `sv_strided` add minus the add --- which is how the design comment
   prices it, "a strided copy is that walk minus the arithmetic", while still
   asking for a new kernel: a type-agnostic one in the existing cbits, needing
   only an element byte-width and no per-type TH families, with `wrapUnary`
   showing how to bind most of it.
3. **The pure-orthotope fallback fix is settled, and will be offered
   as an orthotope PR --- but it is not the C path this document argues for.**
   It was implemented and benchmarked on orthotope branch
   `speedup-strided-tovector` ([micro-regime3 README][readme]). The first
   attempt, one `quotRem` per dimension per element, cost 1.121x on the replica
   and ~1.5--2.1x on these gather chains, and was dropped; what shipped
   precomputes each innermost run's base offset and does one `quotRem` per
   element, beating the original list fallback on every benchmarked shape
   with no regression (geomean 0.173x its time). So it does help the other
   `toVectorT`/`mgenerate` users the tweak had been floated for. End to end
   it is worth 3.96--5.57x on these two-gather chains and 4.7--7.1x
   in allocation, measured as above. Refuted, and not to be chased again:
   the *fused* variants looked ~18--20% slower on the fixed build
   at byte-identical allocation; that is a position effect of RTS pool state
   a predecessor benchmark leaves in the process, not a property of the change
   ([the full account][pos-effect]). What it does not settle: every one
   of the strategies benchmarked there --- the fastest only ~1.5x beyond what
   shipped, and needing a new `Vector` class method, so deliberately not taken
   (a ruling the README has since softened from bar to weight, on the unused
   in-tree precedent `Data/Array/Internal/FastReshape.hs`) --- leaves
   the transfer per-element in Haskell, regime 3 having no contiguous runs
   to slice. Moving it into C (add-zero interim, normalize-in-C upstream)
   is still what this document is about.
4. **Whether the branch's `shn`-sort remains a win over an `sv`-kernel gather
   is still an open measurement, not a prediction** --- the `sv`-kernel gather
   is not built yet. The sort amortizes the Haskell copy path's per-loop-step
   overhead, which the C kernel mostly removes; the C walk still has
   per-dimension structure, but far cheaper steps. (Source-derived predictions
   on this branch have been refuted by measurement before --- the sorted-scatter
   ~4.7x pessimization, and the first fallback attempt's own mixed picture ---
   so this one gets benchmarked, not argued.)

## Open questions

- **Bit-level semantics of `+ 0` on floats.** Under IEEE round-to-nearest
  `(-0.0) + 0.0 == +0.0`, so an add-zero copy flips negative zeros ---
  a bit-level change no plain gather would make, though invisible to `(==)`
  and to every epsilon comparison. Multiplying by 1 instead preserves `-0.0`,
  and hits the same `sv` dispatch (`BO_MUL` has the same `_sv_strided` kernel
  shape). Negative zero is the only discriminating case: the two kernels expand
  one C macro over the element type, so `x + 0.0` and `x * 1.0` alike propagate
  a quiet NaN and quiet a signalling one. Worth deciding before implementing;
  integral types are unaffected either way.
- **One extra copy per slice.** `wrapBinarySV` allocates a fresh dense buffer
  per slice, which `VS.concat` then copies again into the output. Scatter pays
  an analogous write-out, but its copy is proportional to its small
  source-shaped output where this one is proportional to the whole patch array
  --- larger by the same overlap factor --- so the `scatter48` bound absorbs
  only part of it. A later refinement could write slices straight
  into a preallocated output buffer, but that needs the copy-with-offset kernel
  --- i.e. the real stage-2/normalize-in-C work.
- **Tiny slices.** Per-position overhead dominates when slices are small
  (the fused-gather measurements of the issue draft), for the add-zero gather
  exactly as for the current one --- the drafts' argument that one code path
  degrades gracefully carries over unchanged.

[#123]: https://github.com/Mikolaj/horde-ad/issues/123
[readme]: https://github.com/Mikolaj/orthotope/blob/22f100aaa40344e23fc7b7dfc74f3db7843e1a8f/micro-regime3/README.md
[pos-effect]: https://github.com/Mikolaj/horde-ad/blob/master/docs/position-effect.md
[tgatherZSScalar]: https://github.com/Mikolaj/horde-ad/blob/e1bd5f5e22e38960958dbe2c7ba40ffca1a1b081/src/HordeAd/Core/OpsConcrete.hs#L1654-L1665
[tbuildS]: https://github.com/Mikolaj/horde-ad/blob/e1bd5f5e22e38960958dbe2c7ba40ffca1a1b081/src/HordeAd/Core/OpsConcrete.hs#L1776-L1789
[tscatterZSScalar]: https://github.com/Mikolaj/horde-ad/blob/e1bd5f5e22e38960958dbe2c7ba40ffca1a1b081/src/HordeAd/Core/OpsConcrete.hs#L1581-L1619
[arith-internal]: https://hackage.haskell.org/package/ox-arrays-0.2.0.1/src/ops/Data/Array/Strided/Arith/Internal.hs
[arith-c]: https://hackage.haskell.org/package/ox-arrays-0.2.0.1/src/cbits/arith.c
