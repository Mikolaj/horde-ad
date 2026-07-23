# Comment for the ox-arrays issue (draft): the two-stage design

*(Draft of the single design comment on the ox-arrays issue drafted in `oxarrays-issue-description.md`. Links — notably to the orthotope PR — to be filled in when filing.)*

# The two-stage design

The fix splits naturally in two stages across the package boundary, and the second stage may never be needed.

**Stage 1 — orthotope, pure.** The costly regimes live in `toVectorListT`, and orthotope deliberately contains no mutable code (everything goes through the pure `Vector v` class), so the fix stays pure — prepared as an orthotope PR (<link>):

1. replace regime 3's fallback (`vFromListN l . toListT`, a lazy list with a cons and a thunk per element) with `vGenerate` and a linear-index-to-strided-offset computation — machine-`Int` quot/rem per element, no allocation, and no change to the `Vector` class;
2. if measurement asks for more, add a fusion-friendly class method in the spirit of vector's `unfoldrExactN`, stepping a multi-index counter by stride additions (no quot/rem); stream fusion turns the strict state into a register loop, still behind a pure API;
3. optionally tighten regime 2 with a dedicated `toVectorT` that folds the runs directly instead of building the run list.

ox-arrays then needs almost nothing: `mtoVector`/`stoVector` already delegate to `toVectorT`, and `mvecsWritePartialLinear` replaces the TODO'd fold with a `VS.copy` of the (now fast) `toVectorT` result — one intermediate vector per slice, negligible next to today's cost, and the mutation stays in ox-arrays, whose `MixedVecs` machinery is mutable already.

**Stage 2 — ox-arrays, C, only if a measured gap remains.** A strided-copy kernel in the existing cbits, writing directly into the destination buffer at an offset. Unlike the arith kernels it is type-agnostic — it needs only an element byte-width, no per-type TH families — and the existing wrapper plumbing (`wrapUnary` in `Data.Array.Strided.Arith.Internal` already passes shape, strides and an offset pointer to C) shows exactly how to bind it. In spirit the walk already exists: the `_sv_strided` arith kernels traverse arbitrary strides and write densely, and a strided copy is that walk minus the arithmetic — which a client can even exploit today as an interim, densifying each slice by adding a replicated scalar zero through `wrapBinarySV` (see the issue above). The gate for this stage: a gap that survives both stage 1 and that interim on the isolated `gather48`/`scatter48` pair.

Either way, gather-heavy clients get fast with no client-side changes: `mgenerate`'s per-position Haskell overhead remains, but it is per position (point 1 of the issue above), not per element, and the scatter numbers bound the expected effect — slice-level C traversal of this same traffic runs in ~0.55ms where the current gather path takes 5–7ms. Dynamically switching between per-element and per-slice implementations (e.g. on the slice size) should be unnecessary: one code path degrades gracefully, and where slices are tiny, per-position overhead dominates regardless (the fused gather of point 1 of the issue above).
