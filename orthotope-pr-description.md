# PR description for orthotope (draft): speed up strided `toVector` fallbacks

*(Draft description for a future orthotope PR; the code is not written yet. Numbers and links to be refreshed when filing. Full analysis in the companion ox-arrays issue <link> and in https://github.com/Mikolaj/horde-ad/issues/123.)*

Proposed title: **Avoid going via lists in `toVectorListT`/`toVectorT` for strided arrays**

`toVectorListT` — and through it `toVectorT`, i.e. normalization — has three cost regimes:

1. fully normal strides — the whole array is one slice: a single memcpy;
2. a normal stride suffix — a lazy loop conses up one vector slice per contiguous run: memcpy per run, plus boxed per-run overhead;
3. **innermost dimension strided — a per-element fallback** (`vFromListN l . toListT`): a lazy list with a cons and a thunk per element.

For array interpreters downstream (ox-arrays, and horde-ad's AD on top of it), regimes 2–3 dominate gather-heavy programs: convolution gradients spend about two thirds of their runtime normalizing strided views this way, and the same traffic moved through stride-aware C kernels runs ~9–12× faster (measurements in the ox-arrays issue). In a compiled array language this would not matter; under interpretation the granularity of these library loops is a first-order cost.

The change keeps orthotope's no-mutation style — all mutation stays inside vector's own combinators:

1. replace regime 3's list-based fallback with `vGenerate` and a linear-index-to-strided-offset computation — machine-`Int` quot/rem per element, no per-element allocation, no change to the `Vector` class;
2. if measurement asks for more (possibly a follow-up PR): a fusion-friendly method in the spirit of vector's `unfoldrExactN`, stepping a multi-index counter by stride additions (no quot/rem), so stream fusion compiles the copy to a register loop behind a pure API;
3. optionally tighten regime 2 with a `toVectorT` that folds the runs directly instead of building the intermediate run list.

The yardstick: the `gather48`/`scatter48` micro-benchmark pair in horde-ad's `bench/ConvVjpBench.hs` — ~5–7ms via today's fallbacks vs ~0.55ms for the same traffic through C kernels.
