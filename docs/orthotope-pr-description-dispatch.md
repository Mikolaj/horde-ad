# PR description for orthotope (draft): toList's fast cases, and inlining that lets consumers fuse

*(Draft of a second pull request against [orthotope][repo], stacked on the strided-fill PR: branch `pr-mikolaj-canonical-dispatch`, four commits on top of `pr-mikolaj-toVectorListT`. Unwrapped by destination convention --- one line per paragraph --- since it is pasted into a PR body. Measured results belong here; the benchmark that produced them stays on its branch, linked rather than merged. Links to be finalized when filing, the branch commits included, none of which is pushed as this is written.)*

## What this changes

Four things, each its own commit: two about what `toList` does and what a consumer of it compiles to, two about the pragma policy of the wrapper modules and the generic layer under them, and none touching what any function computes.

**`toListT` lists a dense view in O(1).** Its fast path fired only for a view at offset 0 with the raw natural strides over a vector of exactly its length; every other view, dense ones included, was listed by an `indexT` per element. It now dispatches on `regimeT`, the fill PR's regime classification of the canonical view: a canonical Whole lists the vector and a canonical Slice lists the slice, so an indexed sub-array, a row, a view with unit dimensions of any stride and a view with mergeable dimensions each take one slice and the vector's own list. The element-by-element walk stays for runs and strided views, on purpose: it yields lazily in row-major order, which `foldr` over `toList` and a prefix-taking consumer rely on, and the alternatives that would be faster per element materialize the array first. The comment on it says so, and says what would change if that contract were given up.

**Every wrapper's `toList` is INLINE.** Seven of the nine wrapper modules, Dynamic, Ranked and Shaped each boxed, Storable and Unboxed, had no pragma on `toList` and two had INLINABLE, and neither let a consumer fuse with the list. The reason, read off the consumer's Core: `toList` carries an `Unbox` constraint, so the specialiser fires first and rewrites the call to a copy specialised to the element type in the consumer's module; that copy is then optimised as a binding of its own, the generic `toList`, `toListT` and the `build` inlining into it and growing it into a worker; and inlining the worker at the call site is judged on the grown body and refused. The `build` ends up inside the worker and the `foldr` outside it, and fold/build has nothing to match. INLINE substitutes the original right-hand side at the call site before anything grows, and the `build` lands beside the `foldr`.

**One pragma per function across the nine wrapper modules.** They presented one API under several regimes: DynamicS and DynamicU marked about half their wrappers INLINE, RankedS marked nearly everything INLINABLE and ShapedS about a third, and the other five marked almost nothing. Each function now carries one pragma in every module that defines it, by four classes: INLINE for the wrappers a consumer has to see through for fusion, `fromList`, `fromVector`, `toVector`, `mapA`, the `zipWith*A` family, `constant`, `foldrA` and the reductions and generators; INLINABLE for the structural operations with real bodies, `broadcast`, `pad`, `window`, `append`, `ravel`, `unravel`, `normalize`, `reduce`, `rerank`, `update` and their kin, where specialising to the element type is wanted and duplicating the body is not; and no pragma for the O(1) view constructors, `transpose`, `reshape`, `slice`, `rev`, `index` and the rest, where no fusion is at stake. The classes are the mechanism above applied uniformly and are a starting default, not a measurement; the commit says so.

**The generic layer is INLINE throughout.** It nearly was; five functions had drifted, `broadcast`, `rotate`, `ravelOuter`, `allSameA` and `update`, and now follow the layer's one rule, since it is the layer a wrapper's specialised copy is meant to absorb.

## Measurements

**`toListT`.** On a 2000 by 5000 array transposed to force the walk, `head`, `take 3`, a short-circuiting `any` and `head` of an indexed row each allocated about 70 to 90 KB under the interpreter, against 800 MB to force the vector and 8.6 GB to walk the whole list, so the prefix contract holds; the fast paths are O(1) before the list itself.

**Fusion.** A `foldr` and an `any` over `toList` compiled with -O through the Storable, Unboxed and boxed Dynamic wrappers and through RankedS: with INLINE, fold/build fires seven times on 9.12 and nine on HEAD and no `toList` worker is left in the consumer's Core; the same consumer against RankedS at INLINABLE calls the specialised worker on both compilers, fold/build unfired for it. Core inspected on 9.12.

## Validation

The test suite passes unchanged after each commit, 620 cases, among them `toList` on a dense array, the Whole path, and on a transposed one, the walk, with the sum and maximum checks running `toList` over the suite's other views. The fusion and laziness readings above are the measurements this PR rests on; nothing here reaches the micro-benchmark's fill.

## What this does not do

It does not change what `toList` promises for runs and strided views. A fill followed by `vToList` would produce those elements faster and is not harder to write; it materializes the array before the first element, and whether `toList` should do that is a question about its consumers rather than about this code.

[repo]: https://github.com/augustss/orthotope
