# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

horde-ad is a Haskell automatic differentiation library (reverse and forward mode) that supports array operations and generation of symbolic derivative programs. It is an early prototype and deliberately not coded defensively: code is expected to fail on cases not covered by current tests, and the fix is to add primitives/tests rather than defensive code.

Upstream stack: the array backend is ox-arrays (maintained by a horde-ad co-author) over orthotope. Mikolaj maintains horde-ad and, while not an orthotope maintainer, has a history of accepted orthotope PRs — equivalent standing when deciding where a fix should land — so performance fixes are planned across the whole horde-ad → ox-arrays → orthotope stack, orthotope changes going in as PRs to its maintainer. Orthotope deliberately contains no mutable code (a pure `Vector v` class API); keep proposals for it pure.

The closing portable-notes section holds the author-generic conventions and the machine-specific session facts — the sandbox's misleading "No such file" errors, phantom dotfiles in `git status`, `git`/`cabal` writes needing to run unsandboxed — skim it before debugging anything environment-related.

## Build and test commands

Development setup (fast builds, optimization off; guarded not to clobber an existing config):

    [ -f cabal.project.local ] ||
      cp cabal.project.local.development cabal.project.local
    cabal build

Run `cabal` (like all `git` writes and `gpg`) unsandboxed — `~/.cabal` is read-only under the inner sandbox (sandboxing notes below). A full build takes long: give Bash a generous timeout or run it in the background rather than concluding it hung. Local `cabal haddock` costs ~10 minutes even for a sublibrary (haddock re-runs GHC's front end over the whole library dependency, with the typelits plugins dominating typechecking) — prefer CI's `--haddock-all` step, which runs on every push.

Tests are computation-intensive, so run them with optimization even though the dev config sets `optimization: False` for builds: any timing taken without `--enable-optimization` runs ~8x slower and is **not** comparable to optimized numbers — a mysterious ~8x discrepancy is usually exactly this. Pass the flag on the command line:

    cabal test minimalTest --enable-optimization  # short, no dataset needed
    cabal test CAFlessTest --enable-optimization  # sequential; doubles as a benchmark
    cabal test sequentialMnistTest --enable-optimization  # same
    cabal test parallelTest --enable-optimization 2>/dev/null  # large MNIST tests; stderr redirect keeps interleaved printf tidy
    cabal test fullTest --enable-optimization  # everything, sequentially

Run a single test with a tasty pattern:

    cabal test CAFlessTest --enable-optimization --test-options='-p "gatherNested1"'

Test suites in `test/` are thin `Main` wrappers combining `testTrees` from modules in `test/simplified/` (the `testCommonLibrary` sublibrary); test tools (`EqEpsilon` for epsilon float comparison via the `--eq-epsilon` tasty option, `CrossTesting`) live in `test/tool/`. MNIST tests read gzipped IDX files from `samplesData/`. CAFlessTest must stay sequential: the AST-variable counter reset is not thread-safe, and some tests check printed ASTs whose numbering varies with execution order.

Benchmarks: `cabal bench shortProdForCI`, `longProdBench`, `shortMnistForCI`, `longMnistBench` (criterion; a sixth target, `realisticMnistBench`, is deliberately `buildable: False` so that plain `cabal bench` terminates in finite time). The `convVjpBench` benchmark (`bench/ConvVjpBench.hs`; not built under the `release` flag) is the [#123](https://github.com/Mikolaj/horde-ad/issues/123) diagnostic: `conv2dPreservingS` kernel- and input-gradient (dKrn/dInp) sweeps at 6–192, the symbolic and handwritten pipelines decomposed into pairwise-comparable `S-*`/`H-*` stage variants, `gather48`/`scatter48` isolating micro-benchmarks, `cnn-*` groups timing a real shaped two-layer CNN gradient, and a `pitfalls` group with the suite's single recorder of each known measurement trap (artifact hoisting, constant-cotangent embedding). It uses only random data (`randomValue`), so it needs no `samplesData` and runs anywhere; `PRINT_TERMS=1` prints the compared gradient programs instead of benchmarking. As the repo's only convolution-performance benchmark (the MNIST bench suites cover only FCNN nets) it outlives [#123](https://github.com/Mikolaj/horde-ad/issues/123): run it, with full criterion statistics, whenever touching conv-relevant code (gather/scatter rewrites in `contractAst`, the interpreter, the ox-arrays gather path) — the CI smoke run collects none. To analyze a run, collect it with `--benchmark-options='--csv FILE'` and check the module haddock's numbered time properties with `python3 tools/check-conv-bench-props.py FILE` (10% tolerance); the haddock classifies whether a failure means a broken measurement, an engine regression, or a legitimately shifted cost model.

CI protects `convVjpBench` twice: the build step compiles *all* benchmarks (`--enable-benchmarks all`) and the benchmarks step smoke-runs the whole suite with `--benchmark-options='-n 1'` — every benchmark once, no statistics, seconds total. That is build-and-runtime smoke protection, not a perf tripwire: CI criterion numbers are too noisy to gate on.

Source checkouts of ox-arrays and orthotope may be present as siblings (`../ox-arrays`, `../orthotope`) — whether a session sees them depends on the wrapper (sandboxing notes below); when hidden they report "No such file", and the released sources can always be unpacked from the cabal store instead (recipe in the Git-and-tooling notes). The kernels of interest are `mgenerate`, `Data.Array.Strided.Arith` and the `X.replicate` stride tricks. The `packages: ../ox-arrays` line in `cabal.project.local` is often commented out, in which case builds use the released ox-arrays from the cabal store, not the checkout — check before assuming local edits take effect.

Cabal flags: `with_expensive_assertions` (extra checks), `release` (set for Hackage releases; disables test suites that need unpackaged data), `test_seq` (force parallelTest to run sequentially).

Lint/format: `.hlint.yaml` (its `arguments:` passes `-XNoStarIsType`, mirroring the cabal's `default-extensions` — hlint doesn't read the cabal, and without the flag the seven files importing `GHC.TypeLits (…, type (*))` fail to parse) and `.stylish-haskell.yaml` (stylish-haskell); both tools are on PATH, hlint as a locally compiled v3.10 — earlier binaries mishandled that flag and silently *skipped* those seven files with a parse error, so "hlint-clean" claims from before 2026-07 don't cover them (`--cpp-simple` was dropped from the yaml at the same time: the fixed hlint's default CPP handling parses everything, while `--cpp-simple` itself broke on `Core/Types.hs`). CI (haskell-ci generated) builds and tests with GHC 9.10.3, 9.12.4 and 9.14.1, but its tests step runs only `minimalTest -p "detSquare"` (plus the benchmark smoke runs) — CAFlessTest and the other suites, including every printed-AST test, are validated only by local runs.

Standing checks, for a generic "run checks" request — each with its trigger:

- Always: `python3 tools/check-plan-citations.py DOC` over CLAUDE.md and every draft staged in the repo root; then, for any document edited since it was last verified, passes 2 and 3 of the three-pass discipline (portable notes below — pass 3, the quantified-claims grep, is the one that keeps finding real errors).
- When Haskell code changed: build, then `minimalTest` and `CAFlessTest` with `--enable-optimization` (the larger suites above when the change warrants), stylish-haskell and hlint on touched files.
- After a push: CI status via `curl -s "https://api.github.com/repos/Mikolaj/horde-ad/actions/runs?branch=BRANCH&per_page=3"`, reading each run's `head_sha`, `status` and `conclusion` (`gh` is unauthenticated). A green run also validates haddock markup, since the haddock step covers benchmarks and tests.
- After conv-relevant changes, and after any full `convVjpBench` run: the numbered time properties via `tools/check-conv-bench-props.py` (see the benchmark paragraph above).
- When a new self-checking assertion or checker tool is born: prove it non-vacuous by deliberately breaking it (portable notes), and record the proof next to it.

## Architecture

The library is organized around a final-tagless style: tensor operations are type classes (chiefly `BaseTensor` in `HordeAd.Core.Ops`) over a `target :: Target` type constructor, indexed by a type-level tensor kind `TK`. Objective functions are written polymorphically in `target` and then instantiated at one of three carriers:

- `Concrete` — plain evaluation on CPU arrays (backed by ox-arrays/orthotope). Defined in `Core/CarriersConcrete.hs`, instances in `Core/OpsConcrete.hs`.
- `ADVal target` — dual numbers for direct (tape-like) AD, generic over the underlying carrier. `Core/CarriersADVal.hs`, `Core/OpsADVal.hs`.
- `AstTensor` — symbolic AST terms. `Core/Ast.hs` (grammar), `Core/CarriersAst.hs`, `Core/OpsAst.hs`.

Tensor kinds (`Core/Types.hs`, `Core/TensorKind.hs`): `TKScalar r`, `TKR n r` (ranked: only rank in the type), `TKS sh r` (shaped: full shape in the type), `TKX sh r` (mixed), `TKProduct` (tuples); `TKR2`/`TKS2`/`TKX2` allow nested element kinds. Operation names are prefixed by variant: `r*` ranked, `s*` shaped, `x*` mixed, `t*` kind-polymorphic (`tlet`, `tpair`, `tproject1`). The shaped, ranked and mixed styles interoperate freely; conversions are zero-cost (`Core/ConvertTensor.hs`, `Core/Conversion.hs`).

### Two AD pipelines (`HordeAd.ADEngine`)

1. **Concrete AD** (`cgrad`, `cjvp`, `cvjp`): instantiates the function at `ADVal Concrete`. Sharing is preserved automatically; permits dynamic control flow; differentiation happens on every call.
2. **Symbolic AD** (`grad`, `vjp`, `jvp`, `vjpArtifact`, ...): instantiates at `AstTensor`, differentiates the AST once into a derivative "artifact" program, which is simplified and can then be interpreted many times on different inputs. Sharing must be marked explicitly with `tlet`.

Reverse-mode differentiation itself goes through **delta expressions** (`Core/Delta.hs`): a sparse representation of the linear map that is the derivative. `Core/DeltaEval.hs` transposes/evaluates it (`gradientFromDelta`, `derivativeFromDelta`), related, for all `d`, `dt` and `ds`, by `dt <.> derivativeFromDelta d ds = gradientFromDelta d dt <.> ds` — a property checked in the testsuite.

### AST processing pipeline

- `Core/AstVectorize.hs` — BOT (bulk-operation transformation): eliminates `build1`/indexing-under-build, which would otherwise explode delta expressions.
- `Core/AstSimplify.hs` — smart constructors that simplify by inspecting term roots; `Core/AstTraverse.hs` — full bottom-up simplification passes; `Core/AstInline.hs` — inlining and global sharing elimination; orchestrated by `Core/AstEngine.hs` (`simplifyArtifactRev`, etc.).
- `Core/AstInterpret.hs` + `Core/AstEnv.hs` — interpret AST terms in any tensor-class instance (the backend).
- `Core/PPEngine.hs`, `Core/PPTools.hs` — pretty-printing of ASTs/artifacts.

A deliberate layering rule (documented in `Core/Ast.hs` and `Core/Ops.hs`): `Ast*` modules (syntax) and `Ops*`/`Carriers*` modules (semantics) rarely depend on each other; they meet only in `AstInterpret`/`AstEnv` (syntax → semantics) and `OpsAst`/`CarriersAst` (semantics built from syntax).

### Supporting pieces

- `Core/Adaptor.hs` — `AdaptableTarget` converts user-level collections (tuples, lists of tensors) to/from a single tensor-kind representation `X vals`; this is how `grad` accepts functions over tuples.
- `Core/Unwind.hs` (and its more precisely-typed copy `Core/UnwindNum.hs`) — generic operations over nested product tensor kinds.
- `HordeAd.OpsTensor{,Ranked,Shaped,Mixed}` — the user-facing operation surface re-exported by the top-level `HordeAd` module; `Core/Ops.hs` holds the rawer class methods.
- `External/` — optimizers (SGD, Adam) and common NN building blocks.
- `example/` (public sublibrary `exampleLibrary`) — MNIST neural nets (fully connected, convolutional, recurrent; ranked and shaped variants) used by tests and benchmarks.

## Performance model

Runtime performance is an emergent property of four layers — AST term rewriting, the interpreter and its concrete kernels, GHC's optimizer, and the CPU — so it is decided empirically, not by reading source; a cost-centre profile is cheap to obtain (`--enable-profiling --profiling-detail=late` reuses the -O1 dependency store and rebuilds only the local packages). `contractAst` in `Core/AstTraverse.hs` (the backend-recognition pass, run just before interpretation) is by its own docstring "defined in an ad-hoc way based on benchmarks"; treat any rewrite-rule change there as benchmark-gated.

Rules that keep the measurements honest:

- **Only criterion numbers belong in comparison tables and in performance reasoning.** A tasty "Bench" total (the `TestConvQuickCheck` poor man's benchmarks: wall-clock / 100 runs, including per-run random generation and `allClose`, on a coarse ~10ms timer) and a criterion per-call number are *different quantities*; never put both in one table, row or column. Treat any non-criterion figure — a GitHub issue's numbers, tasty totals (which are also machine/context/GC-dependent and not portable across setups or time) — as *anecdotal*: mention it as such, don't base a conclusion on it.
- **Attribute a performance difference by controlled experiment, not hypothesis.** A ~3.3x gap between conv-gradient benchmarks, blamed in turn on harness noise and machine/GHC differences, was really a per-call artifact rebuild — settled by a discriminating benchmark (artifact hoisted out of the timed loop vs rebuilt per call); rule out machine/GHC only once the setup is confirmed identical. Before a number enters a commit message or public doc, ask what *instrument* produced it and whether a cheaper decisive check (printed-AST churn location, a provably-unaffected control) settles the question first.
- **An A/B across two *builds* needs interleaving and controls, because recompilation itself moves numbers.** Two binaries differing by a one-line toggle shift *unaffected* benchmarks by ±2–5% (code-layout/codegen noise), and batched runs (all A, then all B) additionally confound with time/thermal drift. Run interleaved A/B pairs (drift cancels within a pair) and include per-pair controls: a suite the change provably cannot affect (e.g. the concrete `VTA` MNIST groups of `BenchMnistTools` for a `contractAst` change — the concrete pipeline never runs it), and/or a change-independent variant (e.g. `S-exec-raw` for a `contractAst` change: the raw artifact is contraction-independent — see the `vjpArtifact` bullet below — so it is identical across the toggle). The change's effect is the target's per-pair ratio minus the control's.
- **The printed-AST tests are a free, decisive oracle for "can this rewrite affect that program at all".** An unchanged printed artifact means a byte-identical artifact and hence identical interpretation, so checking *where* a rewrite's printed-AST churn falls, before benchmarking, can settle a claim in minutes — a purported MNIST speedup was disproved this way (the churn was confined to CNN tests, so FC-MNIST could not have moved).
- **Benchmark inputs must be random, not broadcast constants.** A constant input like `treplicate … (sscalar 7)` is a stride-0 broadcast that the simplifier constant-folds *through* the very operations you mean to time — a CNN gradient benchmark with a constant glyph lost its im2col gathers to folding and under-measured 24ms vs the honest 158ms. Use `randomValue`; a constant is only right when the *test* (e.g. a printed-AST test) wants a canonical small term.

Cost facts worth knowing before optimizing:

- **The two AD pipelines have different cost shapes.** `cgrad`/`cvjp` re-run differentiation on every call; the symbolic tools (`grad`/`vjp`) pay tracing + `simplifyUserCode` + AD + `simplifyArtifactRev` once — a roughly size-independent overhead — then only interpret the artifact per call. Intended usage: build the artifact once (`vjpArtifact`/`gradArtifact`/`revArtifactAdapt`), interpret it many times (`vjpInterpretArtifact`); a benchmark calling full `vjp` per iteration conflates pipeline cost with execution cost.
- **`sreplicate`, `sreplicateN`, `stranspose` are metadata-only** (stride tricks; ox-arrays `X.replicate` is stretch-to-stride-0), and the ox-arrays dot and elementwise kernels (`Data.Array.Strided.Arith`) are stride-aware. Broadcasts and transposes fed into a dot or a `*` do **not** materialize, so don't rewrite them away on the assumption that they allocate.
- **`tssumN` is iterated `tssum`** (`Core/OpsConcrete.hs`): one full pass and allocation per summed dimension.
- **Interpreted `sgather` dominates gather-heavy programs** (the im2col patch arrays of convolution gradients — often ~two thirds of runtime). It runs through ox-arrays' `mgenerate`: per output position (the `shm` dims) evaluate the index and copy a slice (the `shn` dims); the per-element boxed-`Integer` index arithmetic is the hot loop. Two benchmark-confirmed consequences: (1) `contractAst` sorts a gather's `shn` dimensions ascending, via metadata-only compensating transposes, so the largest dimension is innermost and the copy's inner loop amortizes the per-step overhead — reordering the `shm` dims, by contrast, changes nothing; (2) fusing two gathers into one is a *pessimization* — it trades few large-slice copies for many tiny ones while `mgenerate`'s cost is per position — so the phase-gating that prevents that fusion is intentional, and sorting cannot rescue the fused form (its `shm` order measures flat, the `fused-gather-shm-sorted-*` benches; its `shn` is tiny and already sorted, fusion having consumed the large dims into the index function). One level down, the per-step cost is orthotope's run-decomposition of each strided slice (`toVectorListT`), with a per-element fallback when the innermost dim is strided. Reducing it further has two candidate designs, neither implemented yet: the two-stage upstream (ox-arrays/orthotope) fix in the [#123](https://github.com/Mikolaj/horde-ad/issues/123) material, and the client-side add-zero gather of `notes-add-zero-gather.md` (repo root, committed) — gather rebuilt on the scatter model, each strided slice densified through the stride-aware C arith kernels by adding a replicated scalar zero (normalize-in-C with a fused redundant add); it needs no upstream release and the `scatter48` bound prices it at ~7–10× on the isolated chains. The note's Consequences section records what the design changes in the staged drafts.
- **Concrete scatter is slice-based and ~8–10× cheaper than gather on the same index map and strided-read workload** (`scatter48` ~0.55ms vs `gather48` ~4–6ms). As gather's transpose it performs the same element transfers and, where the index map is many-to-one, even more arithmetic — it sums where gather copies — so the gap is code path, not data volume. The path: `tscatterZSScalar` does per-position index eval + `IntMap.insertWith (+)` with whole-slice adds through the stride-aware `NumElt` C kernels, then flat `VS.copy` write-outs — the interpreted Haskell is per *chunk*, all element traffic is C. The accumulation is what dodges the Haskell strided-normalize (it consumes strided views in C and leaves dense buffers to memcpy), a trick the current gather doesn't borrow, though the add-zero design above shows how a sum-free gather could: force a redundant add. Corollaries: extending the `shn`-sort to scatter is an outright pessimization, measured ~4.4× (`two-scatters-ad-shn-sorted`, 2.3ms vs 0.52ms) — each slice is added as one flat vector, so a sorted `shn` has no per-`shn`-dim loop to amortize, while the compensating transposes leave the slice views strided; scatter in its natural orientation is the empirical bound for a fast gather path (its strid-ified and fused forms are far slower); and a rewrite's whole-program effect grows with problem size, converging toward the dominant op's win (the `shn`-sort is negligible on small overhead-bound nets, ~18% on a 24×24 CNN gradient once gathers dominate).
- **`vjpArtifact` does not run `contractAst`** — it runs `simplifyUserCode` + `revProduceArtifactDt`; `contractAst`'s only caller is `simplifyInlineContract`, which `simplifyArtifactRev` and its `Fwd` sibling apply to artifacts (convVjpBench's handwritten-term variants also call it directly). Hence the *raw* artifact is contraction-independent — which explains `S-exec-raw`'s role as an A/B control and means "artifact" benchmarks measure different pipelines depending on whether they stop at `vjpArtifact` or add `simplifyArtifactRev`.

Adding a `contractAst` rewrite rule: put it in `contractAst`, not a smart constructor (which fires in every phase and reshapes intermediates other rules match on), applied at a node's exit and *after* any case that hoists structure out of the same constructor and re-enters `contractAst`. Make it idempotent, and identify which existing rules could undo the form it introduces — for the `shn`-sort, `astTransposeS`/`astGatherCase` only absorb *leading*-dims permutations while the compensating transposes permute trailing dims — recording that argument as a code comment at the rule.

## Coding style

Author-generic style conventions are collected in the portable-notes section at the end of this file; what follows is horde-ad-specific.

- `StrictData` is on, plus `TypeFamilies`, `PatternSynonyms`, etc. — see `common options` in the cabal file. Type-level shape arithmetic relies on the `ghc-typelits-knownnat` and `ghc-typelits-natnormalise` plugins.
- **Float epsilon margins depend on magnitude, GHC version and machine.** When compared values are large (e.g. gradients reaching ~5e5, where one Float ulp is ~0.03), widen the `assertEqualUpToEpsilon` margin rather than pinning exact low ulps or rewriting the expected values to one machine's output.

## Testing and correctness

- **Benchmarks are not correctness tests.** A body that forces a result by comparing it to itself (`allClose v v`) checks only that the body compiles — it never catches a wrong-operator or copy-paste bug — so when cloning a variant, cross-check every analogous position by hand: the operator called, the data helper used, the point at which a derivative artifact is interpreted. Every benchmarked path needs a *separate* `assertEqualUpToEpsilon` check on same-shaped data — hence deterministic correctness in `TestConvCorrect` alongside the poor man's benchmarks in `TestConvQuickCheck` — though existing tests of closely similar code suffice (the `cnn-*` benchmark groups lean on the many CNN tests).
- **Deterministic vs QuickCheck split for stable timing.** Keep QuickCheck properties and poor man's benchmarks in one module (`TestConvQuickCheck`) and deterministic `testCase` correctness in another (`TestConvCorrect`), so the deterministic suite's wall-clock stays comparable across runs. Share helpers by *exporting* them from the QuickCheck module (no import cycle).
- **Printed-AST regression churn** after simplifier changes is expected and mechanical: refresh the expected strings from a sequential `CAFlessTest` run (parse the tasty-hunit expected/but-got pairs; expect two or three rounds, since each test stops at its first failing assertion), keep that churn in its own commit, and watch for eps-based numeric tests (e.g. `3barS`) drifting in the last Float digit when operation order changes.
- **`cnnObjective` (exported from `TestMnistPP`) is the objective shared between a printed-AST test and its benchmark**: `testCNNOPP2S` consumes it with a constant glyph at print-friendly sizes, `convVjpBench`'s `cnn-*` groups with a random glyph at square doubling sizes — the benchmark provably measures the net the test validates, and the refactor is verified free by the printed-AST test not churning.

## Portable notes: same author, same machine

Nothing in this section is horde-ad-specific: it should hold for other projects by the same author, in the same coding style, developed on the same machine behind the same outer sandbox. Examples are from horde-ad unless attributed.

### Coding style

- Haddocks are expected on all module headers and on functions/types in "major"/interface modules. Minor internal helpers get no haddocks; their comments, if any, must not be haddocks and may describe implementation details and go out of date — don't treat every comment as authoritative documentation.
- Prefer assertions over comments to document invariants, unless that would be too verbose.
- `-fno-ignore-asserts` stays on in the cabal `common options` stanza, so failed `assert`s crash release builds too — crash reports from released code can name assertions.
- Lens libraries are deliberately avoided; state lives in plain records (with record punning).
- GHC2024 is the default language; each project's default-extensions live in the cabal `common options` stanza. Projects normally set `StrictData` — assume it unless the project's notes say otherwise.
- Formatting (also spelled out in the README's Coding style section): 2-space indent, 80 columns, spaces not tabs, spurious whitespace avoided, spaces around arithmetic operators encouraged. Inline comments (`--`) are prefixed with exactly two spaces, unless indented to match other comments. Operators such as `(` and `,`, `<$>` and `<*>`, comment starts, etc. on consecutive lines either align or, if that would make lines too long, indent by 2 spaces from the previous indentation level. Generally, relax and stick to the style apparent in the file being edited.
- Put large, mechanical formatting changes in their own commit, separate from substantive changes.
- If hlint is still too naggy, adding more exceptions to `.hlint.yaml` is fine — don't contort code to appease it.
- **Uniformity across analogous positions is itself a review tool.** Parallel code (e.g. the `Preserving`/`Shrinking`/`Padded` × `dKrn`/`dInp` × size families in the conv tests) and its comments should be identical modulo names and shapes; diffing analogous positions is how bugs surface, and a drifted one is normalized toward the cleaner form, not the first draft. One level up, things meant to be compared (benchmark variants, test cases) are designed as one-to-one counterparts — measuring the same stage, differing only along the compared axis, adjacent in the output — not accreted one probe at a time.
- **Order definitions as they are used, and let every summary span its whole subject.** Auxiliary definitions, do-bindings, list entries and top-level functions follow the order in which their consumers run, print or assert, wherever that order is deliberate or visible; an overview (module haddock, section comment) covers every member of what it describes, not the subset that existed when it was written. Both properties decay silently under accretion — after adding to a set, re-normalize the whole set, not just the new member.
- **One meaning per name, and label deliberate asymmetries.** A letter or abbreviation keeps a single meaning per vocabulary (not `S`/`H` as both the pipelines and the gather orientations they produce, nor `c` as both concrete and contracted); and where uniformity is intentionally broken — a counterpart deliberately absent, a definition that is a fixture rather than a candidate — the site says so and why: an unexplained asymmetry reads as drift and costs a review round-trip.
- **Comments.** A substantial note that sibling sites would repeat with only names changed is stated once, at its canonical occurrence; tiny notes, by contrast, are repeated identically at every analogous position. Match the codebase's spelling and hyphenation (e.g. "poor man's", not "poor-man's") and keep terminal punctuation consistent across parallel clauses (don't end one with ";" and its sibling with "."). A comment must still match the code after refactors — watch for notes invalidated by later changes. Leave pre-existing comments alone unless asked — flag them instead.
- In tests, an expected crash may never fire due to laziness: an assertion or lookup error is swallowed if the offending value is never forced (force it — under `StrictData`, WHNF fully builds an AST). Catch real assert failures with `Control.Exception.try`, rather than pattern-matching on output; the `blame`/`swith` details (from the `assert-failure` package) go to the trace output, not into the exception.
- **Prove a self-checking assertion is non-vacuous.** An invariant check — e.g. verifying that scatter is the adjoint of gather via `sdot0 (sgather x f) y == sdot0 x (sscatter y f)` — should be shown to actually fail when the property is deliberately broken, or it may be passing vacuously.
- Share the objective between a test and its benchmark via one exported helper, parameterized by what differs, so the benchmark provably measures what the test validates — share code, not configuration.

### Working style

- **Scope discipline.** On an ambiguous request ("the *new* tests") take the narrower reading, do it, and flag the boundary with an offer to expand — don't silently touch pre-existing code. Split unrelated work into separate PRs (e.g. convolution benchmarks + tests in one PR, the simplifier fix in another).
- **Verify before claiming done.** "Uniform" / "correct" / "passes" must rest on an actual line-by-line cross-check or a test run, not on the fact that it compiled; a claim about a touched file covers its pre-existing code too, so audit that as well.
- **Only/every/never claims must rest on repo-wide grep, not on the file where the pattern was first noticed** — analogous-variant families (`Preserving`/`Shrinking`/`Padded` × `dKrn`/`dInp`, the ranked/shaped/mixed op surfaces, the `Ops*` instances) make single-file generalization treacherous. The same discipline applies before concluding "this cannot happen here": grep for *every* site that could do it.
- **Commits should be clean and logical, not a diary of the work.** File-partition them, order them so exports precede uses, and fold a follow-up refactor into the commit where the code is logically born rather than adding "add then move" churn.
- **Never push, or open/force-update a PR, without an explicit go-ahead.** Permission to make a change is not permission to publish it.
- **Record don't-do rulings next to the do's.** Refuted designs live in the working documents together with the evidence that killed them, precisely so they aren't re-proposed later; when a new idea dies to evidence, write the ruling down where the next reader will look. (E.g. gather fusion, the `shm` flip and the summation-structure rewrite, each recorded with its killing measurement in the [#123](https://github.com/Mikolaj/horde-ad/issues/123) material.)
- **Drafting GitHub-bound texts**: one file per destination (issue, its design comment, PR description, upstream PR), staged in the repo root until posted; keep the *design* implementation-ignorant and put measured results in the PR description; deliberate overlap between files is fine to make each self-contained. Don't attribute design intent to code that is merely generic ("assumes irregular indexing") — state observed granularity and cost, not motives. Prefer reference-style markdown links so prose stays within 80 columns.
- **Links that cite source code — in GitHub-bound texts and the reference documents — must be GitHub permalinks pinned to a commit hash that is on `master`** (`…blob/<commit>/….hs#L12-L34`): branch-name and unpinned links drift or die when branches move, while a master hash survives rebases and stays verifiable — the citation checker validates such permalinks against the pinned commit. Deliberately-living whole-file links (e.g. the README's `blob/master` pointers) are outside the rule, as are links to foreign repos, which the checker cannot verify.
- **State mathematical properties in the code's surface notation, not abstract math** (in docs and comments alike). Write the gather/scatter adjoint law as `sdot0 (sgather x f) y == sdot0 x (sscatter y f)`, not `⟨gather x, y⟩ = ⟨x, scatter y⟩`: keep the index function `f` explicit rather than hidden in the operator name, and put quantifiers first (*for all `f`, `x`, `y`*). It reads in the vocabulary of the code and keeps the shapes checkable.

### Document verification: the three-pass discipline

Planning/reference documents (this file and any GitHub-bound drafts staged in the repo root) make checkable claims. Whenever such a document (or code it cites) is edited, run three passes:

1. `python3 tools/check-plan-citations.py [DOC]` (from the repo root; DOC defaults to this file) — re-validates `file:line` citations, resolving each, checking the line range and printing the first cited line to eyeball against the surrounding claim, and pinned GitHub permalinks against the commit they name via `git show`, so those never drift; foreign-repo links can't be verified locally.
2. Check that paths, cabal targets and flags named in prose exist.
3. Re-verify only/every/never claims by repo-wide grep.

The passes are ordered by yield: the mechanical ones catch drift, but the quantified-claims grep has found real, long-standing errors every time it has been run, so it is the pass never to skip.

### Sandboxing on the dev machine (outer wrapper + inner sandbox)

Claude Code sessions on Mikolaj's machine run inside an outer bwrap sandbox wrapper (PID 1 is `bwrap`), beyond Claude Code's own (inner) sandbox. Current state and its implications:

- Run `git` writes, `cabal` and `gpg` unsandboxed — the inner sandbox mounts `.git/config`, `~/.cabal` and `~/.gnupg` read-only. `git checkout -b` / `branch -f` fail to lock the config, though the ref often moves anyway — verify refs afterwards. GPG signing (`commit.gpgsign` is on) fails sandboxed and works unsandboxed, so never fall back to `--no-gpg-sign`; SSH pushes likewise work only unsandboxed. Other read-only HOME mounts (e.g. `~/.claude/projects`) also need unsandboxed commands for deletions.
- An unsandboxed (or otherwise permission-gated) command sits at the approval prompt until answered — on the user's screen indistinguishable from a hung long-running command — so before issuing an optional or expensive one (a haddock run, an extra rebuild), say what is about to appear.
- Paths the wrapper blocks report "No such file or directory", not "Permission denied". If a path outside the repo seems missing — especially one documented as expected, like the `../ox-arrays` sibling checkout — suspect the wrapper and ask, rather than record the path as absent. `dangerouslyDisableSandbox` bypasses only the inner sandbox, never the wrapper.
- The wrapper mounts a hand-picked, changeable subset of HOME, curated per-path rather than per-directory: that an entry is visible says nothing about how much of its contents is (at times `~/r` has held only the current repo, and `~/.ssh` carries public material only). Don't infer access from a directory listing and don't record mount inventories — they go stale; verify the specific path at the moment it matters.
- Inside the inner sandbox, HOME appears to be the repo root, so sandboxed `git status`/`ls` show phantom untracked dotfiles (`.bashrc`, `.gitconfig`, `.vscode`, ...) that don't exist on the real filesystem. Ignore them; verify with an unsandboxed command before deleting any.
- System state under wrapper-hidden paths (e.g. `/etc/apparmor.d`) cannot be inspected from inside a session; such diagnosis must be done by Mikolaj in a plain terminal.
- The nested inner sandbox works only because three things hold: the Ubuntu AppArmor userns restriction is off (`kernel.apparmor_restrict_unprivileged_userns=0`, no `bwrap-userns-restrict` profile), the wrapper mounts the repo read-write, and `enableWeakerNestedSandbox: true` is in effect — inherited from the `sandbox` block of the user-level `~/.claude/settings.json` (a project `sandbox` block wholesale replaces the user-level one — settings objects don't deep-merge — so a project that defines one must repeat the flag). If sandboxed commands start failing at startup, check these three first.

### Git and tooling in sessions

- Interactive git is unavailable (`rebase -i`, `add -i`). Rewrite history with `git reset --mixed <base>` + re-`add`/`commit` per file group, reusing messages via `git commit -C <hash>` / `-F <file>`.
- Amending a non-HEAD commit (no `rebase -i`): save working-tree edits as a patch, `git reset --hard <target>` (spares untracked files), apply, `--amend`, then `git cherry-pick` the successors (conflict-free when they don't touch the amended files); update recorded hashes.
- The repo root accumulates many untracked scratch files (`log*`, `*.prof`, `cabal.project.local.bkp*`, `.emacs.desktop*`, etc.); leave them alone and never `git add` them wholesale.
- `awk` is not on PATH — use `python3` or `grep`.
- `gh` is not authenticated; for GitHub reads use `curl` against `api.github.com` (on the sandbox network whitelist).
- To combine several tasty `-p` patterns, tasty wants awk-style syntax: `-p "/foo/ || /bar/"`.
- GHC emits warnings only on *recompilation*: a cached, up-to-date build can hide warnings (e.g. `-Wredundant-constraints`) that a full rebuild would surface — don't infer "no warnings" from a clean second build.
- Keep one set of cabal flags across a session — changing flags (e.g. toggling `--enable-optimization` or `--enable-profiling`) forces a full rebuild of the local packages, though each flag set's dependency builds stay cached in the store. Pass such flags on the command line rather than editing `cabal.project.local`.
- The `/tmp` scratchpad is wiped by a machine restart — put anything that must survive (patches, notes) in the repo tree; binaries just get rebuilt.
- Exact dependency sources are always available: unpack `~/.cabal/packages/hackage.haskell.org/<pkg>/<ver>/` matching `dist-newstyle/cache/plan.json`.
- `.github/workflows/haskell-ci.yml` is generated by `haskell-ci` from the `.cabal` file — regenerate it rather than hand-editing, and re-apply any hand-maintained steps afterwards (the `tests` and `benchmarks` steps, marked by a comment in the workflow).
- Toggle-based A/B builds: make a rule's guard unsatisfiable (e.g. `sigmaL /= sigmaL`), build and copy the binary aside, restore + rebuild + copy again, then run the two preserved binaries in interleaved pairs (no rebuild between A and B); an edited `Core` module rebuilds in ~10 min.
