# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

horde-ad is a Haskell automatic differentiation library (reverse and forward mode) that supports array operations and generation of symbolic derivative programs. It is an early prototype and deliberately not coded defensively: code is expected to fail on cases not covered by current tests, and the fix is to add primitives/tests rather than defensive code.

Upstream stack: the array backend is ox-arrays (maintained by a horde-ad co-author) over orthotope. Mikolaj maintains horde-ad and, while not an orthotope maintainer, has a history of accepted orthotope PRs — equivalent standing when deciding where a fix should land. Performance fixes are therefore planned across the whole horde-ad → ox-arrays → orthotope stack, with orthotope changes going in as PRs to its maintainer. Orthotope deliberately contains no mutable code (a pure `Vector v` class API); keep proposals for it pure.

The closing portable-notes section holds the author-generic conventions and the machine-specific session facts — the sandbox's misleading "No such file" errors, phantom dotfiles in `git status`, `git`/`cabal` writes needing to run unsandboxed — skim it before debugging anything environment-related.

## Build and test commands

Development setup (fast builds, optimization off; guarded not to clobber an existing config):

    [ -f cabal.project.local ] ||
      cp cabal.project.local.development cabal.project.local
    cabal build

Run `cabal` (like all `git` writes and `gpg`) with the sandbox disabled — `~/.cabal` is read-only under the inner sandbox; details in the sandboxing notes at the end of this file.

A full build takes long — give Bash a generous timeout or run it in the background rather than concluding it hung.

Tests are computation-intensive, so run them with optimization even if the dev config disables it for builds. `cabal.project.local` defaults to `optimization: False` (-O0), so any timing taken *without* `--enable-optimization` runs ~8x slower and is **not** comparable to optimized numbers (a mysterious ~8x discrepancy is usually exactly this); pass `--enable-optimization` on the command line.

    cabal test minimalTest --enable-optimization    # short, no dataset needed
    cabal test CAFlessTest --enable-optimization    # sequential; doubles as micro-benchmark
    cabal test parallelTest --enable-optimization 2>/dev/null  # large MNIST tests; stderr redirect keeps interleaved printf tidy
    cabal test fullTest --enable-optimization       # everything
    cabal test sequentialMnistTest --enable-optimization

Run a single test with a tasty pattern:

    cabal test CAFlessTest --enable-optimization --test-options='-p "gatherNested1"'

Test suites in `test/` are thin `Main` wrappers combining `testTrees` from modules in `test/simplified/` (the `testCommonLibrary` sublibrary). Test tools (`EqEpsilon` for epsilon float comparison via the `--eq-epsilon` tasty option, `CrossTesting`) live in `test/tool/`. MNIST tests read gzipped IDX files from `samplesData/`. CAFlessTest must stay sequential because the AST-variable counter reset is not thread-safe; some tests check printed ASTs whose numbering varies with execution order.

Benchmarks: `cabal bench shortProdForCI`, `longProdBench`, `shortMnistForCI`, `longMnistBench` (criterion). The `convVjpBench` benchmark (`bench/ConvVjpBench.hs`; not built under the `release` flag) is the issue-#123 diagnostic: `conv2dSameS` kernel- and input-gradient (dKrn/dInp) sweeps at 6–192, `gather48`/`scatter48` isolating micro-benchmarks, and `cnn-*` groups timing a real shaped two-layer CNN gradient. It uses only random data (`randomValue`), so unlike the MNIST suites it needs no `samplesData` and runs anywhere. Setting `PRINT_TERMS=1` makes it print the compared gradient programs instead of benchmarking. Beyond issue #123 it is the repo's only convolution-performance benchmark (the MNIST bench suites cover only FCNN and RNN nets), so it stays after the issue closes: run it, with full criterion statistics, whenever touching conv-relevant code (gather/scatter rewrites in `contractAst`, the interpreter, the ox-arrays gather path) — the CI smoke run collects none.

CI protects `convVjpBench` twice: the build step compiles *all* benchmarks (`--enable-benchmarks all`), and the benchmarks step smoke-runs the whole suite with `--benchmark-options='-n 1'` — criterion runs every benchmark once, no statistics, the entire suite in seconds. That is build-and-runtime smoke protection, not a perf tripwire: CI criterion numbers are too noisy to gate on.

An ox-arrays source checkout lives at `../ox-arrays` — read it there when digging into backend kernels (`mgenerate`, `Data.Array.Strided.Arith`, the `X.replicate` stride tricks). The `packages: ../ox-arrays` line in `cabal.project.local` is often commented out, in which case builds use the released ox-arrays from the cabal store, not the checkout — check before assuming local edits take effect.

Cabal flags: `with_expensive_assertions` (extra checks), `release` (set for Hackage releases; disables test suites that need unpackaged data), `test_seq` (force parallelTest to run sequentially).

Lint/format: `.hlint.yaml` (hlint with `--cpp-simple -XNoStarIsType`) and `.stylish-haskell.yaml` (stylish-haskell). Known and accepted hlint blind spot: its parser fails on `import GHC.TypeLits (…, type (*))`, silently skipping every file with such an import (`OpsConcrete.hs`, `ConvVjpBench.hs`, three example modules) — don't report "hlint-clean" for those files. CI (haskell-ci generated) builds and tests with GHC 9.10.3, 9.12.4 and 9.14.1.

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

- **Only criterion numbers belong in comparison tables and in performance reasoning.** A tasty "Bench" total (the `TestConvQuickCheck` poor man's benchmarks: wall-clock / 100 runs, including per-run random generation and `allClose`, on a coarse ~10ms timer) and a criterion per-call number are *different quantities*; never put both in one table, or even one row/column. Treat any non-criterion figure — a GitHub issue's numbers, tasty totals — as *anecdotal*: mention it as such, don't base a conclusion on it. Tasty totals are also machine/context/GC-dependent and not portable across setups or time.
- **Attribute a performance difference by controlled experiment, not hypothesis.** A ~3.3x gap between conv-gradient benchmarks, blamed in turn on harness noise and machine/GHC differences, was really a per-call artifact rebuild — settled by a discriminating benchmark (artifact hoisted out of the timed loop vs rebuilt per call); rule out machine/GHC only once the setup is confirmed identical. Before a number enters a commit message or public doc, ask what *instrument* produced it and whether a cheaper decisive check (printed-AST churn location, a provably-unaffected control) settles the question first.
- **An A/B across two *builds* needs interleaving and controls, because recompilation itself moves numbers.** Two binaries differing by a one-line toggle shift *unaffected* benchmarks by ±2–5% (code-layout/codegen noise), and batched runs (all A, then all B) additionally confound with time/thermal drift. Run interleaved A/B pairs (drift cancels within a pair) and include per-pair controls: a suite the change provably cannot affect (e.g. the concrete `VTA` MNIST groups of `BenchMnistTools` for a `contractAst` change — the concrete pipeline never runs it), and/or a change-independent variant (e.g. `S-exec-raw`: `vjpArtifact` runs `simplifyUserCode` + `revProduceArtifactDt` but *not* `contractAst`, which runs in `simplifyArtifactRev` via `simplifyInlineContract` — so the raw artifact is identical across the toggle). The change's effect is the target's per-pair ratio minus the control's.
- **The printed-AST tests are a free, decisive oracle for "can this rewrite affect that program at all".** An unchanged printed artifact means a byte-identical artifact and hence identical interpretation, so checking *where* a rewrite's printed-AST churn falls, before benchmarking, can settle a claim in minutes — a purported MNIST speedup was disproved this way (the churn was confined to CNN tests, so FC-MNIST could not have moved).
- **Benchmark inputs must be random, not broadcast constants.** A constant input like `treplicate … (sscalar 7)` is a stride-0 broadcast that the simplifier constant-folds *through* the very operations you mean to time — a CNN gradient benchmark with a constant glyph lost its im2col gathers to folding and under-measured 24ms vs the honest 158ms. Use `randomValue`; a constant is only right when the *test* (e.g. a printed-AST test) wants a canonical small term.

Cost facts worth knowing before optimizing:

- **The two AD pipelines have different cost shapes.** `cgrad`/`cvjp` re-run differentiation on every call. The symbolic tools (`grad`/`vjp`) pay tracing + `simplifyUserCode` + AD + `simplifyArtifactRev` once — a roughly size-independent overhead — and then only interpret the artifact per call. The intended usage is therefore to build the artifact once (`vjpArtifact`/`gradArtifact`/`revArtifactAdapt`) and interpret it many times (`vjpInterpretArtifact`); a benchmark that calls full `vjp` per iteration conflates pipeline cost with execution cost.
- **`sreplicate`, `sreplicateN`, `stranspose` are metadata-only** (stride tricks; ox-arrays `X.replicate` is stretch-to-stride-0), and the ox-arrays dot and elementwise kernels (`Data.Array.Strided.Arith`) are stride-aware. Broadcasts and transposes fed into a dot or a `*` do **not** materialize, so don't rewrite them away on the assumption that they allocate.
- **`tssumN` is iterated `tssum`** (`Core/OpsConcrete.hs`): one full pass and allocation per summed dimension.
- **Interpreted `sgather` dominates gather-heavy programs** (e.g. the im2col patch arrays of convolution gradients — often ~two thirds of runtime). It runs through ox-arrays' `mgenerate`, which for each output position (the `shm` dims) evaluates the index and copies a slice (the `shn` dims); the per-element boxed-`Integer` index arithmetic is the hot loop. Two benchmark-confirmed consequences: (1) `contractAst` sorts a gather's slice (`shn`) dimensions ascending, via metadata-only compensating transposes, so the largest dimension is innermost and the copy's inner loop amortizes the per-step overhead — reordering the output (`shm`) dims, by contrast, changes nothing; (2) fusing two gathers into one is a *pessimization*, since it trades few-large-slice copies for many-tiny-slice copies while `mgenerate`'s cost is per-output-position, so the phase-gating that prevents that fusion is intentional. One level down, the per-step cost is orthotope's run-decomposition of each strided slice (`toVectorListT`), with a per-element fallback when the innermost dim is strided; reducing it further is an upstream (ox-arrays/orthotope) job, designed in the issue #123 material.
- **Concrete scatter is slice-based and ~8–10× cheaper than gather on the same index map and strided-read workload** (`scatter48` ~0.55ms vs `gather48` ~4–6ms). As gather's transpose it performs the same element transfers and, where the index map is many-to-one, even more arithmetic — it sums where gather copies — so the gap is code path, not data volume. The path: `tscatterZSScalar` does per-position index eval + `IntMap.insertWith (+)` with whole-slice adds through the stride-aware `NumElt` C kernels, then flat `VS.copy` write-outs; the interpreted Haskell is per *chunk*, all element traffic is C. The accumulation is what dodges the Haskell strided-normalize — it consumes strided views in C and leaves dense buffers to memcpy, a trick a sum-free gather can't borrow. Corollaries: extending the `shn`-sort to scatter cannot pay (each slice is copied as one flat vector; no per-`shn`-dim loop to amortize); scatter is the empirical bound for a fast gather path; and a rewrite's whole-program effect grows with problem size, converging toward the dominant op's win as it comes to dominate (the `shn`-sort is negligible on small overhead-bound nets, ~18% on a 24×24 CNN gradient once gathers dominate).
- **`vjpArtifact` does not run `contractAst`** — it runs `simplifyUserCode` + `revProduceArtifactDt`; `contractAst`'s only caller is `simplifyInlineContract`, which `simplifyArtifactRev` and its `Fwd` sibling apply to artifacts (convVjpBench's `H-exec-contracted` also calls it directly). Hence the *raw* artifact is contraction-independent, which both explains `S-exec-raw`'s role as an A/B control and means "artifact" benchmarks measure different pipelines depending on which of the two you call.

Adding a `contractAst` rewrite rule: put it in `contractAst`, not a smart constructor (which fires in every phase and reshapes intermediates other rules match on), applied at a node's exit and *after* any case that hoists structure out of the same constructor and re-enters `contractAst`. Make it idempotent, and identify which existing rules could undo the form it introduces — for the `shn`-sort, `astTransposeS`/`astGatherCase` only absorb *leading*-dims permutations while the compensating transposes permute trailing dims — recording that argument as a code comment at the rule.

## Coding style

Author-generic style conventions are collected in the portable-notes section at the end of this file; what follows is horde-ad-specific.

- `StrictData` is on, plus `TypeFamilies`, `PatternSynonyms`, etc. — see `common options` in the cabal file. Type-level shape arithmetic relies on the `ghc-typelits-knownnat` and `ghc-typelits-natnormalise` plugins.
- **Float epsilon margins depend on magnitude, GHC version and machine.** When compared values are large (e.g. gradients reaching ~5e5, where one Float ulp is ~0.03), widen the `assertEqualUpToEpsilon` margin rather than pinning exact low ulps or rewriting the expected values to one machine's output.

## Testing and correctness

- **Benchmarks are not correctness tests.** A body that forces a result by comparing it to itself (`allClose v v`) checks only that shapes line up (it compiles) — it never catches a wrong-operator or copy-paste bug, so when cloning a variant, cross-check every analogous position by hand: the operator called, the data helper used, and the point at which a derivative artifact is interpreted. Every benchmarked path needs a *separate* `assertEqualUpToEpsilon` check on same-shaped data — that is why deterministic correctness lives in `TestConvCorrect` alongside the poor man's benchmarks in `TestConvQuickCheck` — though existing tests of closely similar code suffice (the `cnn-*` benchmark groups lean on the many CNN tests rather than a dedicated check).
- **Deterministic vs QuickCheck split for stable timing.** Keep QuickCheck properties and poor man's benchmarks in one module (`TestConvQuickCheck`) and deterministic `testCase` correctness in another (`TestConvCorrect`), so the deterministic suite's wall-clock stays comparable across runs. Share helpers by *exporting* them from the QuickCheck module (no import cycle).
- **Printed-AST regression churn** after simplifier changes is expected and mechanical: refresh the expected strings from a sequential `CAFlessTest` run (parse the tasty-hunit expected/but-got pairs; expect two or three rounds, since each test stops at its first failing assertion), keep that churn in its own commit, and watch for eps-based numeric tests (e.g. `3barS`) drifting in the last Float digit when operation order changes.
- **`cnnObjective` (exported from `TestMnistPP`) is the objective shared between a printed-AST test and its benchmark**: `testCNNOPP2S` consumes it with a constant glyph at print-friendly sizes, `convVjpBench`'s `cnn-*` groups with a random glyph at square doubling sizes — the benchmark provably measures the net the test validates, and the refactor is verified free by the printed-AST test not churning.

## Portable notes: same author, same machine

Nothing in this section is horde-ad-specific: it should hold for other projects by the same author, written in the same coding style and developed on the same machine behind the same outer sandbox. Examples are from horde-ad unless attributed.

### Coding style

- Haddocks are expected on all module headers and on functions/types in "major"/interface modules. Minor internal helpers get no haddocks; if they are commented at all, the comments must not be haddocks and are permitted to describe implementation details and go out of date — so don't treat every comment as authoritative documentation.
- Prefer assertions over comments to document invariants, unless that would be too verbose.
- `-fno-ignore-asserts` is kept on in the common `options` stanza of the cabal file, so failed `assert`s crash release builds too, not just development ones — crash reports from released code can name assertions.
- Lens libraries are deliberately avoided; state lives in plain records (with record punning).
- GHC2024 is the default language; each project's default-extensions live in the cabal `common options` stanza. Projects normally set `StrictData` — assume it unless the project's notes say otherwise.
- Formatting (also spelled out in the README's Coding style section): 2-space indent, 80 columns, spaces not tabs, spurious whitespace avoided, spaces around arithmetic operators encouraged. Inline comments (`--`) are prefixed with exactly two spaces, unless indented to match other comments. Operators such as `(` and `,`, `<$>` and `<*>`, comment starts, etc. on consecutive lines either align or, if that would make lines too long, indent by 2 spaces from the previous indentation level. Generally, relax and stick to the style apparent in the file being edited.
- Put large, mechanical formatting changes in their own commit, separate from substantive changes.
- If hlint is still too naggy, adding more exceptions to `.hlint.yaml` is fine — don't contort code to appease it.
- **Uniformity across analogous positions is itself a review tool.** Parallel code (e.g. the `Same`/`Shrinking`/`Padded` × `dKrn`/`dInp` × size families in the conv tests) and its comments should be identical modulo names and shapes; diffing analogous positions is how bugs surface. When one drifts, normalize toward the cleaner form, not the first draft.
- **Comments.** State a non-tiny note that would differ only in test/benchmark names once, at the canonical occurrence, instead of repeating it; present identical tiny notes uniformly at every analogous position. Match the codebase's spelling and hyphenation (e.g. "poor man's", not "poor-man's") and keep terminal punctuation consistent across parallel clauses (don't end one with ";" and its sibling with "."). A comment must still match the code after refactors — watch for notes invalidated by later changes. Leave pre-existing comments alone unless asked — flag them instead.
- In tests, an expected crash may never fire due to laziness: an assertion or lookup error is swallowed if the offending value is never forced (force it — under `StrictData`, WHNF fully builds an AST). Catch real assert failures with `Control.Exception.try`, rather than pattern-matching on output; the `blame`/`swith` details (from the `assert-failure` package) go to the trace output, not into the exception.
- **Prove a self-checking assertion is non-vacuous.** An invariant check — e.g. verifying that scatter is the adjoint of gather via `sdot0 (sgather x f) y == sdot0 x (sscatter y f)` — should be shown to actually fail when the property is deliberately broken, or it may be passing vacuously.
- Share the objective between a test and its benchmark via one exported helper, parameterized by what differs, so the benchmark provably measures what the test validates — share code, not configuration.

### Working style

- **Scope discipline.** On an ambiguous request ("the *new* tests") take the narrower reading, do it, and flag the boundary with an offer to expand — don't silently touch pre-existing code. Split unrelated work into separate PRs (e.g. convolution benchmarks + tests in one PR, the simplifier fix in another).
- **Verify before claiming done.** "Uniform" / "correct" / "passes" must rest on an actual line-by-line cross-check or a test run, not on the fact that it compiled; audit old code in touched files too.
- **Only/every/never claims must rest on repo-wide grep, not on the file where the pattern was first noticed** — analogous-variant families (`Same`/`Shrinking`/`Padded` × `dKrn`/`dInp`, the ranked/shaped/mixed op surfaces, the `Ops*` instances) make single-file generalization treacherous. The same discipline applies before concluding "this cannot happen here": grep for *every* site that could do it.
- **Commits should be clean and logical, not a diary of the work.** File-partition them, order them so exports precede uses, and fold a follow-up refactor into the commit where the code is logically born rather than adding "add then move" churn.
- **Never push, or open/force-update a PR, without an explicit go-ahead.** Permission to make a change is not permission to publish it.
- **Record don't-do rulings next to the do's.** Refuted designs live in the working documents together with the evidence that killed them, precisely so they aren't re-proposed later; when a new idea dies to evidence, write the ruling down where the next reader will look. (E.g. gather fusion, the `shm` flip and the summation-structure rewrite, each recorded with its killing measurement in the issue #123 material.)
- **Drafting GitHub-bound texts**: one file per destination (issue, its design comment, PR description, upstream PR), staged in the repo root until posted; keep the *design* implementation-ignorant and put measured results in the PR description; deliberate overlap between files is fine to make each self-contained. Don't attribute design intent to code that is merely generic ("assumes irregular indexing") — state observed granularity and cost, not motives. Prefer reference-style markdown links so prose stays within 80 columns.
- **Links that cite source code — in GitHub-bound texts and the reference documents — must be GitHub permalinks pinned to a commit hash that is on `master`** (`…blob/<commit>/….hs#L12-L34`): branch-name and unpinned links drift or die when branches move, while a master hash survives rebases and stays verifiable — the citation checker validates such permalinks against the pinned commit. Deliberately-living whole-file links (e.g. the README's `blob/master` pointers, meant to show the current file) are outside the rule, as are links to foreign repos, which the checker cannot verify.
- **State mathematical properties in the code's surface notation, not abstract math** (in docs and comments alike). Write the gather/scatter adjoint law as `sdot0 (sgather x f) y == sdot0 x (sscatter y f)`, not `⟨gather x, y⟩ = ⟨x, scatter y⟩`: keep the index function `f` explicit rather than hidden in the operator name, and put quantifiers first (*for all `f`, `x`, `y`*). It reads in the vocabulary of the code and keeps the shapes checkable.

### Document verification: the three-pass discipline

Planning/reference documents (this file and any GitHub-bound drafts staged in the repo root) make checkable claims. Whenever such a document (or code it cites) is edited, run three passes:

1. `python3 tools/check-plan-citations.py [DOC]` (run from the repo root) — mechanically re-validates `file:line` citations, resolving each, checking the line range and printing the first cited line to eyeball against the surrounding claim, and pinned GitHub permalinks against the commit they name, via `git show`, so those never drift; foreign-repo links can't be verified locally. DOC defaults to this file.
2. Check that paths, cabal targets and flags named in prose exist.
3. Re-verify only/every/never claims by repo-wide grep.

The passes are ordered by yield: the mechanical ones catch drift, but the quantified-claims grep has found real, long-standing errors every time it has been run, so it is the pass never to skip.

### Sandboxing on the dev machine (outer wrapper + inner sandbox)

Claude Code sessions on Mikolaj's machine run inside an outer bwrap sandbox wrapper (PID 1 is `bwrap`), beyond Claude Code's own (inner) sandbox. Current state and its implications:

- Git and cabal in sessions: run `git` writes, `cabal` and `gpg` unsandboxed — the inner sandbox mounts `.git/config`, `~/.cabal` and `~/.gnupg` read-only. `git checkout -b` / `branch -f` fail to lock the config, though the ref often moves anyway — verify refs afterwards. GPG signing (`commit.gpgsign` is on) fails inside the sandbox and works fine unsandboxed, so never fall back to `--no-gpg-sign`. Likewise SSH keys aren't reachable from the inner sandbox, blocking sandboxed pushes. Other read-only HOME mounts (e.g. `~/.claude/projects`) similarly need unsandboxed commands for deletions.
- Paths the wrapper blocks report "No such file or directory", not "Permission denied". If a path outside the repo seems missing — especially one documented as expected, like the `../ox-arrays` sibling checkout — suspect the wrapper and ask, rather than record the path as absent. `dangerouslyDisableSandbox` bypasses only the inner sandbox, never the wrapper.
- The wrapper whitelists specific HOME entries (as of 2026-07-13: `.cabal`, `.cache`, `.claude`, `.config`, `.ghcup`, `.gitconfig`, `.gnupg`, `.local`, `.npm`, `.ssh`, `r`).
- Inside the inner sandbox, HOME appears to be the repo root, so sandboxed `git status`/`ls` show phantom untracked dotfiles (`.bashrc`, `.gitconfig`, `.vscode`, ...) that don't exist on the real filesystem. Ignore them; verify with an unsandboxed command before deleting any.
- System state under wrapper-hidden paths (e.g. `/etc/apparmor.d`) cannot be inspected from inside a session; such diagnosis must be done by Mikolaj in a plain terminal.
- The nested inner sandbox works only because three things hold: the Ubuntu AppArmor userns restriction is off (`kernel.apparmor_restrict_unprivileged_userns=0`, no `bwrap-userns-restrict` profile), the wrapper mounts the repo read-write, and `enableWeakerNestedSandbox: true` is in effect — inherited from the `sandbox` block of the user-level `~/.claude/settings.json` (a project `sandbox` block wholesale replaces the user-level one — settings objects don't deep-merge — so a project that defines one must repeat the flag). If sandboxed commands start failing at startup, check these three first.

### Git and tooling in sessions

- Interactive git is unavailable (`rebase -i`, `add -i`). Rewrite history with `git reset --mixed <base>` + re-`add`/`commit` per file group, reusing messages via `git commit -C <hash>` / `-F <file>`.
- Amending a non-HEAD commit (no `rebase -i`): save working-tree edits as a patch, `git reset --hard <target>` (spares untracked files), apply, `--amend`, then `git cherry-pick` the successors (conflict-free when they don't touch the amended files); update recorded hashes.
- The repo root accumulates many untracked scratch files (`log*`, `*.prof`, `cabal.project.local.bkp*`, `.emacs.desktop*`, etc.); leave them alone and never `git add` them wholesale.
- `awk` is not on PATH — use `python3` or `grep`.
- To combine several tasty `-p` patterns, tasty wants awk-style syntax: `-p "/foo/ || /bar/"`.
- GHC emits warnings only on *recompilation*: a cached, up-to-date build can hide warnings (e.g. `-Wredundant-constraints`) that a full rebuild would surface — don't infer "no warnings" from a clean second build.
- Keep one set of cabal flags across a session — changing flags (e.g. toggling `--enable-optimization` or `--enable-profiling`) forces a full rebuild of the local packages, though each flag set's dependency builds stay cached in the store. Pass such flags on the command line rather than editing `cabal.project.local`.
- The `/tmp` scratchpad is wiped by a machine restart — put anything that must survive (patches, notes) in the repo tree; binaries just get rebuilt.
- Exact dependency sources are always available: unpack `~/.cabal/packages/hackage.haskell.org/<pkg>/<ver>/` matching `dist-newstyle/cache/plan.json`.
- `.github/workflows/haskell-ci.yml` is generated by `haskell-ci` from the `.cabal` file — regenerate it rather than hand-editing, and re-apply any hand-maintained steps afterwards (the `tests` and `benchmarks` steps, marked by a comment in the workflow).
- Toggle-based A/B builds: make a rule's guard unsatisfiable (e.g. `sigmaL /= sigmaL`), build and copy the binary aside, restore + rebuild + copy again, then run the two preserved binaries in interleaved pairs (no rebuild between A and B); an edited `Core` module rebuilds in ~10 min.
