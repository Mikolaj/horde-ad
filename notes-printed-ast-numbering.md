# Make printed ASTs build-independent

*A self-contained pull-request description: problem, requirements, success criteria, evidence, design, implementation and follow-ups in one file, with no companion issue. Labels are prefixed so they never collide — **R** requirements, **V** success criteria, **E** findings, **I** implementation items, **C** commits.*

> **This is a work in progress, and stays one until the PR merges.** It has four states; the status column in Success criteria is what says which one it is in, so read that before trusting any tense elsewhere.
>
> 1. **Now — nothing is implemented.** Evidence, design and risk analysis are complete and measured. I1-I6 and C1-C10 describe what the commits *will* contain, and every V reads `not yet run`.
> 2. **While the implementation starts and progresses.** Items, criteria and findings are updated as the code lands and teaches us things — a design corrected to match the code is worth more than one defended against it, so edit this text rather than argue with it, and re-derive C1-C10 from the body rather than patching them, which is how they drifted before.
> 3. **At the PR.** Once the criteria are met well enough — Future work records which misses are acceptable and why — create the PR and paste this text as its description. Three things first. **(a)** Run `check-plan-citations.py`, `check-doc-refs.py` and `check-doc-examples.py` one final time: it is the last moment they can see this text at all, and 81 `file:line` citations ride on them. **(b)** Delete this banner and put state 4's rule in its place as a single line — *"This description is the single live copy: corrections, rebases and re-measurements land here, and nowhere else, until merge."* — because states 1-3 become history the moment you paste, and a reviewer should not meet four states describing a file that no longer exists. **(c)** Leave the prose unwrapped, one long line per paragraph, since GitHub renders single newlines as hard breaks in a PR body; keep tables, code fences and list items each on their own line, which is what they need to render.
> 4. **Under review.** At paste the PR body becomes the single live copy and **this file is deleted**, so corrections, rebases and re-measurements land there and nowhere else until merge. One copy cannot drift from another, which is the failure mode this document has already suffered once — an earlier commit list fell out of step with the body across three design changes, scheduling work that had been deleted and omitting work that had been added. The price, accepted deliberately, is that the description leaves version control and loses the three checkers, which only ever run against a file; hence step (a) above.

## Summary

Printed AST variable names are numbered straight from a global counter, so a test's expected string depends on how GHC happened to compile that test module. The tree is **already wrong on GHC 9.10.3**, one of the three compilers CI builds with, and escapes notice only because CI never runs the affected tests. This PR renumbers variables **at print time** — densely, in order of first appearance — so a printed term is a function of the term alone; deletes the counter resets that canonical printing makes unnecessary and that make parallel printed-AST tests corrupt rather than merely wrong; regenerates the 392 expected strings; and takes the two payoffs that follow, un-narrowing CI to all three compilers and running `minimalTest` in parallel.

## Problem

Printed AST variable names encode which of a global counter's values happened to reach which variable — a property of how GHC compiled the test module rather than of the program's meaning. 392 expected strings are pinned to those numbers, so any build that allocates ids differently is wrong against them. **Canonicalize the names at print time**, making what is printed a function of the printed term alone.

The tree is wrong *today*, not hypothetically: three printed-AST tests fail on GHC 9.10.3 at `-O1`, one of the three compilers CI builds with, and nobody has noticed because the generated workflow runs `-p "detSquare"` and never reaches them (E6). The `-O0` divergences are what un-narrowing CI would expose next, not the reason to act.

`Core/AstFreshId.hs:35-48` hands out AST variable ids from one global `unsafePerformIO` atomic counter, and `Core/PPTools.hs:60-66` renders a variable as `prefix ++ show (rawId - 100000000)` — the prefix from the tensor rank, the digits straight from the counter. A printed name therefore encodes *which* of the counter's values reached which variable — the Problem's premise, with the mechanism under it. The counter never skips — `add` returns the old value and adds exactly 1 — so what changes across builds is not the sequence but its allocation: a term typically shows only ~43% of the ids issued across its own range (246 of 351 literals with variables have gaps, median span/count 2.3), the rest going to intermediates that did not survive, and a pass such as `simplifyArtifactRev` re-mints some variables while retaining others.

Numbering is **per test**, not cumulative: every test in the module opens with `resetVarCounter`, so drift cannot propagate between tests and a divergence can only arise inside one, after its own reset. Nothing static separates the four `-O0` failures from their siblings — `testCNNOPP2b`, `testCNNOPP6b` and `testCNNOPP7b` use the same helpers as the failing `testCNNOPP5b`, and it is not size either, since `testCNNOPP4b` is the module's largest construction (50 distinct variables, highest id 314) and passes while `testCNNOPP5b` (12 distinct, highest 61) fails. At `-O0`, `sminimizedCNNOPP2`, `sminimizedCNNOPP3b`, `sminimizedCNNOPP5b` and `minimizedCNNOPP4bU` fail (all in `test/simplified/TestGatherSimplified.hs`, bodies at 1300/1376/1486/1616); what they have in common turns out to be a compiler transformation, not a property of the tests, and the findings below identify which.

Four axes, of which R1 covers two. Optimization level is one and is live; **GHC version is another, and it already bites** (E6). Core count is a third and is **latent**, not live: while the suites are sequenced it changes nothing (measured), and it becomes live the moment they are not — which I5 makes them, so R3 is what keeps it covered. CAFs and test order are a fourth in principle — `TestAdaptorSimplified.hs:655-656` defines `artifact` at top level and `testGradFooLetMatrixPP` (`:658-661`) resets the counter before printing it, which does nothing unless that test is the first to force the CAF — but running each failing test alone reproduces its in-suite output byte for byte, so nothing in the current tree exercises it.

392 expected strings across six modules in `test/simplified/` are pinned to those numbers (387 printed-AST plus 5 `show deltas`; 7361 variable tokens; there are no `@?= "…"` assertions anywhere else in `test/`, `bench/`, `example/` or `src/`). `README.md:151-161` quotes one, pinned in turn by `TestAdaptorSimplified.hs:662` — a correspondence `tools/check-doc-examples.py` checks, green today, as are `check-plan-citations.py` and `check-doc-refs.py`.

**What is and is not already covered.** The hand-written workflow (`.github/workflows/lint-and-test-suites.yml`, its Tests step) runs `cabal test minimalTest --enable-optimization` with *no* `-p`, so all 75 live tests in that module — the four `-O0` failures included — already run on GitHub runners today. The expectations therefore already survive a different machine, core count, orthotope checkout and FP flags: machine-invariance is demonstrated, not at risk. Two axes are never exercised, and R1 covers both. **Optimization level** is one, and it is exactly what the generated workflow has to suppress: `.github/haskell-ci.patch` narrows its unoptimized step to `minimalTest --test-options='-p "detSquare"'`. **GHC version** is the other, for these tests: that workflow builds all three compilers, but the same narrowing means 9.10.3 and 9.14.1 never reach a printed-AST test, while the hand-written one is 9.12.4 only. That is why the tree can be wrong on 9.10.3 today without any run going red — the gap I6 closes, and what V2 checks.

## Requirements and scope

What must be true when this lands. Every requirement is claimed by at least one success criterion below.

- **R1 — build-independence.** A term's printed form is identical across optimization levels and across the three GHC versions CI builds with.
- **R2 — position-independence.** It does not depend on where a test sits in its file, on what ran before it, or on which test forced a top-level CAF first — the one case `resetVarCounter` cannot cover.
- **R3 — order-independence.** It does not depend on interleaving, so the printed-AST suites can run in parallel and stay deterministic.
- **R4 — renaming only.** Nothing renumbers terms or changes structure: the ids are load-bearing where they are, and canonicalization normalizes names, never sharing.
- **R5 — no coverage lost.** Every assertion the tree makes today still holds — the 387 printed-AST strings, the `length (show …)` character-count pins, the 5 `show deltas`, and every value assertion.

Two payoffs follow from R1-R3 rather than motivating them, and both are taken here: CI drops its `-p "detSquare"` narrowing, putting ~72 further tests on three GHC versions unoptimized (I6); and `minimalTest` goes parallel (I5), where the wall-clock is worth reclaiming.

### Out of scope

- The AST's derived `Show` (raw ids — which is what the 42 `length (show …)` assertions want: they measure width, not value).
- Any change to how ids are allocated: the counter, its `unsafePerformIO` and its `NOINLINE`s stay exactly as they are. (Its *thread-safety* is not out of scope but is not a change either — `add` is already an atomic fetch-and-add; what was unsafe was the absolute `set` in the resets.)
- Removing `inOrderTestGroup` from `CAFlessTest`: its correctness rationale dissolves, but the suite doubles as a sequential benchmark, so the wrapper stays and the rationale is rewritten rather than deleted. Only `minimalTest` goes parallel.
- `testOverleafPP` (`TestAdaptorSimplified.hs:596`/`:602`) becomes two identical literals under any canonical scheme — the two terms really are alpha-equivalent, printed in different reset scopes. Label it rather than pretend it still discriminates.

## Success criteria

Each names the requirement it discharges. **None has been run yet** — the status table below is the document's state marker: it fills in as the implementation progresses, and "met well enough" against it, with the accepted misses in Future work, is what triggers state 3 above.

**Make the property a test, not a CI side effect (R2).** Add one test in `TestGatherSimplified` with `PP` in its name (so it runs at `-O0` on all three GHC versions once I6 lands) that builds the same term twice at two different `setVarCounter` offsets and asserts the two printed strings are equal. Prove it non-vacuous by watching it fail against the raw printer, and make the two offsets differ by something other than a constant shift of the whole term.

**Prove the parallelism claim before relying on it (R3).** Capture one failing parallel run *first*, on the tree as it stands, so the before/after is evidence rather than a claim: `test/MinimalTest.hs:27` with `inOrderTestGroup` swapped for `testGroup`, at tasty's default `NumThreads` (16 here). Then after I5, run it repeatedly and confirm it is green and the printed strings are stable across repeats. Both runs go in the commit message.

Then the success criteria, each naming the requirement it discharges. Every one of R1-R5 is claimed by at least one, and the work is not done until all nine pass:

- **V1 (R1).** Repeat the unfiltered `-O0` run: it must pass against expectations recorded only from `-O1`. That is the discriminating check.
- **V2 (R1).** Every printed-AST test passes at `-O1` on 9.10.3 and 9.14.1 as well as 9.12.4 — the three failures E6 records are gone. Unlike the rest of these criteria this one is permanent rather than one-shot: I6 puts the whole of `CAFlessTest`, optimized, on all three compilers in the hand-written workflow, so R1's version half stays guarded after merge instead of being verified once by hand. That also settles a scope question rather than leaving it: E6's measurement is `minimalTest`-only, so whether the other five printed-AST modules also fail on 9.10.3 has never been established — after merge, CI answers it on every push, at corpus scale, which is why it is not worth establishing by hand first.
- **V3 (R2).** The position-independence test above is green, and has been watched failing against the raw printer.
- **V4 (R3).** Parallel `minimalTest` is green in three repeats at tasty's default `NumThreads`, printed strings byte-identical across them.
- **V5 (R4).** The one-shot skeleton-equality gate passes and its residue is *exactly* the three alpha-equivalence pairs C4 collapses — anything else is a term regression baked in alongside the renumbering, which is the one thing the regenerated suite cannot notice about itself.
- **V6 (R5).** `cabal build`; `cabal test minimalTest --enable-optimization`; `cabal test CAFlessTest --enable-optimization` (never `parallelTest`); redirect to a file and echo `$?` rather than piping.
- **V7.** `CAFlessTest`'s wall clock is unchanged within noise against the pre-change baseline measured on the current tree: **141.10s, 141.46s and 141.55s** over three sequential optimized runs of all 672 tests. The printer now renders twice and is no longer streaming, and that suite doubles as a sequential benchmark; `printAstPrettyButNested` is the one to watch (Risks, and what bounds them).
- **V8.** `hlint .` back to `No hints`; `stylish-haskell -i` leaves every touched file unchanged; `tools/check-doc-examples.py README.md`, plus the citation and reference checkers on every edited `.md`.
- **V9.** After pushing: two CI runs per push, via `curl -s "https://api.github.com/repos/Mikolaj/horde-ad/actions/runs?branch=BRANCH&per_page=5"`.

| criterion | discharges | status |
|---|---|---|
| V1 | R1 | not yet run |
| V2 | R1 | not yet run |
| V3 | R2 | not yet run |
| V4 | R3 | not yet run |
| V5 | R4 | not yet run |
| V6 | R5 | not yet run |
| V7 | — | not yet run |
| V8 | — | not yet run |
| V9 | — | not yet run |

## Experiments and findings

Measured on 2026-07-31, GHC 9.12.4, by building `minimalTest` twice into separate build directories (`dist-newstyle` optimized, `dist-O0` with `--disable-optimization`) and running the two binaries directly with `-p '/PP/'`, which is 26 tests and 0.3–0.5s per run. Values below are the `expected:`/`but got:` pairs tasty prints for the first failing assertion of each failing test.

*A method note that cost a round.* Rewriting the module's 166 assertion call sites to dump values instead of comparing them — so that one run would enumerate every divergence rather than one per test, `@?=` throwing past the rest of each `do` block — **changed the numbering it was meant to observe**: the instrumented pair of builds showed one divergent test where the unpatched pair shows four. The instrument perturbs exactly the quantity under study, because that quantity is how GHC compiled this module. All figures below come from unpatched builds.

### E1. What diverges

`-O1`: 26/26 pass. `-O0`: exactly the four documented tests fail. Each divergence is *skeleton-equal* (byte-identical once variable tokens are blanked), a bijection on ids, and order-preserving:

| test | id map | shifts |
|---|---|---|
| `sminimizedCNNOPP2` | `{19:20, 24:25, 27:28}` | 0, +1 |
| `sminimizedCNNOPP3b` | `{200:252, 270:274}` | 0, +4, +52 |
| `sminimizedCNNOPP5b` | `{61:66}` | 0, +5 |
| `minimizedCNNOPP4bU` | `{126:130, 127:131, 129:133}` | 0, +4 |

Two of these shift by 4; one shifts by two different amounts within a single assertion. So the divergence is several independent extra-mint events, and `.github/haskell-ci.patch:37`'s "the numbering lands four higher" describes one case rather than the phenomenon.

Widening from `minimalTest` to the whole printed-AST corpus — `CAFlessTest` `-p '/PP/'`, i.e. all six modules — **183 tests, 8 diverge at `-O0`**: the four above, plus `minimizedCNNOPP1e` (`TestConvSimplified`, shifts −7), `4S0rmapAccumRD01SN531b0PP` (`TestRevFwdFold`, a uniform +3), and `minimizedCNNOPP4bW` and `minimizedCNNOPP5bW` (`TestConvSimplified`, +3 each). All eight are skeleton-equal and order-preserving, verified by blanking the variable tokens on both sides. The `mapAccum` one matters because it is the case that exercises `printAstHFun`'s `"<lambda>"` elision. Note also that shifts run in both directions: `-O0` is not uniformly "higher".

### E2. The fix, validated before being written

Applying the proposed canonicalization to the collected `expected`/`got` pairs — every one E1, E3 and E6 record — **all of them fixed**: every pair becomes byte-identical, under first-occurrence *and* under ascending-id numbering alike. No configuration produced a structural difference, so the choice between the two schemes rests on the A/B-collapse argument in Design, not on robustness.

The regeneration itself was also dry-run offline over all 392 literals, which is the PR's largest mechanical risk and costs nothing to check in advance:

| property | result |
|---|---|
| idempotent (`canon (canon x) == canon x`) | 392 / 392 |
| literals where two distinct ids map to one number | **0** |
| distinct literals colliding after canonicalization | 6 (the known A/B pairs) |
| largest canonical number produced | 76, against 517 today |

So the rewrite is a fixpoint and never conflates two variables. Repeating it over the 191 *actual* printed outputs collected during the investigation, rather than the source literals, gives idempotent 191/191 and injective 191/191 as well.

One number the resets' removal depends on: in a reset-free run of 71 tests the highest printed offset reached **13,229**, i.e. raw id ~100,013,229, against the 9-digit ceiling at offset 899,999,999 — **68,000× headroom**. Scaling to `CAFlessTest`'s 672 tests and allowing generously for ids minted but never printed still leaves several orders of magnitude. That is what the 42 `length (show …) @?= N` assertions rest on, since they pin character counts and every id keeps its width.

### Reproducing any of these configurations

All of them are one build plus a sub-second run, and all were done by invoking the test binary directly rather than through `cabal test`:

| configuration | how |
|---|---|
| unoptimized | `cabal build minimalTest --disable-optimization --builddir=dist-O0` |
| CSE off, `-O1` | add `{-# OPTIONS_GHC -fno-cse #-}` to the test module |
| full laziness off | `{-# OPTIONS_GHC -fno-full-laziness #-}` likewise |
| test module `-O0`, library `-O1` | `{-# OPTIONS_GHC -O0 #-}` in the test module |
| library `-O0`, test module `-O1` | `{-# OPTIONS_GHC -O1 #-}` in the module, built into `dist-O0` |
| another compiler | `cabal build minimalTest --enable-optimization -w ghc-9.10.3 -j1` |
| position-independence | delete the 37 `resetVarCounter` lines, then compare `-p` subsets |
| parallel | `inOrderTestGroup` → `testGroup` in `test/MinimalTest.hs`, then `--num-threads=N` |

The complementary `-O0` pair is what isolates cause: the test module alone reproduces three divergences, the library alone reproduces the fourth.

**Step 0 is done — see Evidence.** The design assumed the `-O0` term is alpha-equivalent to the `-O1` one; that is now measured, across every divergence E1, E3 and E6 record, all skeleton-equal and all repaired by the proposed canonicalization. No structural difference appeared anywhere, so the gating condition is discharged and no re-plan is needed. Reproduce it with:

    cabal build minimalTest --disable-optimization --builddir=dist-O0
    dist-O0/build/*/ghc-*/horde-ad-*/t/minimalTest/noopt/build/minimalTest/minimalTest -p '/PP/'

Run the two binaries directly rather than through `cabal test` — the PP subset takes under half a second, so iteration is free once built. Four cautions, each learned the hard way here:

- never run an optimized and an unoptimized suite concurrently; two builds plus two test binaries OOM'd this machine and took a browser with them;
- do not instrument the assertions to dump values instead of comparing them — that edit changes how GHC compiles the module and so changes the very numbering under observation (Evidence, method note);
- **check `cabal build --dry-run` before measuring any binary you did not just build.** A binary in `dist-newstyle` silently outlived a source restore here and produced a full, plausible, wrong table before the dry-run's "file … changed" caught it — exactly the hazard `CLAUDE.md` records;
- if you contain a run with `ulimit`, run the control under the same limit. An apparent OOM here was the limit, not the change, and only the control showed it.

Delete `dist-O0` when finished, since a stray `dist-*` turns `hlint .` from `No hints` into dozens.

### E3. Which transformation moves the counter

| configuration | diverging tests | note |
|---|---|---|
| `-O0` throughout | 4 | baseline |
| `-O1`, `-fno-cse` on the test module | 3 | *identical maps* to `-O0` |
| `-O1`, `-fno-full-laziness` | 0 | not implicated |
| test module `-O0`, library `-O1` | 3 | same three, same maps |
| library `-O0`, test module `-O1` | 4 | `sminimizedCNNOPP2` matches `-O0` exactly; the other three shift *negatively* (−38, −48, −1) |

Three of the four are CSE inside the test module: compiling it with `-fno-cse` at `-O1` reproduces them exactly, with identical id maps. The flag appears in this document only as an instrument — added to a module for one build to isolate a cause, and removed again. No module in the tree carries it, so nothing here depends on one. The fourth originates in the library's optimization, isolated by the complementary build.

### E4. What does *not* move it

Each failing test run alone gives byte-identical output to the same test run inside the PP subset and inside the full suite, at both optimization levels — so test order and CAF forcing are not implicated. Three repeat runs are identical. `--num-threads` 1, 2, 4 and 16 all pass at `-O1`: core count is a latent axis, not a live one, while the suites are sequenced.

### E5. Parallel runs today: corruption, not renaming

Replacing `inOrderTestGroup` with `testGroup` in `test/MinimalTest.hs`, at `-O1`, PP subset, measured on the current tree — this is V4's "before", captured first as V4 asks rather than reconstructed later:

| threads | 1 | 2 | 4 | 8 | 16 | 16 (repeats) |
|---|---|---|---|---|---|---|
| failures of 26 | 0 | 11 | 15 | 15 | 13 | 13, 17, 13 |

The counts move between runs, as a non-deterministic failure should — the three repeats at sixteen threads give 13, 17 and 13. What does not move is the shape: green at one thread, failing from two upwards, never twice the same at sixteen.

And the failures are not misnumbering. They include `astGatherKnobsS: gather vars in v0` (`AstSimplify.hs:3228` — the assertion whose comment at `:3215-3218` names `resetVarCounter` as precisely what breaks its freshness assumption), `substitute1Ast: kind of the variable AstVarId 100000003: FTKScalar, payload kind: FTKR [3,3,3,3]` (`AstSimplify.hs:5545` — variable capture, the no-shadowing invariant at `:5468-5471` violated), `varInAst`'s binder assertions at `AstTools.hs:178` and `:230`, and one silently structurally different term (`gatherTransposeBuild33PP`). This settles a design question: canonical printing alone would leave parallel runs broken, and dropping the resets (I5) is the load-bearing change.

### E6. GHC version *is* a live axis, and the tree is already broken on 9.10.3

**GHC 9.14.1** at `-O1`: all 26 PP tests pass with the expectations recorded on 9.12.4. **GHC 9.10.3** at `-O1`: **3 of 26 fail** — `minimizedCNNOPP4bU`, `sminimizedCNNOPP3b`, `sminimizedCNNOPP5b` — all order-preserving relabellings, all repaired by canonicalization.

Their id maps are *identical* to the ones `-fno-cse` produces on 9.12.4 (`{126:130,127:131,129:133}`, `{200:252,270:274}`, `{61:66}`). The reading is that 9.10.3 simply does not perform the CSE that 9.12.4 does, so it yields the CSE-off numbering — which also explains why exactly the same three tests are involved as in the `-fno-cse` and module-`-O0` configurations.

The consequence is sharper than the `-O0` story. `ghc-9.10.3` is one of the three compilers the generated workflow (`.github/workflows/haskell-ci.yml`) builds with, so the expectations in the tree are **already wrong on a compiler CI uses**; nobody has noticed only because that workflow runs `-p "detSquare"` and never executes these tests. This is R1's live case and the Problem's reason to act: this PR does not rest on `-O0` at all.

Widening from the printed-AST subset to all 72 non-`detSquare` tests at `-O1` bounds what the version axis disturbs: **9.14.1 passes all 72; 9.12.4 passes all 72; 9.10.3 fails exactly 3, all of them printed-AST.** No value assertion and none of the 42 `length (show …) @?= N` assertions moves on any compiler — which also confirms that ids keep their 9-digit width everywhere, the property those assertions actually depend on. The version axis therefore perturbs variable numbering and nothing else.

### E7. What un-narrowing CI actually costs

Measured on the `-O0` binary, which is what the generated workflow builds. `-p "detSquare"` does not save time — it *selects* the expensive tests: `detSquare3` alone runs 34.1s at `-O0`, while everything the filter currently discards runs in 4.5–9.9s depending on capabilities. Peak RSS is unaffected by the change, being set by `-with-rtsopts=-A1G` (from the cabal `exe-options` stanza) times the capability count, which tasty raises to `getNumProcessors`:

| `--num-threads` | 1 | 2 | 4 | 16 |
|---|---|---|---|---|
| wall (non-`detSquare` tests) | 4.48s | 4.96s | 5.89s | 9.92s |
| peak RSS | 1.20 GB | 2.31 GB | 4.50 GB | 13.75 GB |

So un-narrowing adds seconds to a step already spending tens of seconds on the tests it keeps, and adds no memory. The 13.75 GB figure is the nursery on a 16-core machine, not a property of the tests — worth knowing before reading a local peak-RSS number as a CI risk.

### E8. Numbering is independent of a test's position in the file

R2, measured. `resetVarCounter` supplies it today only partly — it cannot re-mint variables a CAF has already built, so a test printing a top-level artifact such as `TestAdaptorSimplified.hs:655-656`'s `artifact` inherits numbers fixed by whichever test forced that CAF first.

Measured by deleting all 37 resets from `TestGatherSimplified` and running the same tests with different work preceding them — alone, within `-p '/CNNOPP/'`, and within `-p '/PP/'`. Raw numbering is position-dependent exactly as expected: alone the suite is green, the CNNOPP subset fails 12 tests, the PP subset 15. On the 12 tests failing in both subsets:

| across the two contexts | identical |
|---|---|
| raw numbering | 0 / 12 |
| canonicalized, first occurrence | **12 / 12** |
| canonicalized, ascending id | **12 / 12** |

Extending to three-way agreement — alone (where the printed value equals the source expectation) against both subsets — gives **12/12 under both schemes**. So canonical printing supplies the property outright, and supplies it more completely than the resets do, since it is immune to the CAF case they miss. That is what licenses I5 to delete `resetVarCounter` rather than merely redefine it.

### E9. Parallel execution: the resets are the whole cause, and canonical printing makes it deterministic

Attribution, with the resets deleted, `setTotalSharing` left intact, and `minimalTest` switched to `testGroup` at 16 threads:

- **Zero exceptions**, in three repeats. Every corruption signature from the earlier measurement — `astGatherKnobsS`, the `substitute1Ast` kind mismatch, the `varInAst` binder assertions — was caused by `resetVarCounter` alone.
- 44 failures across the three repeats, **0 structural**: all pure relabellings.
- Of the 14 tests failing in all three repeats, raw output agrees in **0/14** (interleaving genuinely scrambles ids) but canonicalized output agrees in **14/14**, under both schemes. So canonical printing makes parallel runs deterministic.

`setTotalSharing` (`AstTools.hs:271-278`) is a second global whose own comment warns it "affects all simplification and inlining taking place in parallel in the program at the time it's changed", and it is *not* unused: `rev'` (`CrossTesting.hs:84-89`) toggles it around every call, and there are 50 such call sites in `TestGatherSimplified` alone. It nevertheless does not block the parallel switch, measured: running all 71 non-`detSquare` tests in parallel, three times, every single failure is a printed-AST test (15/15 each time) and no `rev'`-based test fails. The reason is principled — the flag changes how much the simplifier *shares*, which moves term structure and performance but not values, and `rev'` compares numeric gradients. It can only bite where a *printed* term is produced under a toggled flag, which is exactly one test, `TestConvSimplified.testCNNOPP4bD` (`:2038-2043`), and that lives in `CAFlessTest`, which stays sequential.

**Demonstrated rather than inferred.** Adding `setTotalSharing True` to `testCNNOPP2` and rebuilding changes its printed term *structurally* — a binding appears that is otherwise absent:

    off:  … (str (sgather1 @2 (stranspose @[2, 3, 0, 1] …
    on:   … (str (let v55 = sconcrete (sfromListLinear [2] [1,0]) in sgather1 @2 …

Blanking every variable token leaves the two still different, so this is the one perturbation in the whole investigation that canonical numbering provably cannot absorb. That is the flag working as designed, not a defect: comparing *interpretations* across settings is the correct use, and it is what the tree does — `assertEqualUpToEpsilon1` binds `rev'`'s two AST fields as `_astVectSimp`/`_astSimp` and ignores them, comparing only values, which sharing cannot change. The exposure is confined to concurrency leaking a global setting into another test's term. Worth recording as a hazard and a follow-up (threading it through `SimplifyKnobs`, `AstSimplify.hs:151`, would also delete an `unsafePerformIO` read from `astIsSmall`, which is on the simplifier's hot path); not worth blocking this PR on.

### E10. The two non-printing assertion families are already covered

Both families the design reasons about turn out to sit *inside* `PP`-named tests, so the `-O0` printed-AST run exercised them: all 42 `length (show …) @?= N` assertions are in `PP`-named tests in `TestGatherSimplified`, and all 5 `show deltas` are in `PP`-named tests in `TestAdaptorSimplified` (`2overleafPP`, `2listSumrPP`, `2reluPP`, `2reluSimplerPP`, `2reluMaxPP`). None of them is among the 8 failures. The remaining 489 tests in `CAFlessTest` are cross-testing value assertions, which variable numbering cannot reach — so a full unoptimized run of that suite adds nothing, and the ~50 minutes it takes are better spent elsewhere.

### E11. What this evidence does not cover

tasty runs and totals every test — the unoptimized run reports "6 out of 183 tests failed", not a halt. What truncates is the *inside* of one `testCase`: HUnit's `@?=` throws `HUnitFailure`, which aborts the rest of that `do` block, so a test holding four assertions reports one `expected:`/`but got:` pair and never executes the other three (verified: all six failing tests report exactly one pair, while three of them contain four assertions each). So the inventory holds the *first* divergence of each diverging test, not every assertion inside it. Across the whole corpus that is 6 sampled divergences out of an unknown number within those 6 tests; all 6 classify identically, and identically again across six build configurations, but the assertions behind them are inference rather than measurement. Getting them would mean patching expectations one round at a time — and the method note above shows why the obvious shortcut, instrumenting the assertions, does not work.

E3's attribution is narrower than E1's observation, and deliberately left that way. It isolates cause by rebuilding one module at a time, which scopes it to `minimalTest` — so it accounts for four of the eight `-O0` divergences, and no cause has been established for `minimizedCNNOPP1e`, `minimizedCNNOPP4bW`, `minimizedCNNOPP5bW` or `4S0rmapAccumRD01SN531b0PP`. That is affordable because nothing downstream turns on it: E2 repairs all eight regardless of what moved the counter, so the cause is explanatory rather than load-bearing. Establishing it would cost four more builds of a suite six times the size, to sharpen a sentence rather than a decision.

The version axis is measured at `-O1` only — 9.10.3 fails 3 and 9.14.1 passes (E6) — so version and optimization level are never crossed: no compiler but 9.12.4 has been run unoptimized. I6 puts all three on the `-O0` binary, which is where a crossed failure would surface.

### Risks, and what bounds them

**Only one relabelling can reach the printed text, and it does not currently happen.** First-occurrence numbering depends on the printed structure and on which occurrences are the same variable, so any relabelling that leaves the *term* unchanged prints identically — gaps, shifts and permutations alike. The one live place where an AST variable id's order becomes term structure is `bindsToLet` (`AstInline.hs:284-295`), which emits the collected `let` chain `sortOn (Down . varId)`, folded outermost-first; the other id-ordered folds do not qualify (`AstInline.hs:315`'s `DMap.keys` feeds an order-insensitive `any (`varInAst` t)`, `AstEnv.hs:138` sits inside a commented-out `showsPrec` helper, `DeltaEval.hs:75`'s `toAscList` walks positional `InputId`s, and `DeltaEval.hs:723` drains *delta node* ids, a separate counter (`DeltaFreshId.hs`) that no printed AST variable name comes from).

That sort leaves a visible signature: a printed `let` chain must have **ascending** binder numbers. Measured across the corpus with a nesting-aware parser: **102 multi-binder chains, 102 ascending, no exceptions.** So no permutation among let-bound variables occurs today, and a permutation that broke `bindsToLet`'s premise (a binding's RHS mentions only smaller ids) could not reach the output at all — it would bind a dependency inside the scope needing it, i.e. crash or miscompile.

Measured, not assumed: across every divergence E1, E3 and E6 record, every relabelling was order-preserving and every skeleton equal, and no `-O0` output contained a non-ascending `let` chain. So the case is not merely absent from the corpus — it is absent from every build actually tried.

A second, smaller risk: the two-pass printer is not streaming, so a large artifact is built twice into memory before a character is emitted; `printAstPrettyButNested` (7 users) is the one to watch, since `PPTools.hs:42-43` records that its mode computes derivatives.

## Design

Canonicalize variable names **at print time only** — never renumber terms. Two invariants make R4 non-negotiable rather than merely tidy: `AstInline.hs:284-295` (`bindsToLet` emits lets `sortOn (Down . varId)`, so a binding's RHS must mention only smaller ids — a property the counter supplies and no comment at that site states, so it is inference rather than quotation) and `DeltaEval.hs:721-731` (reverse-pass scheduling relies on parent node id > child node id, which `Delta.hs:124-134` does document).

Each exported printer renumbers the variables appearing in **its own complete output** to a dense `1,2,3,…` sequence in **order of first appearance in the printed text**, one sequence shared across all rank prefixes, with explicitly named variables (today's `dret`) excluded. Since `printAstVarId` is the single funnel through which every variable name is rendered, the numbering is obtained by printing **once**, in a marking mode, and then resolving the markers in a separate `String -> String` pass over the finished text.

Making the resolver a separate pass over the *assembled* string, rather than a second print, is what keeps the design small — resolution over a concatenation is compositional where per-printer canonicalization is not. Two consequences:

- `printAstVarName` is *kept* rather than deleted, since marked output is what lets it compose with a separately printed term (and `PPEngine.hs:89,95` uses it internally regardless). It does **not** follow that the 40 concatenation sites need no entry point — I2 works through two of them that would need opposite hand-written prefixes — so `printAstLambdaSimple`/`Pretty` stay in the plan;
- variables renamed through `varRenames` are never marked, so `dret` passes through untouched and that mechanism needs no change;
- the marker carries the rank-derived prefix and is delimited on both sides (`'\1' : prefix ++ show n ++ "\1"`), so one left-to-right scan suffices, the printer runs once rather than twice, and a variable followed immediately by a digit cannot be mis-parsed.

The alternative — a ninth walk over `AstTensor` beside `printAst`, `varInAst`, `inlineAst`, `substitute1Ast`, `interpretAst` and the rest — was weighed and rejected, but not because a ninth walk is unidiomatic; it is perfectly idiomatic here, and it would not duplicate the grammar, which stays one declaration in `Ast.hs`. It was rejected because such a walk must agree with the printer about *which* variables reach the output, and that knowledge lives in `PPTools.hs`, not in the datatype: `printAstHFun` renders `"<lambda>"` under the default config (`:572-588`), and `AstShare _var v` discards its binder (`:199`). Constructor coverage a compiler can check — though weakly here, since `cabal.haskell-ci` sets `error-incomplete-patterns: <0` and warnings are not reported; agreement with those two elisions it cannot check at all, and a disagreement is silent, giving either a printed variable with no number or numbering gaps that depend on structure the reader cannot see. Printing twice makes the printer its own enumerator, so the question cannot arise. The price is one extra rendering and a non-streaming printer, paid where it does not matter and avoidable through `runRawNaming` where it might.

**Why first printed occurrence and not ascending raw id.** `add` returns the counter's *old* value and adds exactly 1 (atomic-counter's own haddock), so the issued sequence never skips: every gap in a printed term is an id minted for something that did not survive into it. Measured over the corpus, 246 of the 351 literals carrying variables have gaps, with a median span/count of 2.3 — a printed term typically shows about 43% of the ids issued across its own range — while 295 of 351 start at offset 1, so the *base* is pinned by the reset and everything after it is not.

What varies is therefore re-spacing and re-ordering, not translation. `testCNNOPP3b` (`TestConvSimplified.hs:1354`/`:1356`) shows both: the raw artifact's 25 variables are `1, 155…178`, one contiguous block; the simplified artifact **keeps 16 of them** (`159…166, 171…178`) and **re-mints 8** (`255,257,259,261, 267,269,271,273`, two counter values burned per re-mint). Ascending-id keeps those two literals distinct only because the re-minted ids sort after the retained ones — a fact about *when the refresh ran relative to the original construction*, which is exactly what a change of evaluation order moves. First occurrence depends only on the printed structure and on which variables are the same variable, so it is invariant under any relabelling, re-spacing or re-ordering alike.

Ascending-id's apparent advantage (6 literals losing uniqueness against first-occurrence's 12) is therefore an artifact: the extra distinctions it preserves are themselves build-dependent. The three pairs that do collapse — `TestConvSimplified.hs:1354`/`:1356`, `:1787`/`:1789` and `TestAdaptorSimplified.hs:2657`/`:2670` — are pairs of near-identical literals asserting that two terms are alpha-equivalent. Replace each with one literal plus an explicit equality between the two printed forms, which states the fact instead of encoding it in two 1419-character strings. `TestAdaptorSimplified.hs:596`/`:602` collapses under either scheme and is genuinely benign (Out of scope, above).

Of the 392 expected strings, 254 change and 138 do not.

## Implementation

### Reviewing this PR

The diff is dominated by 254 regenerated expectation strings, and those are not eye-reviewable: canonicalization renumbers index variables too, so nearly every character after the first binder moves. Read it commit by commit instead. C1-C3 are refactors whose output is byte-identical, and are where the design is actually visible; C4 is the regeneration, best reviewed through the C5 gate rather than by eye; C8 is the behavioural change and the one to read closely.

Each leaves the tree green, with no exception — C6 explains the ordering that buys the one commit that would otherwise have been red.

1. **C1. PPTools machinery** — the marker in `printAstVarId`, the resolver, and the raw/canonical doors; inert, nothing resolves canonically yet.
2. **C2. PPEngine restructure** — every printer routed through the raw door, and each artifact printer emitting header and body as one string; output byte-identical, which the green `CAFlessTest` here *is* the evidence for.
3. **C3. The lambda entry point** — `printAstLambdaSimple`/`Pretty`, and the 40 concatenation sites routed through it: the 14 `printAstVarName` sites in `TestAdaptorSimplified` and the 26 hand-prefixed ones in `TestConvSimplified.hs:1786-1985`. `printAstVarName` is **kept** (`PPEngine.hs:89,95` uses it). Still byte-identical under the raw door.
4. **C4. Flip to canonical + regenerate** — one door swapped, the ascending-`let` tripwire repointed at `printArtifactPrettyRaw` — it calls `printArtifactPretty`, lives on master, and goes vacuous otherwise — with its non-vacuity re-proved after the repoint by flipping `bindsToLet`'s `Data.Ord.Down` again, the rewritten literals, the **seven** live printed-length pins in `TestRevFwdFold`, and `README.md:151-161`. Also here, and **not** earlier: replace the three near-identical assertion pairs (`TestConvSimplified.hs:1354`/`:1356`, `:1787`/`:1789`, `TestAdaptorSimplified.hs:2657`/`:2670`) with one literal plus an explicit equality between the two printed forms, so the alpha-equivalence they encode implicitly is stated rather than left as two strings the regeneration has just made identical. It cannot sit in C3, where an earlier draft put it: each pair prints two *different* terms — at `:1354`/`:1356` the raw artifact against the simplified one, whose numbering the Design section shows diverging (`155…178` against re-minted `255,257,…`) — so before the flip the equality is false and C3 would land red. The flip is what makes it true, so it belongs in the same commit. Atomic: splitting it leaves a red commit. `README.md` carries no verification stamp, so the mixed `.hs`/`.md` commit orphans nothing. The changed-literal count has been re-derived under the current design — no reserved range, every token renumbered by first appearance — and stands: **254 of the 392 literals change, 138 do not**. This lands **before** the minting conversion, which is what makes both green — see C6.
5. **C5. The one guard worth having** — a *one-shot* skeleton-equality gate over C4's regenerated strings: blank every variable token in the old and the new literal and require byte equality, then hand-review the residue. Mandatory rather than optional, because after regeneration the suite passes by construction and cannot tell a correct renumbering from a term regression baked in at the same moment — and the diff is not eye-reviewable, since canonicalization moves index variables too. Dropped from earlier drafts: a permanent canonical-form checker under `tools/` (it could never disagree with the suite, which runs the printer) and the ascending-`let` tripwire (vacuous under first-appearance numbering, and the corruption class it watched for is already covered by live guards at `AstSimplify.hs:3226-3228,5545` and `AstTools.hs:178,230` — all of which fired in the parallel experiment).
6. **C6. Mint the hand-made variables properly** — the ~60 `intToAstVarId` sites (`TestGatherSimplified` 33, `TestConvSimplified` 14, `TestMnistPP` 9, `ConvVjpBench` 3, `TestConvCorrect` 1) become `funToAst ftk id`, and `AstVectorize`'s five prints plus `ConvVjpBench`'s three move to the raw entry points. **Byte-identical, and that is why it sits here rather than before C4.** A canonical name is the variable's position in first-appearance order, which `funToAst` does not move: it changes the *raw* id and consumes one extra counter value, and canonical numbering reads neither. The `length (show …)` pins survive for the neighbouring reason — they measure the derived `Show`, whose raw ids stay 9 digits wide, the reset-free maximum being offset 13,229 against a ceiling of 899,999,999. Ordered the other way round this commit would have been the series' one red link, touching 27 of the 392 literals and putting all 44 `length (show …)` occurrences at risk, since `TestGatherSimplified`'s minting sits precisely in the `*SimpPP*` tests that pin lengths rather than strings — and it would have cost a second, differently-shaped regeneration into an intermediate numbering that is neither the old one nor the canonical one.
7. **C7. Delta ids** — the resolver's extra `DeltaShare` token rule and the five expectations. Not a separate `showDeltaCanonical`; I4 records why that shape was superseded.
8. **C8. Drop the counter resets** — 200 call sites, the two functions, `setVarCounter`, the `AstSimplify.hs` caveat, the hlint fallout, and `test/MinimalTest.hs:27`'s switch to `testGroup`, with the before/after parallel runs and the `/usr/bin/time -v` A/B in the message. Also the three `setTotalSharing` warning comments — they belong here because this is the commit that makes a suite parallel, which is what turns that global from a curiosity into a trap.
9. **C9. CI** — the `.github/haskell-ci.patch` hunk and its comment.
10. **C10. Documents** — `.md` files only, plus re-stamping.


### What changes, file by file

### I1. `src/HordeAd/Core/PPTools.hs` — the mechanism

Add a hidden mode field to `PrintConfig` (`:44-55`) beside the existing `varRenames :: IntMap String`, which keeps precedence, and rewrite `printAstVarId` (`:60-66`) so the offset `n` is marked rather than printed when marking is on, and looked up in a rank map when it is off.

Make the two-pass discipline a **type-level** guard rather than a runtime one: export the field *selectors* but not the constructor for the new field, and export `runCanonicalNaming` / `runRawNaming` as the only doors:

```haskell
module HordeAd.Core.PPTools
  ( PrintConfig(loseRoudtrip, ignoreNestedLambdas, varRenames), defaulPrintConfig
  , runCanonicalNaming, runRawNaming
  , printAstVar, printAst
  ) where
```

Record *update* needs only selectors, so `defaulPrintConfig {loseRoudtrip = False}` keeps working; record *construction* breaks, which nothing in-tree does — `PPEngine` is `PPTools`' only importer (`PPEngine.hs:16`). Then "forgot to resolve the markers" cannot be written, which closes the one silent failure mode: a raw string quietly regenerated into the expectations.

**No reserved range, and the hand-minted ids can then go away.** First-appearance numbering already renumbers every token by printed position, so an id of 0 or 99 needs no special case and C4 can precede C6. The tests mint ~60 variables at literal ids — `intToAstVarId 100000000` (33 sites in `TestGatherSimplified`, 13 in `TestConvSimplified`, 9 in `TestMnistPP`) and `intToAstVarId 100000099` (`TestConvSimplified.hs:1782`, `TestConvCorrect.hs:167`, `bench/ConvVjpBench.hs:201`, `bench/ConvVjpBench.hs:299`, `bench/ConvVjpBench.hs:830`). Every one is **local**: the id is minted, put into an `extendEnv` and/or a term, and interpreted inside the same `let`, never escaping it. They exist only to get a stable, recognisable printed name (`u0`, `w0`, `u99`) — exactly what canonical printing supplies for free. (`TestConvCorrect.hs:158-161` says its terms are the ones `convVjpBench` interprets; that is a claim about the *terms*, not the ids, and the two run in separate processes, so no cross-file agreement is required.)

Replace each with existing API — `funToAst ftk id` returns precisely `(fresh var, AstVar var)`:

```haskell
-- before
varName = mkAstVarName ftk . intToAstVarId $ 100000000
var     = AstVar varName
-- after
(varName, var) = funToAst ftk id
```

That deletes three things from this design: a **reserved-range** concept (offsets `<= 0` never renumbered), the plan's only **term-level change** (relocating `100000099` below the counter floor across five files), and the **`n < 0` negative-name branch** of `printAstVarId`, which becomes dead by construction — it is already dead in practice, since 0 of the corpus's 7361 variable tokens exercise it. `printAstVarId` reduces to: rename lookup → canonical lookup → error.

It also removes a real hazard rather than a hypothetical one. The alternative of *pinning* names through `varRenames` fails because a rename is returned verbatim **before** the rank-derived prefix is chosen: offset 99 is occupied by an ordinary *index* variable, printed `i99`, in three expected strings (`TestConvSimplified.hs:1248, 1345, 2061`), which name-pinning would have silently rewritten to `u99`.

Cost: ~60 mechanical test edits. Two safety checks already done — the 42 `length (show …) @?= N` assertions are unaffected, because a freshly minted id is 9 digits exactly as `100000000` is and stays 9 digits once I5 removes the resets; and the 26 hand-written binder prefixes in `TestConvSimplified.hs:1786-1985` — 24 of them `"\\u0 -> "`, and `:1786`/`:1788` `"\\u0 -> \\u99 -> "` — then fold into the same lambda entry point I2 already introduces for the 14 `printAstVarName` sites, putting 40 sites on one mechanism instead of two ad-hoc ones. `TestMnistPP.hs:260`/`:262` are a 41st and 42nd concatenation, `"\\dummy" ++ " -> " ++ printAstSimple …`, and are deliberately left alone: the prefix names no variable and `printAstSimple` emits no header, so canonical numbering starts at 1 in the body either way and the literal stays correct. Marker details: mark with the offset (always `>= 1`, since I1's minting leaves no id below the counter's floor, so the payload is always digits), delimit with `'\1'`, and have the resolver accept a pair only when the text between is all digits. `'\1'` is safe because every printer branch emits ASCII source text, numbers, or `shows` of shapes, conversions and concrete arrays, and `GoodScalar` (`Core/Types.hs:155-167`) admits no `Char` element — checked empirically too: across all 392 expected strings the only escape sequence that occurs is `\\` (1045 times, the lambda backslash). Key the rank map by id and let each occurrence compute its own prefix, since `reshapeVarName` (`Ast.hs:291-293`) can give one id two ranks and `respanVarName` (`:305-309`) two prefixes, and since one id is genuinely bound twice in disjoint scopes of one term (`let i60 = …` twice at `TestGatherSimplified.hs:1374`, `let i33 = …` twice at `TestConvSimplified.hs:1345`).

### I2. `src/HordeAd/Core/PPEngine.hs` — the entry points

Every exported printer resolves **one string covering header and body**. That is not cosmetic: `printArtifactPrimalSimple`/`printArtifactPrimalPretty` (`:86-96`) today build `"\\" ++ printAstVarName artVarDomainRev ++ " -> " ++ …` from two independent calls, and canonicalizing only the body turns `TestAdaptorSimplified.hs:995`'s `\x1 -> rfromK (let x4 = … x1 …)` into a shadowed `\x1 -> … let x1 = … x2 …`. With the header inside the same resolution, `artVarDomainRev` — minted first, hence lowest id — takes rank 1 and every `\dret u1 ->` survives verbatim, with no seeding logic at all. `artPrimalRev` is a lazy field (`Ast.hs:345`, "rarely used, so not forced"); the derivative printers must keep not forcing it.

**The 40 concatenation sites do need a joint entry point.** An earlier draft argued they self-resolve, because the resolver runs over an assembled string and the binder appears first in it. That is wrong, and two sites in the tree show why they do not even fail the same way:

- `TestConvSimplified.hs:1807` is `"\\u0 -> " ++ printArtifactPrimalPretty …`, and that printer emits its *own* `\u1 -> ` header (`PPEngine.hs:94-96`). The header takes canonical 1 and the test's `u0` takes 2, so the hand-written prefix would have to read `"\\u2 -> "`.
- `TestConvSimplified.hs:1786` is `"\\u0 -> \\u99 -> " ++ printAstPretty t`, whose printer emits no header at all, and whose body mentions `u99` before `u0` — so that prefix would have to read `"\\u2 -> \\u1 -> "`, with the two binders *reversed*.

The prefixes are literal text the printer never emitted, so nothing marks them; and I3's rewriter cannot repair them either, being line-local while the prefixes sit on the preceding line. Add `printAstLambdaSimple`/`printAstLambdaPretty`, taking a binder and a term and resolving `binder ++ " -> " ++ body` as one string, and route all 40 sites through it — deciding the binder's number once in `PPEngine` rather than forty times in the tests. `printAstVarName` is **kept**: `PPEngine.hs:89,95` uses it internally.

Two further families of new exports, then:

- The lambda entry point just above, `printAstLambdaSimple`/`printAstLambdaPretty`.
- Raw counterparts (`printAstSimpleRaw`, `printAstPrettyRaw`, `printArtifactPrettyRaw`) for the eight non-test callers — and for one test, the ascending-`let` tripwire on master, whose whole point is to read counter-order names: `AstVectorize.hs`'s five trace sites (`:72`, `:79`, `:684`, `:692`, `:693`, behind `traceRuleEnabledRef`, default `False`) and `bench/ConvVjpBench.hs:837-841`'s three `PRINT_TERMS` prints. `mkTraceRule` renders `from` and `to` into one `"rule … sends X to Y"` line from two independent calls (`:692-693`), so per-call canonical numbering would give one variable a different name on each side of the arrow — the one thing that trace exists to compare — and would print each term twice, while `padString` (`:650-654`) already forces the whole string before truncating — as does `ellipsisString` (`:656-660`) at the two START/END sites.

### I3. The mechanical refresh

The new literals are a pure function of the old, so generate them offline rather than harvesting from failures: HUnit's `@?=` throws and so aborts its enclosing `Assertion`, so a run reveals only the first stale expectation per test, and 55 of the 159 print-asserting tests carry four apiece — up to four full runs, which is what `test/CLAUDE.md:15` now says, that undercount having been corrected on master ahead of this branch rather than here.

The rewriter uses a boundary-anchored token regex

    (?<![A-Za-z0-9_'])([ixvmtuw])(m?)(\d+)(?![A-Za-z0-9_'])

which finds, across the corpus, exactly the 7361 variable tokens and nothing else — `sdot0`, `sindex0`, `ssum0`, `tproject1`, `sgather1 @50`, `sreplicate0N` and float literals are all rejected by the boundaries, and no expected string carries one number under two prefixes. All 392 `@?= "…"` are single source lines, so the rewrite is line-local — but enumerate them with `@\?=\s*"` rather than `@?= "`: `TestAdaptorSimplified.hs:1360` is the one site written with two spaces, and a single-space pattern skips it in silence, leaving one stale expectation behind. It renumbers **every** token: first-appearance numbering has no reserved range, so the `u0`/`w0`/`u99` occurrences renumber with the rest whether or not I1's minting conversion has landed yet.

Two things put the rewrite out of reach of a purely offline pass. The line-local rewrite cannot fix the hand-written binder prefixes, which sit on the line *before* the `@?=` (`TestConvSimplified.hs:1786` against `:1787`) — C3 routes those sites through the lambda entry point instead. And **seven** live assertions pin a printed *length* rather than a printed string, all in `TestRevFwdFold` and six of them spelled `length` then `(printAstSimple` on the next line, which is why a grep for the one-line spelling found only `:2929`: `:2403, :2417, :2431, :2449, :2469, :2536, :2929` (two more at `:2492, :2516` are `_`-prefixed and dead). Canonical names are shorter, so all seven change, and two of them are megabyte-scale (`4648181`, `300893`) and can only come from a run.

Keep the rewriter in the repo root and delete it before the commit lands. Nothing permanent goes into `tools/`: a checker asserting the literals are in canonical form could never disagree with the suite, which asserts the same thing by running the printer. What *is* worth doing once is the skeleton-equality gate in C5 — blanking the variable tokens on both sides of the regeneration and requiring byte equality — because that is the one check the suite cannot perform on itself.

Running the suites afterwards with zero failures is the proof that the rewriter's model and the printer's implementation are the same rule.

### I4. Delta ids

`TestAdaptorSimplified.hs:603,1069,1227,1263,1429` assert on `show deltas`, embedding raw ids from the *second* counter (`Core/DeltaFreshId.hs`) as `DeltaShare 100000002`; the `InputId n` beside them are positional and contiguous from 0 (`DeltaEval.hs:222-226`) and already deterministic.

**Measured: the delta counter does not diverge at `-O0`** — all five tests pass in an unoptimized `CAFlessTest`. So this item is not motivated by optimization level; it is the price of I5. `resetIdCounter` is what pins those ids to `100000001` upwards, and removing it makes them depend on everything that ran before, so I4 exists to pay for I5 rather than to fix the `-O0` problem — and if I5 were dropped, I4 could be dropped with it.

**Fold this into the same resolver rather than writing a second one.** The marked-printing resolver already renumbers delimited tokens by first appearance; delta ids need only one extra token rule, anchored on the constructor (`DeltaShare <digits>`). That removes the need for a separate `showDeltaCanonical`, for any change to `Delta`'s derived `Show`, and for a second numbering convention to keep aligned with the first. Anchor on the constructor and never on the magnitude of the number — the counter's base is not something to depend on. `InputId` prints `(InputId 0)` with small semantic indices and stays untouched.

(Superseded shape, kept for the reasoning: add `showDeltaCanonical` to `test/tool/Shared.hs`, renumbering the ids after the fixed prefix `DeltaShare ` — by first appearance, as in I1. That prints `:1069`'s `DeltaShare 100000003 ⊃ 100000002 ⊃ 100000001` as `1 ⊃ 2 ⊃ 3`, i.e. outermost-first, where the raw ids read innermost-first. The *property* `Delta.hs:124-134` documents (parent id > child id, consumed by `DeltaEval.hs:721-731` via `DMap.maxViewWithKey`) is a property of the graph, not of the rendering, and holds regardless; if it is worth asserting it should be asserted, not inferred from the digits. Keeping this in the test tool library rather than `PPEngine` avoids adding a lexical post-process of a derived `Show` to the public API. Note it does not widen what CI can run: those five assertions live in `CAFlessTest`, not `minimalTest`.)

### I5. Dropping the counter resets — and getting parallel PP tests back

This is the item that delivers R3 and the parallel payoff the Summary names, so state it as one. Parallel printed-AST tests break today because of the *reset*, not the counter: `add` is an atomic fetch-and-add, so concurrent mints stay unique and each thread's own mints stay in program order, whereas `resetVarCounter = set unsafeAstVarCounter 100000001` (`AstFreshId.hs:43`) is an absolute write, so a second test rewinds the counter while the first is mid-term and that term's later mints re-issue ids it has already used. Every structure keyed by id then conflates two distinct variables — `AstEnv` (`AstEnv.hs:29`), `AstBindings` (`AstInline.hs:275`), `AstMemo` (`AstInline.hs:39`) — `substituteAst`'s stated no-shadowing invariant (`AstSimplify.hs:5468-5471`) is violated so substitution captures, `astGatherKnobsS` errors (`AstSimplify.hs:3226`, its comment at `:3215-3218` naming `resetVarCounter` as exactly how freshness breaks), and the premise behind `bindsToLet`'s descending sort — that a binding's RHS mentions only smaller ids (`AstInline.hs:284-295`) — becomes false, so bindings land outside the scopes they need and subterms can duplicate.

All of that is measured, not inferred (E5): with `testGroup` in place of `inOrderTestGroup`, the PP subset fails 0/10/12/14/14 of 26 at 1/2/4/8/16 threads and varies run to run at 16 (15, 15, 13). The failures are exactly the predicted collisions — `astGatherKnobsS: gather vars in v0`, a `substitute1Ast` kind mismatch, `varInAst`'s binder assertions — plus one silently wrong term. That last point decides a design question: canonical printing alone would leave those runs broken, because they are corruption rather than misnumbering.

So removing the resets, together with canonical printing (I1-I2), canonical delta rendering (I4) and hand-minted ids outside the issuable range (the properly minted ids of I1), is what makes the printed-AST suites parallel-safe again. **Take R3's payoff: replace `inOrderTestGroup` with `testGroup` in `test/MinimalTest.hs:27`.** That is the suite CI runs unoptimized on three GHC versions, so it is where wall-clock is worth reclaiming, and unlike `CAFlessTest` it has no benchmark role to protect — `CAFlessTest` keeps its wrapper and `test/CLAUDE.md:9` is rewritten to say that its remaining reason is timing comparability, not correctness. `AstVectorize.hs:645`'s `traceNestingLevel` is a third global of the same shape and should be named in the commit message so it is not reintroduced; it only garbles trace indentation. The second, `setTotalSharing`, is analysed below rather than here — it has five live call sites, not none.

R2 is the requirement to honour while doing it, and E8 shows canonical printing supplies it outright — with all 37 resets deleted, the same tests printed under three different preceding contexts agree 12/12 once canonicalized, against 0/12 raw — and supplies it *better* than the resets, which cannot re-mint what a CAF has already built. So `resetVarCounter` can be deleted rather than given new semantics.

With printing canonical, `resetVarCounter` is load-bearing for nothing: the 387 printed-AST expectations no longer depend on it; the 42 `length (show …) @?= N` assertions in `TestGatherSimplified` depend only on ids being 9 digits wide (the 43rd, `:202-203`, compares two printed lengths against each other and does not depend on width at all), which I1's `funToAst` minting preserves — measured, the highest offset a reset-free run reaches is 13,229, against a 9-digit ceiling at 899,999,999; the 5 `show deltas` are covered by I4. Remove the 195 `resetVarCounter` and 5 `resetIdCounter` calls, then the two functions (`AstFreshId.hs:42-43`, `DeltaFreshId.hs:30-31`) — nothing in `src/`, `bench/` or `example/` calls them — except that the *body* of `resetVarCounter` is worth keeping as a generalized `setVarCounter :: Int -> IO ()` for the invariance test below. This lets `AstSimplify.hs:3215-3218` drop the caveat that its freshness assumption holds only while `resetVarCounter` is unused, and `AstFreshId.hs:39-41` / `DeltaFreshId.hs:27-29` drop their "run sequentially" warnings.

Removing a leading `resetVarCounter` leaves single-statement `do` blocks (e.g. `TestAdaptorSimplified.hs:658-661`), and `.hlint.yaml`'s `within: ["Test*"]` list (`:118-124`) does not ignore `Redundant do`. `hlint .` must be back to `No hints`; treat any hand-count of affected sites as a floor.

**Sign the one hazard this PR does not remove: `setTotalSharing`.** It is the second global of the same family (`AstTools.hs:271-278`), read by `astIsSmall` and toggled by `rev'` (`CrossTesting.hs:84-89`) at 50 call sites in `TestGatherSimplified` alone — which is to say, inside the very suite I5 makes parallel. E9 measured exactly that configuration: three parallel repeats, **0 exceptions and 0 structural differences**, every failure a printed-AST relabelling that canonicalization repairs, and no `rev'` test failing. So the hazard is bounded, not absent.

Bounded, because the flag changes how much the simplifier *shares*, which moves term structure but not values, and `rev'` compares gradients — indeed `assertEqualUpToEpsilon1` binds its two AST fields as `_astVectSimp`, `_astSimp` and ignores them. Not absent, because a *printed* term produced while another test holds the flag would differ structurally, and the canonical numbering changes only **names**. One test couples the two deliberately today, `TestConvSimplified.testCNNOPP4bD` (`:2038-2043`), and that is correct because `CAFlessTest` stays sequential.

Record the conclusion, so it is not re-derived. The comment does not guard a door this PR leaves open — the measured configuration is clean, and the one test pinning a printed term under the flag stays sequential. The point is that this question looks alarming, takes real work to bound, and will otherwise be asked again. Following the repo's convention that a substantial note lives once at its canonical occurrence with tiny pointers at the analogous sites, extend the existing comment at `AstTools.hs:270-272`:

```haskell
-- Turns off all but the most trivial cases of astIsSmall.
-- For tests only. Affects all simplification and inlining taking place
-- in parallel in the program at the time it's changed.
--
-- Changing it changes the term, not merely the names of its variables:
-- more sharing means bindings that are otherwise absent. That is the
-- point, and comparing interpretations across settings is the right use
-- -- values do not depend on sharing, and the harness ignores the AST
-- it is handed (see _astVectSimp, _astSimp in CrossTesting). Printed
-- terms do depend on it, and the canonical numbering in Core/PPTools.hs
-- normalizes names, not structure. Hence the one rule: a suite holding
-- both a toggle of this ref and a printed-AST test stays sequential,
-- since under concurrency one test's setting reaches another's term.
```

and one line at each of the two use sites — at `CrossTesting.hs:84`, that the toggle is safe there because `assertEqualUpToEpsilon1` ignores the two AST fields it is handed (they are bound as `_astVectSimp`, `_astSimp`) and compares only values, which sharing cannot change; at `TestConvSimplified.hs:2038`, that this test deliberately pins a printed artifact built under the flag, which is correct sequentially and is what keeps `CAFlessTest` off the parallel list.

Note what the warning is *not*. Nothing in the tree equates an AST built with the flag against one built without it, and nothing should: that the term differs is the flag's purpose. The exposure is only that the ref is global, so concurrency can leak a setting between tests — which no value assertion would ever notice. Threading the flag through `SimplifyKnobs` (`AstSimplify.hs:151`) would retire all three comments and delete an `unsafePerformIO` read from `astIsSmall`, which sits on the simplifier's hot path — a worthwhile follow-up, out of scope here, though cheaper than its 37 call sites across four modules suggest: the 29 `ixIsSmall` ones are all inside `astGatherKnobsS` or `astScatterKnobsS`, which already take knobs. The obstacle is `astIsSmall`'s 8, whose callers — `astLet`, `inlineAst`, `astShareNoSimplify`, `astLetFun` among them — mostly carry none.

### I6. CI and documentation

- `.github/haskell-ci.patch` — delete `--test-options='-p "detSquare"'`, and with it the part of the hunk comment that justifies the `-p` narrowing: once the printed-AST tests are build-independent there is nothing left to narrow away. That comment's three factual errors — the "lands four higher" shift, the cause attributed to thunk forcing, and the implication that passing optimized meant safe — were corrected on master ahead of this branch rather than here, so what this PR deletes is a comment that is accurate but obsolete, which is the easier review. Keep the `minimalTest` narrowing, which is about `samplesData/` not shipping in the sdist. Regenerate twice and compare (`haskell-ci regenerate`), per the double-apply hazard.
- `.github/workflows/lint-and-test-suites.yml` — widen its Tests step from `minimalTest` on 9.12.4 to **the whole of `CAFlessTest`, optimized, on all three compilers**: `cabal test CAFlessTest --enable-optimization` under a GHC matrix of 9.10.3, 9.12.4 and 9.14.1, with no `-p` at all. The obvious narrower move — the `-p "/PP/"` subset — is a trap: those 183 tests and `minimalTest`'s 75 overlap in only 26, so swapping one for the other would drop `TestGatherSimplified`'s 49 non-`PP` tests, `detSquare3` and `detSquare9` among them, from optimized coverage entirely. Running the suite whole avoids choosing, and subsumes what the step covers today. It is what makes V2 a standing guard rather than a one-off: R1's version half is the half nothing watches today. `CAFlessTest` reads no MNIST data, so it runs here as happily as `minimalTest` does — it is normally left out of the generated workflow on cost, not on capability — and the whole suite is 141s optimized, measured, so the added cost is two more optimized builds plus about seven minutes of test time across the matrix. `minimalTest` stays in the generated workflow, unoptimized on the same three compilers, and the overlap between the two is deliberate: the 26 PP tests in `minimalTest` are then covered at both optimization levels on every supported compiler.
- `CLAUDE.md:75`, `:79`, and `:141` — the last is the oracle claim, "an unchanged printed artifact means a byte-identical artifact and hence identical interpretation", which weakens to *identical up to the variable numbering the printer now normalizes away*. State the payoff accurately: ~72 additional tests gain **unoptimized** coverage on three GHC versions; they already run optimized in the hand-written workflow.
- `test/CLAUDE.md:9` — both correctness reasons for CAFlessTest's `inOrderTestGroup` dissolve; keep the wrapper (the suite doubles as a sequential benchmark), name what still requires it so the next reader does not delete a live guard, and keep the surviving observation that `AstInline.hs:288` still sorts lets by descending raw id. `:15` — the round count is already corrected on master; what remains is the narrowing this PR earns, which is nowhere else in this document. Churn from a simplifier change *survives*: a changed term prints differently and always will. What disappears is churn where the term did not change and only the numbering moved — a simplifier edit that mints a different number of intermediates while leaving an alpha-equivalent term today churns every expectation and afterwards churns none. Narrow the bullet to say that rather than deleting it: the harvesting advice is still needed for the churn that remains, and the offline rewriter cannot be named as a standing route because I3 deletes it before the commit lands. `:16` — recheck its `TestMnistPP.hs:6` citation, since C4 edits that file (I6 deliberately leaves it alone).
- `bench/CLAUDE.md:11` — checked: it already describes the diagnostic ("`PRINT_TERMS=1` prints the compared gradient programs instead of benchmarking"), and that sentence survives C6 untouched. What is worth adding is one clause on why the output stays *raw*-numbered: the three programs printed there are meant to be compared against each other, and per-print canonical numbering would number each by its own first-appearance order, so one variable could wear three different names — the same reason the `AstVectorize` trace sites keep the raw printers (I2). Its stamp is hand-written (it cites no line), so it needs no re-stamp.
- `README.md:151-161` — the quoted artifact renumbers with its test; re-run `python3 tools/check-doc-examples.py README.md`.
- `horde-ad.cabal` and `CHANGELOG.md` — **already done on master ahead of this branch**: the version is `0.4.0.0` and the unreleased section exists. This PR's own export-list changes need no further bump, since they land in that same unreleased version, and their changelog lines go in at release time with everything else still to come. Nothing to do here.
- Re-stamp `CLAUDE.md` and `test/CLAUDE.md` with `python3 tools/check-plan-citations.py DOC --restamp` in a commit touching only `.md` files, and re-run all three checkers over each edited document.

### API and compatibility

`HordeAd.Core.PPTools` narrows its export list: `PrintConfig(..)` becomes the three field selectors, and the new mode field's constructor is deliberately not exported (I1). `HordeAd.Core.PPEngine` gains `printAstLambdaSimple`/`printAstLambdaPretty` and the three `*Raw` printers (I2). `AstFreshId`/`DeltaFreshId` lose `resetVarCounter`/`resetIdCounter` and gain `setVarCounter` (I5). Narrowing an export list is PVP-breaking even though `PPEngine` is `PPTools`' only in-tree importer, all three are breaking, but they need no version bump of their own: master is already at `0.4.0.0` and unreleased, so they land in that version and are recorded in its changelog section at release time (I6).

## Future work

- **Thread `setTotalSharing` through `SimplifyKnobs`** (`AstSimplify.hs:151`), retiring the three warning comments I5 adds and deleting an `unsafePerformIO` read from `astIsSmall` on the simplifier's hot path. I5 bounds why this is safe to defer.

- **The ascending-`let` tripwire is done**, on master ahead of this branch rather than here: a test prints one representative artifact and asserts its `let`-chain binders ascend, proved non-vacuous by flipping `bindsToLet`'s `Data.Ord.Down`. What this PR owes it is one word. It reads the raw printer today only because there is no other kind; once C4 lands, first-appearance numbering would number a chain in printing order and the assertion would pass by construction, so **point it at `printArtifactPrettyRaw` in C4 — the raw twin of the `printArtifactPretty` it calls — or it goes quietly vacuous** — the failure mode a tripwire can least afford.

If that tripwire ever fires, the fix is a second canonicalization rather than a re-plan: `printAst`'s `AstLet` case already flattens the chain into a list before rendering (`PPTools.hs:172-179`), so a topological sort with a deterministic tiebreak would normalize it — in the `loseRoudtrip = True` rendering only, since the `tlet`-lambda form prints the nesting literally. That is a contingency, not part of this PR.

### Success criteria this PR does not fully meet

- **V7 is a sanity bound, not a gate.** The two-pass printer renders twice and no longer streams; `CAFlessTest` doubles as a sequential benchmark, so a wall-clock regression would show, but no threshold is set and none of the printers is on a hot path.
- **E11's limit stands.** The inventory holds the *first* divergence of each diverging test, not every assertion inside it, and closing that would mean patching expectations one round at a time. Accepted: all sampled divergences classify identically across six build configurations.
