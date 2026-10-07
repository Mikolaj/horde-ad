# Haskell performance checklist

The checks to run on Haskell code for its performance, each with what
it catches, the case it came from, a recipe over horde-ad's `tools/` and how
to read what comes back; then the measuring conditions every timing assumes,
and the tools themselves. Distilled on 2026-10-07 from the orthotope work
of 2026-09-30 to 2026-10-07, whose figures the cases quote, and the home
of horde-ad's A/B rules and tool reference. A session reaches it through
the user-scope `haskell-perf-checklist` skill: asked to do the checklist
on a project, it runs the whole list as the next section says; asked for one
check by name ("check eta vs INLINE"), it runs that check's recipe rather
than composing one.

The tools the checks call resolve their arguments against the working directory,
so they run from any project's root as `python3 $T/NAME.py`
with `T=~/r/horde-ad/tools`, wherever the session's wrapper mounts
`~/r/horde-ad`.

## Running the checklist on a project

1. Resolve the project's root, the base the work is measured against (`master`
   or the branch's merge base), the compiler and the client modules
   that exercise the library, its tests and benchmarks. The compiler is GHC
   HEAD, `/home/mikolaj/r/horde-ad/ghc/_build/stage1/bin/ghc` with the project's
   HEAD configuration (orthotope's is `cabal.project.local.head`), unless
   the project's notes name another; a released GHC is built only where a check
   says so.
2. The static checks, which build nothing: W1, W3, W4, and the source halves
   of I1 and L1.
3. The dump builds of the tip and, where a check compares, of the base (D
   below), backgrounded.
4. The Core checks over those dumps: S1, S2, I1, I2, L1, L2 and C1, and the rule
   counts of F1 and F2.
5. The run-time checks, which need a criterion benchmark of the operations
   and the conditions of M: I3, F1, F2, A1 and W2, and any reading a Core check
   raised.
6. Report one verified line per check, naming what was run and what it found,
   or why it did not run. A check needing a GHC option the cabal file lacks
   waits for Mikolaj's approval of that option.

**D. The dump build.** One build feeds `spec-audit`, `pragma-calls`,
`core-diff`, `rules-diff`, `captured-unbox` and `ctime-diff`, each in a fresh
build directory, since cabal answers "Up to date" when only `-ddump-*` flags
change:

    cabal build all --enable-tests --enable-benchmarks -w GHC \
      --builddir=dist-dump-TIP --ghc-options="-ddump-simpl \
      -ddump-simpl-stats -ddump-timings -ddump-to-file -dsuppress-uniques \
      -dsuppress-idinfo"

Add `-ddump-dmd-signatures` for L1. Build it alone where C1 will read
its timings, and in horde-ad never beside another build of the test suites
or benchmarks. Dump flags change no code; `-g1`, `-ticky`, `-fspec-constr`
and the rest do, and are asked for one at a time.

## M. Before any reading

Not a check: the conditions every timing below assumes.

- **An A/B across two *builds* needs interleaving and controls, because
  recompilation itself moves numbers.** Two binaries differing by a one-line
  toggle shift *unaffected* benchmarks by +/-2--5% (code-layout/codegen noise;
  the artifact can be larger and need not shrink with size --- the `NotShared`
  prod benches run measurably slower on a build carrying a rule their `cgrad`
  pipeline never reaches, and that gap *grows* with product length, ~4%/15%/22%
  at 100/1000/10000, the three sizes those benches exist at, a per-iteration
  placement effect rather than a fixed small-scale one; a dead-rule-guard
  rebuild returns toward baseline but only weakly corroborates, the compiler
  being free to drop the always-false guard), and batched runs (all A, then all
  B) additionally confound with time/thermal drift. Run interleaved A/B pairs
  (drift cancels within a pair) and include per-pair controls: a suite
  the change provably cannot affect (e.g. the concrete `VTA` MNIST groups
  of `BenchMnistTools` for a `contractAst` change --- the concrete pipeline
  never runs it), and/or a change-independent variant (e.g. `S-exec-raw`
  for a `contractAst` change: the raw artifact is contraction-independent ---
  see the `vjpArtifact` cost fact in `.claude/rules/performance-model.md` ---
  so it is identical across the toggle). The change's effect is the target's
  per-pair ratio minus the control's.
- **An A/B also needs the same benchmark selection in every run compared,
  and its decisive numbers taken one benchmark per process: a predecessor's
  leftover RTS pool state can shift a follower's time ~7--10% at the `-A32m`
  horde-ad's suites run at, and did 22% at `-A1G`.** Interleaving and controls
  cannot catch it, both arms of a pair sharing their roster, and pinning alone
  is not sufficient when the compared builds change a predecessor's own
  allocation profile. Mechanism, evidence and the practical trade-offs
  are in `docs/position-effect.md`.
- Build what is timed through `tools/align-as.py`, from a fresh build directory,
  with
  `LOOP_MAXSKIP=1 LOOP_LOOKTHROUGH=1 LOOP_DEADSPOT=1 LOOP_EXITSPAN=1 LOOP_SETTLED=1`
  in the environment and `--ghc-options="-pgma $T/align-as.py -fforce-recomp"`.
  The shim needs no approval. It is the remedy for code placement: Mikolaj ruled
  reading which loops cross a cache line too simplistic a model to check by.
- Run `tools/machine-busy.sh` before timing. Time
  with `python3 $T/ab-time.py --cpu 3 BIN_A BIN_B ROUNDS NAME...`, reading
  allocation first. Back any time ratio that decides something
  with instructions, `python3 $T/perf-per-call.py --cpu 3 BIN_A BIN_B NAME N`,
  which code placement does not move.
- A time difference under about 10% decides nothing without instruction counts:
  an unchanged row's ratio ranged from 0.86 to 0.98 across pairs of builds.
- `-A32m`, and `-A4m` too where a library's users may run at the default area.
- Ask for every GHC option a benchmark or probe build adds beyond the cabal
  file's and the shim (`bench/CLAUDE.md`). Never `-fno-full-laziness`
  with `-fno-cse`, which GHC
  [#27886](https://gitlab.haskell.org/ghc/ghc/-/work_items/27886) miscompiles;
  keep iterations from sharing work by a NOINLINE `perturb i x` instead.
- Fusion and sharing can delete the work being measured: a `length` let fusion
  skip building the vector, a `take . generate` control fused, and four
  identical parts were computed once. Feed distinct inputs and consume the whole
  result.
- Allocation per element, from `getAllocationCounter` in a NOINLINE helper after
  a warm-up call (the first call allocates a 32 KB stack chunk), hides O(1)
  costs: a dictionary call per call vanishes at 200000 elements. Judge O(1)
  operations per call.

## S. Specialisation

### S1. Specialisation audit: does every hot call run specialised?

**Catches** client code that passes a class dictionary at run time, so
that the element type's methods are unknown calls. **Seen:** orthotope's
Storable and Unboxed modules exported specialisation rules keyed on the vector
type alone, the element's `VecElem` constraint, an associated type family,
staying abstract (`irred` in Core). Those rules sent clients' calls to copies
polymorphic in the element, and Storable `pad`'s fill took 43 times as long
an element as `toVector`'s. `index`, `scalar` and `unScalar`, without a pragma,
were called with `$fUnboxDouble` at run time, most of why Unboxed `rerank` took
2.2 times its control. `DynamicS.toVector`, without a pragma, was split
into a wrapper and a worker with no unfolding, which no client could specialise.

**Recipe**, over the tip's dump build:

- `python3 $T/spec-audit.py dist-dump-TIP --module CLIENT --ignore List`:
  the calls that hand a function an instance dictionary (`$fUnboxDouble`,
  `$fNumDouble`, ...), by callee, and the bindings that take a dictionary
  as a lambda argument (`$dVector`, `$dUnbox`, ..., and `irred`
  for a type-family constraint such as `VecElem v a`), CLIENT being what
  the tests' and benchmarks' modules' paths contain;
- first, the same run over a known positive, a module built `-fno-specialise`,
  so that its silence elsewhere means something;
- on each GHC of the support range, the project's specialisation test, where
  specialising depends on a flag one GHC defaults and another does not:
  `-fpolymorphic-specialisation` is on by default only on HEAD, and orthotope's
  boxed modules ran up to 8 times slower on 9.12.4 without it.

**Read:** set aside dictionaries that feed `Show`, error messages and the test
harness. Every other callee wants INLINE or INLINABLE, or a recorded reason
it cannot have one. `-fexpose-overloaded-unfoldings` does not stand in
for the pragma: a client specialises an imported function only if it is INLINE
or INLINABLE or the client is built `-fspecialise-aggressively`,
and the polymorphic worker ran 6 to 44 times slower in the fill's variant C.
Library code is the scope: a user's own unspecialised call is the user's to fix
in their Core.

**Keep** a test that fails when specialisation breaks, cheap enough for CI: one
shape and `Double`, every operation at every vector type, an allocation bound
against a module built `-fno-specialise` (orthotope's `BenchViewsTest`).

### S2. Specialisation copies: keyed on the types the work depends on

**Catches** copies per type the code does not depend on, and too few copies
where it does. **Seen:** Ranked `rotate`, INLINE over the ranks, made 48 copies
in one test module, INLINABLE one per rank pair, because the specialiser keys
on every type its constraints mention, `KnownNat` ranks included. Too few came
of the rules that `Dynamic`, `DynamicS` and `DynamicU` export for their own
`rotate`: they sent the boxed, Storable and Unboxed calls to three library
copies polymorphic in the element, where eight specialised copies were wanted
(GHC [#27873](https://gitlab.haskell.org/ghc/ghc/-/work_items/27873)).
A specialised worker with no unfolding cannot be specialised further, which
is what a partial specialisation of an INLINABLE function leaves (GHC
[#23050](https://gitlab.haskell.org/ghc/ghc/-/work_items/23050));
`ghc --show-iface MODULE.hi` shows whether a binding carries an unfolding,
and its arity.

**Recipe:** predict the count, call sites times the vector and element types
the client uses. Then count:
`python3 $T/core-diff.py dist-dump-TIP --module MODULE` lists every binding name
of the module with its count and terms,
and `python3 $T/core-diff.py dist-dump-BASE dist-dump-TIP --module MODULE`
those whose count differs between two builds.

**Read:** investigate a gap either way. The recorded fix for type-level keys
is an INLINE wrapper turning them into values over an INLINABLE worker
that specialises on the vector and element types alone.

## I. Inlining

### I1. Eta vs INLINE: calls too unsaturated to inline

**Catches** an INLINE function applied to fewer arguments than its definition's
left-hand side has, which GHC never inlines there; the client gets a specialised
copy, and a function argument stays an unknown call. **Seen:** `map toVector as`
in `concatOuter` and `ravel` left `$stoVector` copies in the client; a partly
applied `S.zipWithA (+)` left `$szipWithA`; a probe of `rerank2` measured
nothing until its INLINE copy was applied fully.

**Recipe:**

- Source: every INLINE name passed as an argument (`map f`, `foldr f`,
  a section, `f .`) or applied partly; read each.
- Core: `python3 $T/pragma-calls.py --inline dist-dump-TIP SRCDIR`, which marks
  each INLINE target CALLED where a module still calls it or its worker,
  and COPIED where a module made its own `$s` copy of it.
- Across a change:
  `python3 $T/rules-diff.py dist-dump-A dist-dump-B --unfolding NAME` counts
  the inlinings of NAME per module.

**Read:** each survivor is unsaturated, recursive (I2) or held back by a phase,
and is a lead to measure rather than a defect: eta-expanding the `map toVector`
sites, `map (\a -> toVector a) as`, gained nothing measurable, while inlining
`rerank2`'s wrapper took Storable `rerank2` from 1.64 to 1.02 times its control,
which needed INLINE in place of INLINABLE and its arrays moved into a lambda,
so that its calls saturate it.

### I2. INLINE on a recursive function

**Catches** an INLINE that blocks worker/wrapper on a self-recursive function,
its own loop breaker, which is never inlined anyway. Measured on GHC
10.1.20260918; the worker/wrapper and exposure behaviour checked 2026-09-27
on minimal modules and on horde-ad's interfaces: INLINE blocks worker/wrapper
even where it cannot be honoured, a self-recursive function staying the loop
breaker; INLINABLE does not, and moves its stable unfolding to the worker;
neither does NOINLINE, which moves to the worker and leaves the wrapper
inlinable only from the final phase. `-fexpose-overloaded-unfoldings`,
horde-ad's package default from 9.12 that some of its modules opt out
of in their headers, exposes every overloaded binding's unfolding, loop breakers
included; an exposed loop breaker is still never inlined, so all that exposure
or INLINABLE can buy there is cross-module specialisation.

**Recipe:** the targets
`python3 $T/pragma-calls.py --inline dist-dump-TIP SRCDIR` marks RECURSIVE,
binders of a `Rec {` group of their own module's Core. Functions recursing
through one another share a group and are marked together; a target whose worker
alone is recursive, worker/wrapper having run, is rightly not marked.

**Read:** INLINABLE or NOINLINE instead, or a non-recursive INLINE wrapper
over the recursive worker.

### I3. INLINE against INLINABLE: what each costs

**Catches** INLINE copying a large body into every call site, against what only
inlining gives. **Seen:** orthotope's fill, INLINE, was about half of a test
module's final Core. What only inlining gives, as met there:

- list fusion: `toListT` meets its consumer only when inlined (F1), so INLINABLE
  would lose it;
- vector's inplace rule, which needs the consumer to see the fill's `new`,
  though no orthotope call site gave it the chance;
- known function arguments: INLINABLE `reduce`, `rerank`, `rerank2`
  and `traverseA` were specialised but not inlined, leaving a thunk an element
  in `reduce` and 1.6 times the time on `rerank2`;
- a join point: a specialised copy met float-out before simplification,
  and a loop became a heap closure of 56 to 80 bytes a call (GHC
  [#27894](https://gitlab.haskell.org/ghc/ghc/-/work_items/27894)).

A top-level function with no unfolding, called per element or per conversion,
is the same question asked of NOINLINE.

**Recipe:** build both forms, dumps (D) and timed binaries (M).

- `python3 $T/core-diff.py dist-dump-A dist-dump-B` shows where the Core grows:
  in the importers, not the defining module.
- `python3 $T/ctime-diff.py dist-dump-A dist-dump-B` gives compile time against
  its controls.
- `python3 $T/rules-diff.py dist-dump-A dist-dump-B` shows any fusion lost.
- `ab-time.py` and `perf-per-call.py` time the benchmark.
- `python3 $T/ticky-diff.py A.txt B.txt` names a closure that appeared; it needs
  `-ticky`, so ask.

For a group of pragmas removed at once,
`python3 $T/pragma-calls.py DUMPS_A DUMPS_B WORKTREE_B` sorts them into DEAD
and MOVED before any bisection.

**Read** by the project's pragma rules: horde-ad's are in `CLAUDE.md`, Pragmas
and optimisation flags, and the worked method in `docs/pragmas-and-flags.md`.
GHC's `inline` at one call site is the per-site alternative to a pragma.

## F. Fusion

### F1. List fusion (foldr/build)

**Catches** a producer written `build`-style, `... cons nil`, whose consumer
never meets it, so that cells and boxes are built after all. **Seen:** `toListT`
fused per route, `fold/build` firing for each and `foldr/nil` for the empty
case, its guard and its case on the route notwithstanding. `maximumA` folded
by `foldr` over its producer, and `rerank` with `subArraysT` written
as a `build`, ran faster than before. `vConcatN` fuses with a `build` producer
and not with a recursive local function, and vector's `concat` walks its list
twice, so it fuses with none. A fused element walk can regress a route
it was not meant for: allocation rose 160 times on views of runs in one variant.

**Recipe:**

- In one build: `python3 $T/rules-diff.py dist-dump-TIP --module MODULE` lists
  the fusion rules that fired.
- Across a change: `python3 $T/rules-diff.py dist-dump-BASE dist-dump-TIP`,
  whose fusion rules are marked.
- Decide by allocation: a probe consumer such as `sum (toList a)`, run
  by `ab-time.py`, allocates nothing per element when fused. Measure every route
  of a dispatching producer.

**Read:** the producer must be INLINE (I3) and reach the consumer in one
expression. A count that falls may only have lost a duplicated consumer, so read
it against `core-diff.py`.

### F2. Vector stream fusion, and fusion that costs without SpecConstr

**Catches**, at the `-O1` that runs no SpecConstr:

- Chains expected to fuse that don't. Orthotope's operations never fused
  into one another, making its vector field lazy changing nothing,
  and a bounds-checked `slice` has no fusion rule.
- Fusion that lowers performance. A chain fused through `unsafeSlice`,
  `unsafeTake`, `take`, `tail`, `zipWith` or `enumFromN` allocated 16 to 64
  bytes an element. It took 1.9 to 3.7 times as long as storing the vector
  and summing it. All of it is gone at `-O2` or `-O1 -fspec-constr`.
- vector's own `map` and `zipWith` over stored vectors, allocating per element:
  a Storable `zipWith` of Doubles 112 bytes and an Unboxed one 72, against 64
  and 8 with SpecConstr.
- A `concat []` left with its copy loop, which SpecConstr would remove.

**Recipe:**

- Which vector rules fire in which module:
  `python3 $T/rules-diff.py dist-dump-TIP`, one build, or two builds against
  each other (`stream/unstream [Vector]`, `clone/new [Vector]`,
  `transform/unstream [New]`).
- In the source, the vector functions inside each chain that fires,
  and the callers of vector's `map`, `zipWith` and `concat` in hot code.
- A probe of each such chain at `-O1` and at `-O1 -fspec-constr` (ask), compared
  by `ab-time.py`, allocation first. What `-fspec-constr` removes
  is SpecConstr's cost, not a bug.

**Read:** where the project builds at `-O1`, a costly chain wants a form
that does not lean on SpecConstr. One such form is a `generate` over indices,
as in orthotope's Storable and Unboxed `vMap` and zips, marked as standing
in for SpecConstr (W1); if it gives up fusion, its comment says so or says why
not. `-fspec-constr` grew one test module's Core by 6 to 9%. Rewrite rules
at orthotope's API that would fuse its operations are refuted
(`.claude/rules/performance-model.md`).

## L. Laziness and strictness

### L1. Bangs

**Catches** an argument or binding the code forces anyway left lazy, its loop
then boxing or thunking. **Seen:** in 908, `allSameT`'s `x` had its bang dropped
for a reason a later guard removed. The binding stayed lazy, and the element
was unboxed again on every iteration once a client specialised it. A new Unboxed
min/max loop allocated more than vector's own until its reads were forced,
`let !x`.

**Recipe:**

- Bangs on some equations only, which leave the argument lazy, GHC keeping one
  demand per argument for the whole function:
  `python3 $T/bang-lazy-check.py SRC --dumps 'dist-dump-TIP/**/*.dump-dmd-signatures'`,
  after its `--selftest`.
- Bangs the base had and the tip dropped: `python3 $T/bang-drops.py OLD NEW`
  over two source trees.
- Unbanged bindings that a lambda, a section or a per-element combinator reads:
  `python3 $T/lazy-reads.py TREE`.
- After a change to pragmas or structure that a bang's reason leaned on: flip
  each bang alone, rebuild the dumps and run
  `python3 $T/core-diff.py dist-dump-A dist-dump-FLIP --verdicts` over every
  module. GHC's redundant-bang warnings are no evidence (GHC
  [#27862](https://gitlab.haskell.org/ghc/ghc/-/work_items/27862)).

**Read:** a bang changes semantics where an element may be boxed and undefined.
Force only unboxed elements there (vector's `elemseq`), or record the change
in the CHANGELOG.

### L2. Captured values unboxed per iteration, and lazy element reads and writes

**Catches:**

- A loop that scrutinises a `D#` or `I#` bound outside it, on every iteration.
  Seen: 908, `zipWithT`'s broadcast branches, and Unboxed `padT`'s padding
  value.
- An element read stored unevaluated, keeping its source alive and costing
  a thunk.
  - `VGM.unsafeWrite out o (VG.unsafeIndex v i)` writes a thunk, boxed
    and in dictionary-polymorphic Unboxed code;
    `VG.unsafeIndexM v i >>= VGM.unsafeWrite out o` does not.
  - A boxed `generate` stores thunks, which orthotope's `iotaT` avoids
    by building from an evaluated list.
  - Storable's element read is lazy ([vector issue
    570](https://github.com/haskell/vector/issues/570)), which W2 audits.

**Recipe:**

- `python3 $T/captured-unbox.py DUMP...` over the dumps of a client calling
  the library at concrete element types.
- In the source, `unsafeWrite` of an `unsafeIndex` read, and `generate` in boxed
  instances.
- Allocation per element in a probe. A thunk is looked for in compiled code
  and never in GHCi: GHCi showed boxed `iota` storing thunks where an `-O1`
  program showed values.
- Keep a test comparing a built vector's elements with the source's
  by `reallyUnsafePtrEquality#`, as orthotope's `prop_sameElems` does.

## A. Allocation shape

### A1. Closures and boxed state in loops

**Catches** a loop that is a heap closure where a join point was meant,
or that carries boxed state. **Seen:**

- #27894's floated copy (I3).
- Exitification leaving an exit lazy in boxed cursors. By GHC's boxity analysis
  that keeps the loop boxed, 16 bytes an element (GHC
  [#27893](https://gitlab.haskell.org/ghc/ghc/-/work_items/27893)).
- Full laziness floating a closed recursive join point to the top level (GHC
  [#13286](https://gitlab.haskell.org/ghc/ghc/-/work_items/13286)).
- vector-stream's zip state boxed per element at `-O1`.
- CPR lost for a sum type returned out of line. Also lost for a result that may
  be an existing boxed value: a heap check per element in `V.maximum`'s loop.

**Recipe:**

- `python3 $T/ticky-diff.py A.txt` lists one run's closures by allocation,
  and `python3 $T/ticky-diff.py A.txt B.txt` those whose allocation moved
  between two builds, from `+RTS -rFILE` runs at the same `--iters` of builds
  made with `-ticky` (ask).
- `core-diff.py --module` names a `$wgo` or `go` that appeared.
- In the dump, `letrec` where `joinrec` was meant, and `I#` or `D#` built
  in a loop's jumps.
- `perf-per-call.py` gives what it costs in instructions.

**Read:** prefer the smallest workaround that keeps a hand-written loop's shape,
its loops having been tuned for register allocation. A loop bound computed
from what the enclosing function binds kept `go` a join point.
`-fno-full-laziness` and `-fno-exitification` are flags to ask for, not fixes.
Mark the workaround with its issue (W1).

## W. Workarounds and their records

### W1. Every workaround names its cause

**Catches** code shaped around a compiler or library problem with no record
of which, so that nobody can remove it when the fix ships and is backported.
The accepted forms:

- the issue's URL at the code site, a GHC work item or a vector issue;
- "stands in for the SpecConstr that `-O1` leaves off", or for whichever flag
  it stands in for;
- "a workaround for an unidentified issue", where it is likely a performance bug
  and none is filed (Mikolaj's ruling of 2026-10-06).

Where a workaround gives something up by design, its comment says what,
as orthotope's instances say that no fusion is given up. **Seen:** a survey
of orthotope's comment blocks found blocks citing an issue, blocks standing
in for a flag, design notes, and a few hidden ones. One hidden block matched GHC
[#27737](https://gitlab.haskell.org/ghc/ghc/-/work_items/27737), filed
from that same loop, and now cites it.

**Recipe:** `python3 $T/workaround-cites.py SRC`, both directions at once:
the comment blocks that speak of a workaround and name no cause, each read whole
and set against the issue files of `docs/`; and each filed issue with the files
citing it, W2 finding the sites that hit an issue and cite nothing.

### W2. Code that hits a filed issue: the fix matrix

**Catches** the sites that hit a filed upstream issue, beyond those already
worked around. **Seen:** the Storable lazy read of vector issue 570 was worked
around in `equalT` and `compareT` alone. Built against vector with the issue's
fix, `traverseA`, `convert` to boxed and every consumer given an unknown
function allocated less. Every moved row landed on Unboxed's figure.

**Recipe:**

- Build the benchmark against the stock and the fixed dependency, the fix being
  a patched copy named by `packages:` in a project file, each at `-O1`
  and at `-O1 -fspec-constr` (ask).
- `python3 $T/ab-time.py --cpu 3 STOCK FIXED STOCK_SC FIXED_SC 2 NAME...` reads
  allocation per benchmark. The rows that move with the fix are the issue's
  sites. The probe must be a criterion benchmark, which is what `ab-time.py`
  runs.
- For a GHC issue with a local fix, build with the patched compiler.
  `python3 $T/core-diff.py dist-STOCK dist-FIXED --verdicts` names the modules
  it reaches.

**Read:** Mikolaj adopts a workaround only where it costs virtually nothing once
the fix ships and the user builds with SpecConstr. Unspecialised callers do
not count.

### W3. Unnatural tweaks not marked

**Catches** hand-tuned shapes that a reader would tidy back into the slow form:

- a loop written by index where a combinator exists;
- an argument order, or a `case` in place of `<>`;
- a cursor stepped twice, or a literal where the value would read better;
- `GHC.Exts` primitives, `lazy`, `oneShot`, `inline`, or NOINLINE on a helper;
- a bang's placement, a wrapper and worker split, or a route recognised again
  deep inside a fill.

Each wants a comment giving its measurement and its cause, or W1's
"unidentified". Orthotope's `genericFillStrided` says it re-derives `RRuns`,
a hack that lets each vector kind be tuned, in a system where some layouts
are routes and others are recognised deeper down.

**Recipe:**

- `git diff BASE -- '*.hs' | command grep -nE '^\+.*(GHC\.Exts|#\)|\blazy\b|oneShot|\binline\b|NOINLINE|unsafeIndexM|generate|unsafeWrite)'`.
- Then read every function the diff rewrote against its natural form. Code
  with no comment at all is what W1's tool cannot reach, and no tool tells
  a tweak from a design.

### W4. Flags added

**Catches** `OPTIONS_GHC`, `ghc-options` or project-file flags added without
Mikolaj's approval, or without a comment saying why and for which GHCs.

**Recipe:**
`git diff BASE -- '*.hs' '*.cabal' 'cabal.project*' | command grep -nE '^\+.*(OPTIONS_GHC|ghc-options|-f[a-z]|-O[0-9])'`.

**Read:** never `-fno-full-laziness` with `-fno-cse` (#27886). Take `-O2`'s
constituents, never the bundle.

## C. Compile time

### C1. Core bloat: where the copies come from

**Catches** a function copied far more often than the work needs. **Seen:**

- an INLINE body at every call site (I3);
- a specialisation per type that does not matter (S2);
- floated duplicates that CSE leaves unmerged: GHC
  [#27892](https://gitlab.haskell.org/ghc/ghc/-/work_items/27892) left 80 copies
  of `concat []` per element type in one test module.

**Recipe:** predict first, then compare the prediction with the dump and adjust
the model to it. The prediction is call sites, times type combinations, times
the body's terms.

- `python3 $T/core-diff.py dist-dump-TIP --module MODULE` gives the copies
  by name, with their terms.
- `python3 $T/one-shot.py LOG MODULE OUTDIR -- FLAG...` compiles the worst
  module alone under a flag.
- `python3 $T/src-attrib.py DUMP SRCDIR` credits a `-g1` dump's code to source
  definitions. Ask for `-g1`, which changes what GHC floats, so it locates code
  and does not predict savings.
- `ctime-diff.py` and `core-diff.py` compare two builds, each made alone.

**Read:** by the project's pragma rules (I3).

## The tools

Scripts under `tools/` measure a difference between two builds and take
it from "something moved" to the function or module that moved it, and the last
two of its list concern where loops happen to land: `align-as.py` keeps it out
of that difference and `loop-offsets.py` reads it off a binary. Each
of the others has a `--self-test` and exits 2 rather than 0 when its run did
not happen, so that a build made without the needed flags cannot read as one
where nothing changed. `docs/overloaded-unfoldings.md` shows `ab-time`,
`cachegrind-per-call`, `ticky-diff` and `core-diff` in use,
and `docs/pragmas-and-flags.md` `pragma-calls`.

- `tools/ab-time.py` runs the A/B procedure of M as a script over two or more
  builds' benchmark executables: interleaved rounds, the order rotated
  from round to round, one benchmark per process, optionally pinned to one CPU,
  and for each build after the first the median of its per-round ratios
  of criterion's time slope to the first's, beside both builds' allocation per
  iteration. Single pairs on a loaded or virtual machine scatter far more
  than the effect under test --- 0.42 to 1.36 around a true 1.00 in that study
  --- so read only the median, and only after allocation has been compared.
- `tools/perf-per-call.py` gives instructions and cycles per call of one
  benchmark in each of several builds, from `perf stat` runs at `--iters 2N`
  and `--iters N`, interleaved, rotated and optionally pinned, with the median
  of a few repetitions. Its instruction counts back a wall-time ratio
  as cachegrind's do, at native speed; its cycles carry the machine's noise.
- `tools/cachegrind-per-call.py` gives instructions and estimated cycles per
  call of one benchmark, from cachegrind runs at `--iters 2N` and `--iters N`,
  for a machine where `perf stat` cannot run. It is deterministic, so it is what
  backs a wall-time ratio that decides whether a change is banned; in that study
  it showed wall-time medians of 1.05 to 1.06 to be noise, the instruction
  counts equal to 0.003%.
- `tools/ticky-diff.py` diffs the per-closure allocation of two ticky-ticky runs
  of one benchmark, closure names normalised across builds. Build both
  with `--ghc-options=-ticky` and run the same `--iters` with `+RTS -rFILE`.
  It is how a whole allocation difference was pinned on one function,
  `astTimesK`, in one step. Given one run, it lists its closures by allocation
  (A1).
- `tools/core-diff.py` compares two builds' optimised Core module by module,
  from `-ddump-simpl -ddump-to-file -dsuppress-uniques` dumps in two build
  directories or `-dumpdir` trees: bindings and terms per module;
  the specialisations and workers a module has in one build and not the other,
  with their terms where the dumps keep the size comments
  of `-dsuppress-idinfo`; or a verdict per module, the Core the same, the same
  but for unboxed literals, or different. Compile-time cost lands in the modules
  that specialise an exposed function, not in the module that exposes it,
  so this --- not timing the module --- is how to see where a flag or pragma
  puts its cost. Given one build and `--module`, it lists every binding name
  of the modules matched, with its count and terms (S2, C1).
- `tools/pragma-calls.py` sorts the inlining pragmas a worktree's diff removes
  by whether their removal changed the Core, counting each target's name per
  module in two builds' dumps: DEAD where every count agrees, MOVED
  with the modules that differ. It is the step between removing a whole group
  of pragmas and bisecting it. DEAD is weaker than identical Core, and does
  not make a pragma removable: the threshold rule in `CLAUDE.md` keeps it.
  With `--inline` it reads one build instead, marking each INLINE target
  of a source tree CALLED, COPIED or RECURSIVE (I1, I2).
- `tools/rules-diff.py` compares which rewrite rules fired per module in two
  builds, from `-ddump-simpl-stats` dumps, the fusion rules marked,
  and with `--unfolding NAME` how often a function was inlined. It answers
  whether what fused still fuses; a fusion count can fall only because
  a duplicated consumer went, so read a drop against `core-diff`. Given one
  build, it lists the fusion rules that fired (F1, F2).
- `tools/ctime-diff.py` compares two builds' compile time and GHC allocation per
  module, from `-ddump-timings` dumps beside the Core dumps, the modules whose
  Core is the same in both serving as controls whose time ratios are the noise
  of the run. On one pair of orthotope builds whose Core shrank by 2.3%,
  the time ratio was 1.005, inside the controls' 1.004 to 1.114,
  and the allocation ratio 0.978, the steadier measure.
- `tools/one-shot.py` recompiles one module of a finished build alone, flags
  added, from the arguments a `cabal build -v2` log records, reading the build's
  interfaces and writing none of its files: a module's Core under a flag,
  or with its call sites edited, for the price of that module's compilation.
- `tools/src-attrib.py` credits the code of a `-g1` Core dump to the source
  definitions its innermost source notes name, and compares two dumps so.
  It shows where a module's code came from, but on the module it was tried
  on `-g1` changed what GHC floated and duplicated, so it does not predict what
  a pragma saves: build the change and compare with `core-diff`.
- `tools/align-as.py` stands in for the assembler,
  as `--ghc-options="-pgma $PWD/tools/align-as.py -fforce-recomp"`, and aligns
  loop heads to a cache line, which GHC's native backend never does, so that two
  builds compared do not differ by where their hot loops happen to straddle one.
  A build uses it, or an edited copy of it, only from a fresh `--builddir`,
  an existing one keeping its object code whether or not `-fforce-recomp`
  is passed. `LOOP_*` variables choose the placement; its docstring describes
  each, and what orthotope's micro-regime3 benchmark, where it was written,
  measured of the forms they build; its cases are in `tools/defects.json`,
  and it exits with the real assembler's status, or 1 on a setting it refuses.
- `tools/loop-offsets.py` finds a binary's copies of a hot loop structurally,
  by a backward branch and the bytes it spans, groups them by their bytes
  and says where each lands in its cache line, so that a margin between two
  builds can be checked for being one of them placing a loop astride a line
  where the other did not: on micro-regime3 a straddled copy of one 28-byte loop
  was priced at 1.19 against a resident one. `--survey` counts every loop up
  to a line long and the straddlers among them, `--delta` reads how far
  a rebuild moved the tracked loops, and `--match` names a binary's straddlers
  off its `-g3` twins; its cases are in `tools/defects.json`.

The tools written for the checks of one build or one source tree,
`tools/spec-audit.py`, `tools/bang-drops.py`, `tools/lazy-reads.py`,
`tools/captured-unbox.py` and `tools/workaround-cites.py`, exit 0 clean, 1
with findings and 2 when the run did not happen, as `pragma-calls.py --inline`
does; `tools/bang-lazy-check.py`, without `--allow`, exits 0 whatever
it printed, its candidates being for the reader.

- `tools/spec-audit.py` lists the calls in optimised Core that hand a function
  an instance dictionary, by callee, and the bindings that take a dictionary
  as a lambda argument: code running unspecialised (S1).
- `tools/bang-lazy-check.py` flags an argument banged on some equations
  of a definition and left unforced on another, and checks each against GHC's
  demand signatures (L1).
- `tools/bang-drops.py` lists the bangs a later version of a source tree dropped
  (L1).
- `tools/lazy-reads.py` lists the unbanged bindings that a lambda, a section
  or a per-element combinator reads (L1, L2).
- `tools/captured-unbox.py` finds the loops that unbox, on every iteration,
  a value captured from outside them (L2).
- `tools/workaround-cites.py` lists the comment blocks that speak
  of a workaround and name no cause, and each filed issue of `docs/`
  with the files citing it (W1).
