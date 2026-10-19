# Haskell performance checklist

The checks to run on Haskell code for its performance, each with what
it catches, the case it came from, a recipe over horde-ad's `tools/` and how
to read what comes back; then the measuring conditions every timing assumes,
the rules for pragmas and flags, and the tools themselves. Distilled
on 2026-10-07 from the orthotope work of 2026-09-30 to 2026-10-07, whose figures
the cases quote, and the home of horde-ad's A/B rules, pragma and flag rules
and tool reference. A session reaches it through the user-scope
`haskell-perf-checklist` skill: asked to do the checklist on a project, it runs
the whole list as the next section says; asked for one check by name ("check eta
vs INLINE"), it runs that check's recipe rather than composing one.

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
2. The static checks, which build nothing: A2, I4, W1, W3, W4, and the source
   halves of I1, L1 and A3.
3. The dump builds of the tip and, where a check compares, of the base (D
   below), backgrounded.
4. The Core checks over those dumps: S1, S2, I1, I2, L1, L2, B1, B2 and C1,
   and the rule counts of F1 and F2.
5. The run-time checks, which need a criterion benchmark of the operations
   and the conditions of M: I3, F1, F2, A1, A3, B1's allocation, B2's ranking
   and W2, and any reading a Core check raised.
6. Report one verified line per check, naming what was run and what it found,
   or why it did not run. A check needing a GHC option the cabal file lacks
   waits for Mikolaj's approval of that option.

**D. The dump build.** One build feeds `spec-audit`, `pragma-calls`,
`core-diff`, `rules-diff`, `captured-unbox`, `box-audit` and `ctime-diff`, each
in a fresh build directory, since cabal reports "Up to date" when only
`-ddump-*` flags change:

    cabal build all --enable-tests --enable-benchmarks -w GHC \
      --builddir=dist-dump-TIP --ghc-options="-ddump-simpl \
      -ddump-simpl-stats -ddump-timings -ddump-to-file -dsuppress-uniques \
      -dsuppress-idinfo"

Add `-ddump-dmd-signatures` for L1 and `-ddump-cpr-signatures` for B1's results.
Build it alone where C1 will read its timings, and in horde-ad never beside
another build of the test suites or benchmarks. B2 runs `loop-reloads`
over this build with `-ddump-asm` added and `-dsuppress-uniques` dropped,
in a build directory of its own, `dist-asm-TIP`: under that flag no call's
return point is named, and the tool exits 2. Dump flags change no code; `-g1`,
`-ticky`, `-fspec-constr` and the rest do, and are asked for one at a time,
`-ticky` excepted (Mikolaj's ruling of 2026-10-16).

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
  in the environment and `--ghc-options="-pgma $T/align-as.py -fforce-recomp"`,
  and nothing else, orthotope's specialisation benchmark allocating alike
  with and without it. It plans slowly, orthotope with its benchmark and probes
  being the most it builds in reasonable time, so ox-arrays and horde-ad
  are timed without it. It is the remedy for code placement: Mikolaj ruled
  reading which loops cross a cache line too simplistic a model to check by.
- Run `tools/machine-busy.sh` before timing. Time
  with `python3 $T/ab-time.py --cpu 3 BIN_A BIN_B ROUNDS NAME...`, reading
  allocation first. Back any time ratio that decides something
  with instructions, `python3 $T/perf-per-call.py --cpu 3 BIN_A BIN_B NAME N`,
  which code placement does not move.
- A time difference under about 10% decides nothing without instruction counts:
  an unchanged row's ratio ranged from 0.86 to 0.98 across pairs of builds.
- An instruction count decides only at the cells it counts: count the large size
  and every view the change's code takes, a cost having twice gone unseen
  at the cells left out. Read gains and costs at one threshold, reporting
  a ratio exactly at it; check a counting tool's verdict on one row before
  counting its list; and read a stage's tests line before its counts.
- A count differencing N and 2N calls spans few calls at a large size,
  and an old-generation collection falling between them in one build and
  not the other moved one cell by 6M instructions a call, at `-A4m`: recount
  such a cell over ten times the calls before reading it.
- `-A32m`, and `-A4m` too where a library's users may run at the default area.
- `GHCRTS=-V0`, which stops the RTS clock, on every timed or counted process
  of horde-ad or orthotope; `ab-time.py`, `perf-per-call.py`,
  `cachegrind-per-call.py` and the launching scripts at the top of orthotope's
  `micro-regime3` set it themselves. With the clock running, some processes
  of a HEAD-built `shortProdForCI` carried 56M instructions more than the rest.
  Set it per command or in a measuring script, never session-wide, since
  a program linked without `-rtsopts`, stylish-haskell among them, exits 1
  under it. Profiles are the exception: under it a cost-centre profile recorded
  no ticks, and a `-hT` heap profile 3 samples where it took 12 without.
- Ask for every GHC option a benchmark or probe build adds beyond the cabal
  file's (`bench/CLAUDE.md`). Never `-fno-full-laziness` with `-fno-cse`, which
  GHC [#27886](https://gitlab.haskell.org/ghc/ghc/-/work_items/27886)
  miscompiles; keep iterations from sharing work by a NOINLINE `perturb i x`
  instead, whose result depends on `i`: one ignoring `i` let 2000 iterations
  share one call, allocating barely more than 100 did.
- Fusion and sharing can delete the work being measured: a `length` let fusion
  skip building the vector, a `take . generate` control fused, and four
  identical parts were computed once. Feed distinct inputs and consume the whole
  result.
- Allocation per element, from `getAllocationCounter` in a NOINLINE helper after
  a warm-up call (the first call allocates a 32 KB stack chunk), hides O(1)
  costs: a dictionary call per call vanishes at 200000 elements. Judge O(1)
  operations per call.
- Check by coverage that a benchmark takes every path of an operation
  it is meant to measure: build it `-fhpc`, run it, combine its runs' tix
  with `hpc combine` and read their `hpc draft` through `tools/hpc-untaken.py`.

## P. Pragmas and flags: the rules

Not a check: the rules by which a verdict on an inlining or specialisation
pragma (`INLINE`, `INLINABLE`, `NOINLINE`, `SPECIALISE`, phase control) or
on an optimisation flag is read, kept here and nowhere else. Which half below
holds is settled module by module, by whether a caller can specialise
the module's overloaded functions without a pragma: it can where the module
is built `-fexpose-overloaded-unfoldings` and the caller
`-fspecialise-aggressively`, and otherwise, small functions aside, only through
`INLINE` or `INLINABLE`. horde-ad builds `-fspecialise-aggressively` throughout
and `-fexpose-overloaded-unfoldings` from GHC 9.12, some of its modules opting
out of the latter in their headers, so it has modules under each half. A library
whose users build as they please, orthotope among them, is under the second half
throughout, its own flags reaching no user's build.

### Common principles

- **What is traded:** run time against compile time --- that of the project's
  own optimised build, every component with exactly the flags of its `.cabal`
  file, and for a library that of its users' builds too, which its `INLINE`
  and `INLINABLE` bodies land in; the dependencies' build time does not count.
  A change that improves the trade without costing speed is welcome, one
  that only speeds compilation included, such as a pragma removed or a module's
  `-fno-expose-overloaded-unfoldings`. A light compile-time cost is acceptable
  for a large speed gain, but a speed cost never is for faster compilation,
  except in code whose speed the project names as tradable. horde-ad names
  simplification: the smart constructors, the traversals, vectorisation,
  inlining, and building and simplifying artifacts. It protects computing
  on concrete values: interpretation, `interpretAst` and every primitive
  it calls, the `Concrete` instances, and all AD that never builds an AST,
  the non-symbolic pipeline (`cgrad`, `cvjp`, `cjvp` and their `2` variants)
  with the `ADVal` instances, the delta expressions they record and their
  evaluation in `Core/DeltaEval.hs`; none of it may get slower than the state
  the work started from.
- **Noise margins** (Mikolaj's ruling of 2026-10-10): a change counts above 2%
  on a wide benchmark, an end-to-end suite or a test suite of fixed inputs,
  never one of QuickCheck properties, whose arguments change from run to run,
  and above 10% on a narrow one, a micro-benchmark of one function, or
  on a noisy reading, one that cannot distinguish 10% from nothing, as wall time
  and estimated cycles are on a busy machine or in the cloud, though not
  on a lightly loaded one here. Allocation, exact within one build, moved up
  to 1.5% between builds under unrelated edits. It is screened first,
  but a change in evaluation rather than allocation is priced in instructions:
  removing `-fworker-wrapper-cbv` left every allocation figure but one unchanged
  and cost up to 3.8% in instructions. Exact counts are the exception (Mikolaj's
  ruling of 2026-10-16): the margins bind time and readings that drift between
  builds, while an exact count of one build, of instructions or of allocation
  at a row, decides at any size once its move is explained, in Core or
  in the machine code.
- **A call's result forced and consumed** (Mikolaj's ruling of 2026-10-15):
  where a benchmark reads a call both with its result forced to normal form
  and with it consumed as a client would, as orthotope's specialisation
  benchmark does under `--summed`, the two readings have equal standing in every
  decision, and a tie between them that cannot be broken goes to the consumed
  one.
- **Which representation counts most** (Mikolaj's ruling of 2026-10-15): a tie
  between the figures of Storable, Unboxed and boxed arrays that cannot
  be broken goes to Storable, then to Unboxed.
- **Which GHCs count** (Mikolaj's rulings of 2026-10-11): a GHC older than 9.12
  decides nothing, neither by a measurement nor by the half its modules fall
  under. HEAD's measurements carry 80% of a decision, those of the released GHCs
  from 9.12 on the other 20%.
- **What a pragma buys** is each check's rule, stated in the check: `INLINE`
  against `INLINABLE` I3's, a fusion path F1's, a value never to be built A3's,
  a call too unsaturated to inline I1's, a recursive function I2's, type-level
  keys in the constraints S2's, a `NOINLINE` on a helper W3's, a flag W4's. One
  kind is no check's: a phase control, `INLINE [n]`, that orders inlining
  against rewrite rules, or against specialisation that has to happen in code
  that is then inlined, stays for that order even where plain `INLINE` would
  cost less. horde-ad's `tscatterZRDict` and `tscatterZSDict` carry `INLINE [1]`
  and an explicit dictionary argument so that GHC specialises the inlined code
  consistently at each element type, though plain `INLINE` would save 2%
  of the Core.
- **Removing a pragma:** not one that is dead only at today's thresholds,
  an `INLINE` on a function GHC inlines anyway or a `NOINLINE` on one it would
  not inline, since the thresholds can change; this binds only where the pragma
  could matter once a threshold, such as the one for exposing unfoldings,
  is lowered (Mikolaj's ruling of 2026-10-16), which the `INLINABLE`s taken off
  orthotope's `unravel` wrappers, `HasCallStack` alone in their contexts, could
  not. Remove such a pragma only when removing it changes the optimised Core
  and measurements show that what it did buys nothing, on the GHCs that count,
  weighed as above: without an `INLINE` that did nothing measurable on GHC
  9.14.1, some benchmarks allocated up to 43% more on HEAD. Measure the removal
  at the benchmarks' smallest sizes too, empty included, where a cost paid once
  a call is not lost among those paid per element. The census is a fixed point
  over the pragmas and their notes: run it on the tree being changed, after
  every change to the pragmas kept or their notes, and before measuring;
  an `INLINE` the rule requires, on a forwarder, a thin wrapper or on a binding
  F1's recipe or A3 confirms, is not released on a measurement.
- **Local bindings** (Mikolaj's ruling of 2026-10-18): a binding in a `where`
  or a `let` takes `INLINE` wherever these rules give it to a top-level binding
  and is held to nothing else in them: no rule here takes its `INLINE` away
  or requires a comment for it, such pragmas being needed far more often
  in local bindings than at top level, and often measured.
- **Measuring a pragma change:** a pragma added, removed or changed is measured
  with the binding's calls in I1's terms, point-free and with its arguments
  named, and with the library's own calls of it as written and all saturated
  where these differ; the form taken is the best of them.
- **Measuring compile time:** each build alone, in a fresh `--builddir`,
  on an otherwise idle machine, without `jobs` or `semaphore`
  in `cabal.project.local`, which skew build times; read the two per module
  with `ctime-diff.py`, whose modules of unchanged Core give the run's noise.
  A flag's build cost moves with the Core it works on: one cost 17% of a build
  and nothing measurable once a group of pragmas had gone, so price it on top
  of the pragmas it will live with.

`docs/pragmas-and-flags.md` records one application of these rules, to horde-ad.

### With `-fexpose-overloaded-unfoldings`

Callers built `-fspecialise-aggressively` specialise every overloaded function
of such a module from its exposed unfolding, so a pragma there buys what
inlining or a phase gives and, for `INLINABLE`, the unfolding taken before
the module's own optimisation rather than the optimised one, which escaped GHC
[#27893](https://gitlab.haskell.org/ghc/ghc/-/work_items/27893)'s boxed loop.

- **A pragma is a cost in itself:** visual noise, counted against a change
  in any trade-off. Where one module-level flag does what a dozen pragmas do,
  the flag wins. When a pragma proves beneficial, add similar ones only where
  each pays for itself individually, never across the board.

### Without `-fexpose-overloaded-unfoldings`

A caller specialises an overloaded function of such a module only
if the function is `INLINE` or `INLINABLE`, or small enough for GHC to expose
its unfolding automatically; otherwise each call passes it the dictionaries
at run time. Exposing a module's overloaded unfoldings stands in for the pragma
at callers built `-fspecialise-aggressively`, which a library cannot detect
in its users. At callers built without it, exposure did for a function GHC
derived from an `INLINABLE` one, the partial specialisation of GHC
[#23050](https://gitlab.haskell.org/ghc/ghc/-/work_items/23050), and
not for orthotope's fill, which had no pragma at all (S1's variant C).

- **Where the callers' speed is protected, a binding needs `INLINE` where
  inlining alone gives it something**: its type takes an argument of function
  type, which inlining makes a known call; it is directly fusing (F1); its type
  takes or returns a sum marked as never to be built, which inlining lets
  the caller take apart unbuilt (A3); or a measurement shows another of I3's
  gains. **A binding that forwards to one needing `INLINE` needs it too**:
  its body calls that binding, directly or through a class method one of whose
  instances it is, and passes it the function or the list of its own type
  that makes the callee need it, or, where the callee's `INLINE` stands
  on a measured gain rather than on fusion, a marked sum or a function argument,
  wraps it, the call heading its body, so that the gain reaches the caller
  through every link. **So does a thin wrapper**, a binding whose right-hand
  side is constructors, newtype fields, `coerce`, `$` and `.` around at most one
  call: the thin wrappers whose release cost nothing at GHC's default thresholds
  were mostly ones GHC inlined anyway, and with the package's own modules built
  `-funfolding-creation-threshold=30`, where it no longer does, some
  of orthotope's were left out of line and cost up to a kilobyte a call.
  That threshold is not to be used for benchmarking again (Mikolaj's ruling
  of 2026-10-13): it also stops base's functions, `all` among them, from being
  inlined into the `INLINE` unfoldings a module stores, inhibiting their
  simplification, so a build at 30 is a different program even where every
  `INLINE` is kept. A recursive binding takes a non-recursive `INLINE` wrapper
  over it instead (I2). **Otherwise a binding gets `INLINABLE` where
  it is overloaded**, by a class constraint in its signature, in its instance's
  context or in its class method's own type, `HasCallStack`, equalities,
  `TypeError` and type-level comparisons not counting, **and otherwise
  no pragma**. A need for `INLINE` that the type does not show, or shows only
  through a marked sum, a forwarder's and a thin wrapper's aside, and any
  departure from this, stands only under a plain comment directly above
  the binding's haddock whose first line opens with the pragma the binding
  carries, or `No pragma`, and a colon, as in `-- INLINE:`, and which cites
  the measurement or reading behind it: the check that took it, one of I1, I2,
  I3, F1, A3, S2, W3 and W4, a GHC version, HEAD included, with the date
  it was taken, or `see` and the comment that does; a commit message does
  not count. A declaration does it in bulk: a comment saying
  `INLINE throughout`, `INLINABLE throughout` or `No pragma throughout`,
  with its reason, covers each binding carrying that pragma, or none,
  in the module whose header holds it or among the methods of the instance
  or class it stands directly above, where it overrides the module's. After
  a `but` it names every binding there that carries another pragma,
  `INLINE throughout but rotate and window:`, and their reasons go in it too:
  a binding it names is held to this rule, and to the declaration's citation
  or its own comment. `INLINE throughout` suits a layer whose callers
  are `INLINABLE`, as I3 allows. I4 checks a tree against this.
- **Where their speed is tradable,** a pragma is a trade like any other and pays
  for itself or goes, as in the half above. Opting a module out
  of `-fexpose-overloaded-unfoldings` is itself such a trade: compile time saved
  where specialisation buys nothing, as horde-ad measured of its opt-out modules
  (`docs/overloaded-unfoldings.md`).
- **A removal shows in a caller's Core, not in the module's own:** the removing
  rule above reads the dumps of the project's tests and benchmarks, or
  of a probe client.

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
- on HEAD and each released GHC from 9.12 on, the project's specialisation test,
  where specialising depends on a flag one GHC defaults and another does not:
  `-fpolymorphic-specialisation` is on by default only on HEAD, and orthotope's
  boxed modules ran up to 8 times slower on 9.12.4 without it;
- where the question is boxing as a whole, B1, which runs this audit as one
  of its steps.

**Read:** set aside dictionaries that feed `Show`, error messages and the test
harness. Every other callee needs what P requires of its module, a pragma where
the callers cannot specialise without one: the polymorphic worker ran 6 to 44
times slower in the fill's variant C. A class method can need more: on GHC
9.12.4 a client called orthotope's INLINABLE `vUnsafeFillStrided`, a method
constrained by `VecElem`, unspecialised through the generic apply, 16%
at Dynamic's small strided Storable `force`, which an INLINE method forwarding
to a top-level INLINABLE function took back. Library code is the scope: a user's
own unspecialised call is the user's to fix in their Core.

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
copies polymorphic in the element, where eight specialised copies were needed
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
is an INLINE wrapper turning them into values over a worker that specialises
on the vector and element types alone, `INLINABLE` where P's second half holds.

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

**Read:** each survivor is unsaturated, recursive (I2), held back by a phase
or in a boring context --- its arguments variables GHC has no information
on and its result returned or stored as it is, where GHC by design inlines only
a tiny INLINE body, as at `padT`'s `toVectorListT sh t` with no padding
requested --- and is a lead to measure rather than a defect: eta-expanding
the `map toVector` sites, `map (\a -> toVector a) as`, gained nothing
measurable, while inlining `rerank2`'s wrapper took Storable `rerank2` from 1.64
to 1.02 times its control, which needed INLINE in place of INLINABLE
and its arrays moved into a lambda, so that its calls saturate it.

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
over the recursive worker; or no pragma on a monomorphic function, which
INLINABLE has nothing to specialise. Such an INLINE is dead at every threshold,
so P's rule on removing pragmas dead at today's does not keep it: dropping
orthotope's on `getStridesT` changed its callers' Core only in the line numbers
call stacks quote.

### I3. INLINE against INLINABLE: what each costs

**Catches** INLINE copying a large body into every call site, against what only
inlining gives. **Seen:** orthotope's fill, INLINE, was about half of a test
module's final Core. What only inlining gives, as met there:

- list fusion: `toListT` meets its consumer only when inlined (F1), so INLINABLE
  would lose it;
- vector's inplace rule, which needs the fill's `new` visible to the consumer,
  though no orthotope call site gave it the chance;
- known function arguments: INLINABLE `reduce`, `rerank`, `rerank2`
  and `traverseA` were specialised but not inlined, leaving a thunk an element
  in `reduce` and 1.6 times the time on `rerank2`;
- a join point: a specialised copy met float-out before simplification,
  and a loop became a heap closure of 56 to 64 bytes a call, with 8 more
  in the closure capturing it (GHC
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
  a `-ticky` build.

For a group of pragmas removed at once,
`python3 $T/pragma-calls.py DUMPS_A DUMPS_B WORKTREE_B` sorts them into DEAD
and MOVED before any bisection.

**Read:** `INLINE` only for what inlining alone gives, the list above; otherwise
the pragma P's half requires, `INLINABLE` where a caller needs one to specialise
and none where it does not. An `INLINE` body whose callers are all `INLINABLE`
is copied once per type, into their specialised copies, not at every call site,
so such a layer can be `INLINE` throughout. The trade is weighed by P. GHC's
`inline` at one call site is the per-site alternative to a pragma.

### I4. Pragma by P's rule: does each binding carry the pragma P gives it?

**Catches** a binding whose pragma differs from what P's rule gives it
with no comment saying why: one missing, one superfluous or one of the wrong
kind, a forwarder's and a thin wrapper's included. **Seen:** orthotope's boxed
`fmap`, `foldr` and `traverse` forwarded a caller's function to `mapA`, `foldrA`
and `traverseA` with no pragma, and the list instance of `Vector` took function
arguments with none. Acting on every finding of orthotope's tree at once, before
its fusing bindings were marked, stripped `INLINE` from `toListT`'s wrappers
and ran `toList` 8 to 10 times slower (2026-10-11).

**Recipe:**

- Mark before acting on any finding: mark the types meant never to be built
  (A3); give each binding listed as directly fusing with no F1 comment
  its comment in P's form once F1's recipe shows the fusion firing, each binding
  listed as taking or returning a marked sum its comment naming the sum
  and citing A3, and each `INLINE` that stands on a measured gain its comment
  citing the measurement; then run the census again. The forwarders follow only
  from bindings so found, so a finding acted on before the marking can strip
  `INLINE` from a fusing binding's wrappers.
- `python3 $T/pragma-census.py --rule SRC` lists every top-level function
  with a signature, every instance method and every class default method whose
  pragma differs from P's rule with no comment above its haddock in P's form
  and no declaration covering it, the recursive bindings the rule would make
  `INLINE`, the methods of classes whose method types it cannot determine,
  the bindings whose comment names F1 but which pass their list to a tree
  binding, the innermost being the one to carry it, the directly fusing bindings
  with no comment in P's form citing F1, the bindings taking or returning
  a marked sum with no comment in P's form naming it and citing A3, and each
  declaration whose `but` leaves out a binding of another pragma in its scope
  or names one it should not. It lists no local binding, so one lacking
  an `INLINE` P gives it is found by reading.
- `python3 $T/pragma-census.py --write SRC` writes into a tree under P's second
  half each pragma the rule adds or strengthens, round after round until
  the census requires none more; with `--release` it weakens and removes them
  too, but for the findings a `--keep` file lists, building the tree on which
  a removal is measured.
- `python3 $T/pragma-census.py SRC` lists only the overloaded bindings
  that carry no pragma.
- S1's audit shows which callers still pass a dictionary at run time.

**Read:** by P: settle each finding by changing its pragma, an existing one
as P's rule on removing pragmas says, or by writing the comment P requires.
The rule binds only a module under P's second half, where its callers' speed
is protected; elsewhere a finding is a candidate, a pragma there paying
for itself or going.

## F. Fusion

### F1. List fusion (foldr/build)

**Catches** a producer written `build`-style, `... cons nil`, whose consumer
never meets it, so that cells and boxes are built after all. **Seen:** `toListT`
fused per route, `fold/build` firing for each and `foldr/nil` for the empty
case, its guard and its case on the route notwithstanding. `maximumA` folded
by `foldr` over its producer, and `rerank` with `subArraysT` written
as a `build`, ran faster than before. `vConcatN` fuses with a `build` producer
and not with a recursive local function, and vector's `concat` walks its list
twice, and its `fromList` and base's `maximum` take theirs apart by `case`,
so none of them fuses. A fused element walk can regress a route it was not meant
for: allocation rose 160 times on views of runs in one variant.

**Recipe:**

- In one build: `python3 $T/rules-diff.py dist-dump-TIP --module MODULE` lists
  the fusion rules that fired.
- Across a change: `python3 $T/rules-diff.py dist-dump-BASE dist-dump-TIP`,
  whose fusion rules are marked.
- Decide by allocation: a probe consumer such as `sum (toList a)`, run
  by `ab-time.py`, allocates nothing per element when fused. Measure every route
  of a dispatching producer.

**Read:** a binding is directly fusing when its own body holds the `build`
or `augment` of its list result, or the `foldr` that consumes its list argument
once, written there or inside a function outside the tree defined by it, such
as `all` or `sum`, and the recipe shows `fold/build` firing where it is inlined
beside its counterpart; one passing the list to a tree binding that does so
is a forwarder, and one applying its `foldr` to a call's list is where
the fusion happens and needs nothing for it. The comment P requires
of a directly fusing binding names F1. P says what that requires of it
and of the bindings forwarding to it. `pragma-census.py --rule` lists
as candidates the bindings whose body names `build` or `augment` and whose
result is a list, or names a good consumer defined outside the tree and which
take a list each equation names once and no pattern takes apart, lists of `Int`
or `Bool` left out; this recipe confirms them. A count that falls may only have
lost a duplicated consumer, so read it against `core-diff.py`.

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

**Read:** where the project builds at `-O1`, a costly chain needs a form
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
  after its `--self-test`.
- Bangs the base had and the tip dropped: `python3 $T/bang-drops.py OLD NEW`
  over two source trees.
- Unbanged bindings that a lambda, a section or a per-element combinator reads:
  `python3 $T/lazy-reads.py TREE`.
- After a change to pragmas or structure that a bang's reason leaned on: flip
  each bang alone, rebuild the dumps and run
  `python3 $T/core-diff.py dist-dump-A dist-dump-FLIP --verdicts` over every
  module. GHC's redundant-bang warnings are no evidence (GHC
  [#27862](https://gitlab.haskell.org/ghc/ghc/-/work_items/27862)).
- Arguments left lazy that the final Core takes apart: B1's `box-audit.py`,
  whose `unused` lines include each argument taken apart under a branch
  and passed boxed.

**Read:** a bang changes semantics where an element may be boxed and undefined.
Force only unboxed elements there (vector's `elemseq`), or record the change
in the CHANGELOG. A bang costs, too, where the function is inlined and a caller
passes the argument a list a `build` produces, or a constant: it is a `case`
in the caller, which blocks `foldr/build` fusion and can keep work
on the constant from running once at top level. In orthotope on GHC HEAD
(2026-10-18) the Unboxed `vUnsafeConcatN` banged on its list cost up to 824
bytes a call, and the Ranked `transpose` banged on its permutation 136.

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
- Allocation per element: B1's allocation sweep over the benchmark, and a probe
  for code no benchmark row runs. A thunk is looked for in compiled code
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

- B1's allocation sweep: `python3 $T/ticky-diff.py A.txt` lists one run's
  closures by allocation, and `python3 $T/ticky-diff.py A.txt B.txt` those whose
  allocation moved between two builds, from `+RTS -rFILE` runs at the same
  `--iters` of builds made with `-ticky`.
- `core-diff.py --module` names a `$wgo` or `go` that appeared.
- In the dump, `letrec` where `joinrec` was meant, and `I#` or `D#` built
  in a loop's jumps.
- `perf-per-call.py` gives what it costs in instructions.

**Read:** prefer the smallest workaround that keeps a hand-written loop's shape,
its loops having been tuned for register allocation. A loop bound computed
from what the enclosing function binds kept `go` a join point.
`-fno-full-laziness` and `-fno-exitification` are flags to ask for, not fixes.
Mark the workaround with its issue (W1).

### A2. HasCallStack where its frame can show

**Catches** a `HasCallStack` whose frame no backtrace can print, an argument
on every call for nothing, and one missing on an operation that checks
its arguments, whose error then names no caller. **Seen:** orthotope, where
it sat on most of Dynamic's operations and on few of Ranked's or Shaped's.

**Recipe:** `python3 $T/hascallstack.py ROOT` reports the signatures
and `GHC.Stack` imports that disagree with the rule its docstring states,
the errors worded as neither an argument's nor a violated contract's, which
the rule reads, and the stack-taking functions that call themselves; `--fix`
rewrites the signatures and imports, and `--list` prints the verdict.

**Read:** a stack-taking function that calls itself pushes a frame at every
level, so recurse through a local worker that takes none.

### A3. Values meant never to be built

**Catches** a value of a type meant never to be built, built only where
a consumer takes it apart, built after all because a binding that returns
or takes one is called out of line. GHC HEAD 10.1.20260918 returns no sum
unboxed, so a sum crosses a call only as a heap object (A1), where
worker/wrapper passes and returns a product unboxed. **Seen:** orthotope's
`Route` and `Range`. With `unorderedRouteT` and `cellsRouteT` out of line, their
workers returned a boxed `Route` at 18 and 45 client call sites, while
a benchmark timing 200000-element arrays moved on none of them (2026-10-11);
with `readRangeT`, `sameRangeT` and `range3T` out of line, they returned a boxed
`Range` at 262 call sites in the library and the benchmark, each probe of them
allocating as much as with the `Range` built (2026-10-12).

**Recipe:**

- Find the candidates by B1's `box-audit.py`: it lists each binding that takes
  a value apart though passed it boxed and, with `-ddump-cpr-signatures`
  in the dump build, each returning one boxed, marked or not; a sum among them
  is a candidate, a project's printed `sum` once `--sum` names its type.
- Mark each such type: a plain comment directly above its haddock whose first
  line opens `-- Unmaterialized:`, saying where it is built and taken apart;
  a product too, such as orthotope's `Axes`, where it is meant to stay unboxed.
- `python3 $T/pragma-census.py --rule SRC` makes each binding whose type takes
  or returns a marked sum require `INLINE`, and lists those whose comment in P's
  form does not name each such sum and cite A3,
  as `-- INLINE: Route, A3: it returns the Route its callers take apart.` does.
  A marked product requires no pragma of its bindings.
- Confirm by allocation at a client, on small arrays: call each binding taking
  or returning a marked type, product or sum, once as compiled and once
  with the value passed to a `NOINLINE` identity, which builds it; where the two
  allocate alike, the call built it. orthotope's specialisation benchmark
  carries such probes, which part by the value's size where nothing is built, 24
  bytes a `Range` or an `RSlice`, 32 an `Axes` and 64 an `RRuns` or an `RFill`
  with its `Axes`, and its rows on [2, 2] arrays price what a call costs once.

**Read:** P says what a binding taking or returning a marked sum needs;
its callers need nothing for it. A probe of a product that reads alike both ways
requires the binding's code or pragma changed by measurement, under a comment
citing it. A value built once inside one binding and taken apart in several
places, as at a join point, is built whatever the pragmas, as orthotope's
`equalT` built a `Route` with all its callees `INLINE`, and requires the code
changed rather than a pragma.

## B. Boxing

### B1. Boxing audit: does every value meant unboxed run unboxed?

**Catches** a value that runs boxed where the code means it unboxed,
in whichever form: an argument a callee takes apart but receives boxed, a result
returned boxed, loop state or a captured value kept boxed, a thunk where a value
was meant, a dictionary passed at run time. Five checks find one form each: S1
the dictionaries, L1 an argument or binding left lazy, L2 a captured value
unboxed on every iteration and a lazy element read, A1 closures and boxed loop
state, A3 the values meant never to be built. This is the sweep of the evidence
they share, allocation, the Core's arguments and results, captured values
and dictionaries, whose findings each reads for its own form, and it finds what
none of them looks for, an argument taken apart though passed boxed
and a product returned boxed. **Seen:** on GHC HEAD (2026-10-19), a NOINLINE
function taking six two-field products apart got a worker taking eight fields
unboxed and the last two products boxed, at `-fmax-worker-args`'s default of 10,
all twelve unboxed at 20; the same function small enough to inline got no worker
at all, all six passed boxed wherever a call does not inline it, though
its demand signature called four of them unboxed, so the final Core
is the evidence; and orthotope's cases of the five checks.

**Recipe**, over the tip's dump build and the project's benchmark:

- Allocation first, which catches at once every form that allocates: each
  benchmark cell's bytes a call against what its result holds and, for a change,
  against the base's, cell by cell, before any count; `ticky-diff.py` names
  the closure that allocates. A1 and L2 take their allocation from this step.
- Arguments and results:
  `python3 $T/box-audit.py dist-dump-TIP --module CLIENT --sum TYPE --ignore REGEX`,
  CLIENT as in S1, each `--sum` a type of the project's that is a sum
  or a synonym of one (orthotope's `IU.ShapeL` and `I.InnerFirst`), each
  `--ignore` naming the client's own bindings (the specialisation benchmark's
  `lvl` rows): each argument a binding takes apart though passed boxed, and,
  with `-ddump-cpr-signatures` added to the dump build, each result returned
  boxed. First run it over a module built with the same GHC in which a NOINLINE
  function takes apart six two-field products: it must print the worker's last
  two arguments `unused` at the default `-fmax-worker-args` and none at 20. L1
  reads its `unused` lines for arguments left lazy, A3 those of a sum type.
- Captured values by L2's `captured-unbox.py`, and dictionaries by S1's audit.
- Each finding read in the Core by the check of its form, then priced
  at a client by `perf-per-call.py` before the code changes.

**Read:** `used`, the box used besides its fields, is most often deliberate:
a box stored, returned or handed on to a callee that takes it boxed. `unused`
is the box worker/wrapper did not remove: past `-fmax-worker-args`, for which
a narrower callee is the remedy; under a lazy demand, for which L1's bang is;
or in a function small enough to inline, which gets no worker and is boxed only
where a call does not inline it. A sum crosses a call boxed whatever is done
(A3). What no scan reports, a field stored boxed or a box rebuilt at a call
site, shows only as allocation, which is why allocation comes first. Count a box
that allocates nothing before calling it a cost.

**Keep** the benchmark's allocation compared cell by cell before any timing
of a change.

### B2. Wide calls after a client's loop: unboxing that costs

**Catches** the reverse of B1: a call that needs many values, the fields
an out-of-line worker takes unboxed or those a box passed to it is rebuilt from,
made right after a client's loop, keeps all of them live through the loop, each
reloaded from the stack on every iteration that evaluates a boxed element.
The reloads allocate nothing: instructions move, by the element and the value
kept live. **Seen:** orthotope's `compare`, made INLINABLE (2026-10-19):
its specialised worker took ten arguments, a dictionary and nine fields
of the two arrays, and a client summing the boxed elements of `min a b` before
computing `min b a` reloaded ten values an element where the inlined `compare`,
whose first out-of-line call takes the two shapes, reloaded three, and moved
values through C-stack slots 12 times against 2: 55 instructions an element
against 38, 1.21 times at 200000 elements. The saving and restoring around each
element's evaluation, evaluated already or not, is GHC
[#25349](https://gitlab.haskell.org/ghc/ghc/-/work_items/25349).

**Recipe:**

- `python3 $T/loop-reloads.py dist-asm-TIP --module CLIENT` over D's build
  for B2: each loop's return point and the values it reloads from the enclosing
  frame on every iteration, most first. Its known positive is the case above,
  ten against three.
- Rank them by how often they run: a callgrind run of a client cell, read
  by `cg-read.py seq`, gives each return point's executions a call,
  and those times its reloads are the instructions it costs. A procedure
  the dump labels `.L` has no symbol in the binary, and callgrind books its code
  under the nearest global symbol before it in the dump, so `seq` runs
  over that symbol, and the return point is the one whose loads match
  the offsets listed.
- A count by `perf-per-call.py` decides.

**Read:** a loop costs only as often as it runs, so read the ranked list
from the top. A narrow first call keeps the other values in their stack slots
through the loop: an INLINE wrapper whose first out-of-line call takes only what
it needs first, `compare` on the shapes, and the wide call after that. Narrow
is what the call needs live, not its arity: a client calling a `compare`
that took the two shapes and two boxes, which the client rebuilt at the call
from fields it held, reloaded nine values an element (2026-10-19). The narrow
first call pays for passing the fields to a second call, about 35 instructions
a comparison of two [3, 3] arrays in orthotope, against a cost that grows
with the loop: count both sides at the sizes the clients use.

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
as orthotope's instance comments say that no fusion is given up. **Seen:**
a survey of orthotope's comment blocks found blocks citing an issue, blocks
standing in for a flag, design notes, and a few hidden ones. One hidden block
matched GHC [#27737](https://gitlab.haskell.org/ghc/ghc/-/work_items/27737),
filed from that same loop, and now cites it.

**Recipe:** `python3 $T/workaround-cites.py SRC`, both directions at once:
the comment blocks that mention a workaround and name no cause, each read whole
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
- `python3 $T/ab-time.py --cpu 3 STOCK FIXED STOCK_SC FIXED_SC 2 NAME...`
  reports allocation per benchmark. The rows that move with the fix
  are the issue's sites. The probe must be a criterion benchmark, which is what
  `ab-time.py` runs.
- For a GHC issue with a local fix, build with the patched compiler.
  `python3 $T/core-diff.py dist-STOCK dist-FIXED --verdicts` names the modules
  it reaches.

**Read:** Mikolaj adopts a workaround only where it costs virtually nothing once
the fix ships and the user builds with SpecConstr. Unspecialised callers do
not count.

### W3. Unnatural tweaks not marked

**Catches** hand-tuned shapes that a reader would tidy back into the slow form:

- a loop written by index where a combinator exists;
- an argument order;
- a cursor stepped twice, or a literal where the value would read better;
- `GHC.Exts` primitives, `lazy`, `oneShot`, `inline`, or NOINLINE on a helper;
- a bang's placement, a wrapper and worker split, or a route recognised again
  deep inside a fill.

Each needs a comment giving its measurement and its cause, or W1's
"unidentified". Orthotope's comment on `genericFillStrided` says it re-derives
`RRuns`, a hack that lets each vector kind be tuned, in a system where some
layouts are routes and others are recognised deeper down.

**Recipe:**

- `git diff BASE -- '*.hs' | command grep -nE '^\+.*(GHC\.Exts|#\)|\blazy\b|oneShot|\binline\b|NOINLINE|unsafeIndexM|generate|unsafeWrite)'`.
- Then read every function the diff rewrote against its natural form. Code
  with no comment at all is what W1's tool cannot reach, and no tool
  distinguishes a tweak from a design.

### W4. Flags added

**Catches** `OPTIONS_GHC`, `ghc-options` or project-file flags added without
Mikolaj's approval, or without a comment saying why and for which GHCs.

**Recipe:**
`git diff BASE -- '*.hs' '*.cabal' 'cabal.project*' | command grep -nE '^\+.*(OPTIONS_GHC|ghc-options|-f[a-z]|-O[0-9])'`.

**Read:** never `-fno-full-laziness` with `-fno-cse` (#27886). Take `-O2`'s
constituents, never the bundle: where it helps, bisect the flags it enables
beyond `-O` and take only those that carry the effect. The trade is weighed
by P. An A/B of a flag needs fresh build directories rather than a rebuild:
`ghc --make` does not recompile a module when only `-fkeep-auto-rules`
or `-fpolymorphic-specialisation` changes, though both change what it exports.

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
- `ctime-diff.py` and `core-diff.py` compare two builds, each made as P measures
  compile time.

**Read:** by P.

## The tools

Scripts under `tools/` measure a difference between two builds and take
it from "something moved" to the function or module that moved it, and the last
two of its list concern where loops happen to land: `align-as.py` keeps it out
of that difference and `loop-offsets.py` determines it from a binary. Each
of the others has a `--self-test` and exits 2 rather than 0 when its run did
not happen, so that a build made without the needed flags cannot look like one
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
  and `--iters N`, interleaved, rotated and optionally pinned, over a few
  repetitions: the instructions from the lowest count at each `--iters`,
  and the cycles from the median. Where a build's instruction differences spread
  over more than 1%, it reports that and exits 1. Its instruction counts back
  a wall-time ratio as cachegrind's do, at native speed; its cycles carry
  the machine's noise.
- `tools/cachegrind-per-call.py` gives instructions and estimated cycles per
  call of one benchmark, from cachegrind runs at `--iters 2N` and `--iters N`,
  for a machine where `perf stat` cannot run. It is deterministic, so it is what
  backs a wall-time ratio that decides whether a change is banned; in that study
  it showed wall-time medians of 1.05 to 1.06 to be noise, the instruction
  counts equal to 0.003%. With `--cells FILE` it counts every cell of a file
  of `MODE NAME N` lines in each of several builds, a `summed` cell run
  with `--summed` as orthotope's specialisation benchmark takes it, each figure
  exact to two decimals; give a cell of large arrays 100 calls or more, which
  keeps a collection from moving its count. `--cpu` pins the runs to one CPU,
  and `--arg` passes the benchmark an argument.
- `tools/cg-read.py` reads a benchmark binary's callgrind runs, made with
  `valgrind --tool=callgrind --dump-instr=yes --compress-strings=no --compress-pos=no`,
  against the binary's symbols and disassembly, each symbol's z-encoded unit
  prefix stripped so that a function keeps its name across builds: `bysym` gives
  instructions a call by symbol in two runs, `incr` the same between N and 2N
  calls of each of two binaries, which cancels the process's setup, `allocs`
  the heap-pointer bumps executed at least half as often as the calls
  and the info pointers stored into the memory they allocate, `region`
  the executed instructions of one symbol's code in two runs, diffed, and `seq`
  one run's, filtered by count a call. Its disassembly restarts at every
  executed address a sweep did not decode: a linear sweep through one of GHC's
  info tables falls out of step with the code after it, dropping executed
  instructions and printing the table's bytes as code. In orthotope's
  specialisation benchmark a run of N calls executes the row N + 2 times, so one
  run's counts over N are high by (N + 2)/N, and `incr`'s are not. `sweep`
  reports whether every `perf record` sample of a range decodes
  as an instruction start in a linear sweep from the range's start; settle
  that before reading a hot loop off the samples and objdump at the hot
  addresses, and where it reports a miss, read the loop from `seq` instead.
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
- `tools/row-core.py` tells which rows of orthotope's specialisation benchmark
  have Core that differs between two builds, from their `-ddump-simpl` dumps
  and a source tree resolving the qualifiers: for each row, the forced
  and the summing function are each `same`, `literals` or `differs`, following
  the benchmark's own code alone and then every reference, a binding's hash
  covering everything it reaches. `diff` names a row's first differing node,
  `dump` writes a row's closures to a file, and `nodes` and `tokens` compare two
  such files node by node and one node token by token, names normalised.
  It is the first reading of a change, the rows it leaves `same` serving
  as controls for the counts and timings after it.
- `tools/census.py` runs a census of orthotope's specialisation benchmark
  over two builds: `cells` takes the cells of the rows `row-core.py` marks
  `differs`, and `movers` those whose bytes differ between the two builds'
  tables; `count` counts each with `perf-per-call.py` at N and 2N calls, N sized
  from the first build's table to about 20 ms, resuming where an earlier count
  stopped, and `--cpus` splits it over lanes, one a CPU; give CPUs on separate
  cores. `read` groups the cells whose ratio moves by 0.2% or more, one exactly
  at it included, and lists apart those counted over fewer than 200 calls
  in a group not every cell of which moves, which `noise` counts again at ten
  times N. Its figures are differences between N and 2N calls, so the two
  evaluations the harness makes before each batch cancel.
- `tools/pragma-calls.py` sorts the inlining pragmas a worktree's diff removes
  by whether their removal changed the Core, counting each target's name per
  module in two builds' dumps: DEAD where every count agrees, MOVED
  with the modules that differ; a name removed in several modules is judged per
  module, each counting only the tokens that name its own module's binding.
  It is the step between removing a whole group of pragmas and bisecting it.
  DEAD is weaker than identical Core, and does not make a pragma removable: P's
  rule on removing keeps it. With `--inline` it processes one build instead,
  marking each INLINE target of a source tree CALLED, COPIED or RECURSIVE (I1,
  I2).
- `tools/pragma-map.py` sets the inlining pragmas of two source trees side
  by side, keyed by file, enclosing class or instance head, name and occurrence,
  and prints those that differ, `none` where a tree has none for a key:
  the pragmas two commits of a library disagree on, where `pragma-calls.py`
  reads what removing some does to the Core.
- `tools/rules-diff.py` compares which rewrite rules fired per module in two
  builds, from `-ddump-simpl-stats` dumps, the fusion rules marked,
  and with `--unfolding NAME` how often a function was inlined. It reports
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
  and reports where each lands in its cache line, so that a margin between two
  builds can be checked for being one of them placing a loop astride a line
  where the other did not: on micro-regime3 a straddled copy of one 28-byte loop
  was priced at 1.19 against a resident one. `--survey` counts every loop up
  to a line long and the straddlers among them, `--delta` reports how far
  a rebuild moved the tracked loops, and `--match` names a binary's straddlers
  off its `-g3` twins; its cases are in `tools/defects.json`.

The tools written for the checks of one build or one source tree,
`tools/pragma-census.py`, `tools/spec-audit.py`, `tools/bang-drops.py`,
`tools/lazy-reads.py`, `tools/captured-unbox.py`, `tools/box-audit.py`,
`tools/loop-reloads.py`, `tools/workaround-cites.py`, `tools/hascallstack.py`
and `tools/hpc-untaken.py`, exit 0 clean, 1 with findings and 2 when the run did
not happen, as `pragma-calls.py --inline` does; `tools/bang-lazy-check.py`,
without `--allow`, exits 0 whatever it printed, its candidates being
for the reader.

- `tools/pragma-census.py` lists the overloaded functions, instance methods
  and class default methods of a source tree that carry no pragma,
  and with `--rule` every one whose pragma differs from what P's rule gives it,
  a forwarder's and a thin wrapper's included (I4), and each one taking
  or returning a sum marked as never to be built that lacks its comment (A3);
  with `--write` it writes the pragmas the rule adds or strengthens
  into the tree (I4).
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
- `tools/box-audit.py` lists the arguments optimised Core takes apart though
  they are passed boxed, marking those whose box is used besides, and, from CPR
  dumps, the results returned boxed (B1).
- `tools/loop-reloads.py` lists, from `-ddump-asm`, the loops whose every
  iteration reloads values from the enclosing frame (B2).
- `tools/workaround-cites.py` lists the comment blocks that mention a workaround
  and name no cause, and each filed issue of `docs/` with the files citing
  it (W1).
- `tools/hascallstack.py` checks orthotope's `HasCallStack` constraints,
  and the error wording they depend on, against the rule its docstring states,
  and rewrites the constraints to it (A2).
- `tools/hpc-untaken.py` lists the functions and expressions a run of an `-fhpc`
  build never entered, from its `hpc draft`, error calls and type-only
  placeholders left out where the draft quotes them (M).
