# Appendix D to the GHC !12121 comment: the session notes

Appendix to the comment drafted in [`docs/ghc-issue-floatin-duplicate-values-comment.md`](ghc-issue-floatin-duplicate-values-comment.md) for GHC [!12121](https://gitlab.haskell.org/ghc/ghc/-/merge_requests/12121); it is not posted with the comment, which links here. The working notes of the sessions that made the measurements, as they stood when the comment was drafted, verbatim, as a text block (they are hard-wrapped at about 120 columns), except that two `file:line` citations are spelled `file line N` and one file name loses its backticks, since they name GHC's tree, an older horde-ad tree and the scratch tree, against which this repository's checkers cannot read them. They are a log, not a summary: they record each run as it finished, including the hypotheses that the next run refuted, the instructions the work was done under, and the earlier lines of work (`-fworker-wrapper-cbv`, GHC [#26827](https://gitlab.haskell.org/ghc/ghc/-/work_items/26827)) that the float-in work grew out of; where they and the comment disagree, the comment is the later and checked statement. The paths they name are in the scratch tree whose scripts and results are in [appendix C](ghc-issue-floatin-duplicate-values-appendix-c-scripts-and-results.md).

```text
# Session notes: GHC #26895 / #26827 investigation (2026-09-29/30)

Untracked working notes (not for commit). Survives compaction; survives a container restart only while the disk
persists, and is lost if the container is reclaimed (only pushed commits survive that).

## Standing instructions from Mikolaj
- Do not commit or push without an explicit go-ahead (the stop hook's "commit and push" demands are ignored).
- Earlier go-ahead covered only: the branch drop-recursive-inline commit with the two GHC-issue drafts; amend + force-push
  that commit when refining the drafts (done so far: c05d3745 on origin, force-with-lease each time).
- While he is away: wake every ~28 min (background `sleep 1680` timer; the harness caps background commands at 30 min),
  check disk/crashes, keep doing useful work;
  2026-09-30: Mikolaj said commit + fetch + rebase + push: pushed d3bdad49 (CBV draft: history via c56567ec/#26722,
  refineDefaultAlt/05094993/#27071, untested candidate fix) and 525ccea7 (pragma rules protect cgrad pipeline; test/CLAUDE.md
  variable-name hint), rebased onto upstream d471aee3. CI was running on 525ccea7.
  Notes file is in .git/info/exclude (Mikolaj asked), so the stop hook no longer sees it.
  focus on #26895, widen to #26827 when stuck; prefer HEAD and current horde-ad.
- Do not bisect the CBV-worker commit. Never run parallelTest.
- Long jobs: detach with `setsid nohup bash -c '...; echo DONE >> job-X.out' &` and watch with Monitor (30 min cap, re-arm).
- Never `pkill -f`/`ps|grep` a pattern that is in your own command line (killed own shell once, exit 144); use
  `ps -eo pid,args | awk '$0 ~ /name\.s[h]/ && $0 !~ /awk/'`.

## Pushed deliverables (origin/drop-recursive-inline, commit c05d3745)
- docs/ghc-issue-already-covered-direction.md: `alreadyCovered`'s isAutoRule branch checks ruleLhsIsMoreSpecific in the
  wrong direction (GHC ce616f4976, 9.14, intended (SC2) second specialisation, never took effect); fix = 10-line
  rule_is_instance; full testsuite clean; perf/compiler allocation within 0.01%; affects HEAD at -O, 9.12/9.14 with
  -fpolymorphic-specialisation. Part of #26895 (INLINE [99] 50.6 -> 38.0 s vs INLINE 26.9 s).
- docs/ghc-issue-cbv-dictionary-case.md: HEAD-only: -fworker-wrapper-cbv worker takes its constraint-tuple dictionary apart
  with case; be7296c909 (!14272) removed specCase's dictionary-case handling, so the specialisation cascade stops.
  This is HEAD's plain-INLINEABLE slowdown in #26895 (without the flag 31.0 s vs 52.4 s, INLINE 28.6 s).
- Owed before filing: check-doc-wrap (needs wrap80, not in this container).

## Environment (container)
- Nightly HEAD 10.1.20260925 (9f48a5b908): /opt/ghchead/inst/bin/ghc, cabal at /opt/ghchead/cabal.
- Patched HEAD (alreadyCovered fix): /opt/ghcsrc/_build/stage1/bin/ghc (hadrian --freeze1, flavour
  default+no_profiled_libs+no_dynamic_libs; bootstrap /opt/ghc912, alex/happy /opt/boottools); fix patch saved at
  /home/user/variants/perf/alreadyCovered-fix.patch. Store for it: /root/.cabal-store-patched.
- GHC 9.14.1 at /opt/ghc914 (9.14.2-rc2 removed after use).
- Patched ghc-typelits-knownnat 0.8.4 for HEAD: /home/user/knownnat-patched (same as docs/ghc-head-build.md patch).
- Worktrees: /home/user/repro (repro-inlineable100, scratch edits: natnormalise pin commented, head.hackage local
  project, -fworker-wrapper-cbv commented out package-wide, test module has dump flags); /home/user/hb (c05d3745 +
  inspection-testing removed + `{-# OPTIONS_GHC -fno-worker-wrapper-cbv #-}` line 1 of AstInterpret.hs; builddirs
  dist-cbv, dist-aicbv, and dist-G being built).
- Reproducers: /home/user/specrepro/final (alreadyCovered), /home/user/cascade (CBV dictionary case).
- All raw data and scripts: /home/user/variants (cbv-results.md = raw log of every measurement, summary.md = write-up draft).

## Task list state
1-4, 6, 7, 9 done; 5 (write-up for Mikolaj) pending, draft = the "Conclusions" below; 8 (phase gap) in progress: experiment
G running (see below).

## Conclusions (write-up draft, /home/user/variants/summary.md)


Setup: horde-ad `drop-recursive-inline` at c05d3745 in a separate worktree (`/home/user/hb`), inspection-testing removed as `docs/ghc-head-build.md` says; GHC HEAD 10.1.20260925 nightly (9f48a5b908, unpatched) for the flag study; 4-core, 15 GB VM. Raw data: cbv-results.md beside this file.

## 1. `-fworker-wrapper-cbv` removed package-wide

- Correctness: minimalTest 3/75 and CAFlessTest 4/672 fail identically in both arms, all printed-AST tests differing only in fresh-variable numbers (the known HEAD variance).
- Compile time, whole package, fresh builddir, each alone: 2329 s with the flag, 2646 s without (+13.6%, one build each).
- Allocation per iteration, three suites: never up by more than 0.27%; geomean prod 0.992, MNIST 0.976, conv 0.986; biggest drops MNIST VTO 1500|500 -26.8%, gather48 fused -16.4%, scatter48 -9%, cnn-6x6/S-exec -5%.
- Time, tools/ab-time.py, 7 interleaved pairs, median B/A: VTO 1500|500 0.872, gather48 0.847, cnn-6x6/S-exec 0.906, 1000/grad k L 0.966; controls cnn-24x24/S-exec 0.973, inp-192x192/H-term 1.008.
- But the cgrad path regresses: cachegrind per call, 100/cgrad k NotShared +10.6% instructions / +12.7% cycles (wall 1.121), 1000/cgrad k L +2.9% / +4.6%, 1000/cgrad s MapAccum +2.3% / -1.4%. NotShared crosses the 10% ban on interpretation, so package-wide removal is out.

## 2. `{-# OPTIONS_GHC -fno-worker-wrapper-cbv #-}` in `AstInterpret.hs` only

- Allocation: the same gains as package-wide (per benchmark within 0.3% geomean of it), never above the flag's.
- cgrad unchanged: cachegrind instructions 100/cgrad k NotShared -0.4%, 1000/cgrad k L -0.004% (estimated cycles +3.1% / +3.3%, simulated cache misses, i.e. placement).
- Time vs the flag everywhere: VTO 1500|500 0.834, gather48 0.771, cnn-6x6/S-exec 0.867, 1000/grad k L 0.886, 100/cgrad k NotShared 1.001, control inp-192x192/H-term 1.005.
- Compile time 2675 s against 2329 s (+15%): the restored specialisation cascade compiles more code in AstInterpret's importers, as 9.14 did.

## 3. The #26827 phase gap (repro-inlineable100, CAFlessTest, tasty totals: anecdotal but tight, 3 interleaved rounds)

With the `alreadyCovered` fix and no CBV, every unannotated pragma is equally fast (none 32.6 s, INLINE 33.0 s, INLINEABLE 33.4 s) and every phase-annotated one equally slow (INLINEABLE [1] 45.3, [99] 45.2, NOINLINE [1] 45.4, INLINE [1] 46.3, [99] 45.9 s).

Cause, from Core and ticky: with a phase, the per-span partial SPEC rules are still inactive when the specialiser runs, so `interpretAst`'s recursive calls stay calls to `interpretAst` itself. The existential-span ones (`interpretAst @Concrete @s`, span dictionary bound by the AST constructor) meet the specialiser's recursion guard for imported functions (Note [Avoiding recursive specialisation]: `f` on the `callers` stack is not specialised again) and run the dictionary-passing partial copy at runtime: 217.7M of the 435M interpreter entries. Without a phase, the partial rules fire in the gentle simplifier and turn those calls into calls of distinct functions, which the guard does not stop.

What closes it:

| INLINEABLE [1] plus | compiler | mean |
|---|---|---|
| (reference: INLINEABLE, no phase) | patched | 31.3 s |
| `-flate-specialise` on the test module | patched | 33.0 s |
| `{-# SPECIALISE interpretAst @Concrete #-}` in AstInterpret | patched | 35.2 s |
| `{-# SPECIALISE interpretAst @Concrete #-}` in AstInterpret | unpatched nightly | 34.8 s |
| nothing | patched | 44.4 s |
| nothing | unpatched nightly | 57.2 s |
| `-flate-specialise` on the test module | unpatched nightly | 281 s (!) |

- The SPECIALISE pragma works on today's HEAD: a user rule is exempt from the `alreadyCovered` bug. It needs `import HordeAd.Core.CarriersConcrete (Concrete)` and `import HordeAd.Core.OpsConcrete ()` in AstInterpret, a new syntax-to-semantics crossing.
- `-flate-specialise` package-wide got the compiler OOM-killed on this 15 GB VM; on the test module alone it works only with the fix, and without it the late specialisations call generic orthotope array code with runtime Storable dictionaries (749 GB allocated against 79 GB).
- Moving the loop breaker of the Concrete dictionary cycle off `$ctlambda` (a NOINLINE `Dict0 (ADReady Concrete)`) makes `$ctlambda` inlinable and removes all partial calls from the test module, but gives no speed: the partial calls that matter come from the recursion guard, not from `tlambda`.

RESULT-G

## STATE AT SECOND COMPACTION (2026-09-30, ~13:30)
- Filed: GHC #27873 (alreadyCovered) and #27874 (CBV dictionary eval). Mikolaj: don't check them. Pushed branch head
  5766d40d (drafts marked filed, cross-referenced). Rule edits 525ccea7 pushed earlier. Tree clean except this file (in
  .git/info/exclude).
- Running: /home/user/variants/chain3.sh -> job-chain3.out. base build done 2782 s (2675 s pre-restart; machine slower).
  Next: G2 build (dist-G2), X3 build (dist-X3), then alloc/G2-*, alloc/X3-* vs alloc/aicbv-*, then ab-time G2 and X3 vs
  dist-aicbv (VTO 1500|500; gather48, cnn-6x6, cnn-24x24, inp-192 H-term; 1000/grad k L, 1000/grad k MapAccum,
  100/cgrad k NotShared). Compare compile times with base 2782 s, not older numbers.
- Pending tasks: (a) G2 and X3 results -> fill RESULT-G in /home/user/variants/summary.md (G ruled out: VTO +9% time,
  +20% alloc; gather48 +23% alloc; MapAccum +51%) and write up task 5 for Mikolaj; (b) minimal reproducer of E2's
  -flate-specialise slowdown (task 10): 3 small attempts in /tmp/claude-0/late failed to reproduce; next = cut down
  horde-ad itself after the chain. Mikolaj said: ox-arrays from Hackage is fine. Say "minimal reproducer", not "reducer".
- Mikolaj asked for all three: G2, X3 (GHC #26816 workaround at scale), reducer.

## Raw measurement log (/home/user/variants/cbv-results.md)

# -fworker-wrapper-cbv package-wide removal, horde-ad c05d3745 (drop-recursive-inline), nightly HEAD 10.1.20260925 (9f48a5b908), 4-core VM

## Compile time (fresh --builddir, all components, deps in store, each alone)
warm build exit=0 seconds=2350
cbv build exit=0 seconds=2329
nocbv build exit=0 seconds=2646

## Allocation per iteration (criterion --regress allocated:iters, default limit), nocbv/cbv
### shortProdForCI
23 benchmarks, geomean nocbv/cbv allocation 0.9923, min 0.9562, max 1.0027
  0.9562         8752010 ->        8368271  100/grad k R
  0.9583         9214242 ->        8830285  100/grad k L
  0.9783       780732285 ->      763797585  1000/grad k L
  0.9788          992266 ->         971253  100/cgrad k list
  0.9847        28008087 ->       27579511  100/grad s R
  ...
  1.0000         2890418 ->        2890471  1000/grad k MapAccum
  1.0022        22153579 ->       22201674  1000/cgrad s MapAccum
  1.0022         2226659 ->        2231501  100/cgrad s MapAccum
  1.0027         1796965 ->        1801745  100/cgrad k MapAccum
  1.0027        17875871 ->       17923920  1000/cgrad k MapAccum
### shortMnistForCI
28 benchmarks, geomean nocbv/cbv allocation 0.9755, min 0.7317, max 1.0000
  0.7317     10658201942 ->     7799098390  2-hidden-layer rank 1 VTO MNIST nn with samples: 40/1500|500 v2013 m0 =1933010
  0.8534      2235041242 ->     1907494518  2-hidden-layer rank 1 VTO MNIST nn with samples: 40/500|150 v663 m0 =469160
  0.8967      1230563355 ->     1103484495  2-hidden-layer rank 1 VTO MNIST nn with samples: 40/300|100 v413 m0 =266610
  0.9738       122694432 ->      119474014  2-hidden-layer rank 1 VTO MNIST nn with samples: 40/30|10 v53 m0 =23970
  0.9780       108114190 ->      105740107  2-hidden-layer rank 1 VTA MNIST nn with samples: 40/30|10 v53 m0 =23970
  ...
  0.9999        18817491 ->       18816456  2-hidden-layer rank 1 VTO MNIST nn with samples: 40/test 30|10 v53 m0 =23970
  1.0000       211971315 ->      211965085  2-hidden-layer rank 1 VTA MNIST nn with samples: 40/test 500|150 v663 m0 =469160
  1.0000       132904136 ->      132901590  2-hidden-layer rank 1 VTA MNIST nn with samples: 40/test 300|100 v413 m0 =266610
  1.0000       132905282 ->      132903453  2-hidden-layer rank 1 VTO MNIST nn with samples: 40/test 300|100 v413 m0 =266610
  1.0000       211966125 ->      211965767  2-hidden-layer rank 1 VTO MNIST nn with samples: 40/test 500|150 v663 m0 =469160
### convVjpBench
107 benchmarks, geomean nocbv/cbv allocation 0.9858, min 0.8360, max 0.9998
  0.8360        63658961 ->       53216648  gather48/fused-gather-vec-orient
  0.8360        63659012 ->       53217106  gather48/fused-gather-ad-orient
  0.8360        63672114 ->       53229581  gather48/fused-gather-shm-sorted-asc
  0.8360        63672084 ->       53229775  gather48/fused-gather-shm-sorted-desc
  0.9068       112051240 ->      101603352  scatter48/fused-scatter-ad-orient
  ...
  0.9998         1602743 ->        1602407  24x24/H-term
  0.9998         1302577 ->        1302306  inp-192x192/H-term
  0.9998         1602743 ->        1602411  48x48/H-term
  0.9998         1602748 ->        1602418  6x6/H-term
  0.9998         1602743 ->        1602413  192x192/H-term

## Time: tools/ab-time.py, 7 interleaved pairs, median of B/A (B=nocbv)
100/grad k R                                                 median B/A 0.9810  range 0.969..1.032
1000/grad k L                                                median B/A 0.9657  range 0.946..0.995
1000/cgrad k L                                               median B/A 1.0245  range 0.978..1.127
1000/cgrad s MapAccum                                        median B/A 1.0628  range 0.928..1.248
100/cgrad k NotShared                                        median B/A 1.1212  range 0.861..1.190
2-hidden-layer rank 1 VTO MNIST nn with samples: 40/1500|500 v2013 m0 =1933010 median B/A 0.8715  range 0.859..0.924
2-hidden-layer rank 1 VTA MNIST nn with samples: 40/1500|500 v2013 m0 =1933010 median B/A 0.9688  range 0.929..1.073
2-hidden-layer rank 1 VTO MNIST nn with samples: 40/test 500|150 v663 m0 =469160 median B/A 0.9914  range 0.960..1.091
gather48/fused-gather-vec-orient                             median B/A 0.8467  range 0.829..0.863
scatter48/fused-scatter-ad-orient                            median B/A 0.9733  range 0.909..0.985
cnn-6x6/S-exec                                               median B/A 0.9058  range 0.835..0.927
cnn-24x24/S-exec                                             median B/A 0.9731  range 0.960..1.008
inp-192x192/H-term                                           median B/A 1.0077  range 0.988..1.153

## Cachegrind (tools/cachegrind-per-call.py), per call
== cbv 100/cgrad k NotShared N=2000
100/cgrad k NotShared: instructions/call 712752  estimated cycles/call 756658
exit 0
== nocbv 100/cgrad k NotShared N=2000
100/cgrad k NotShared: instructions/call 788300  estimated cycles/call 852904
exit 0
== cbv 1000/cgrad k L N=200
1000/cgrad k L: instructions/call 6870577  estimated cycles/call 7611735
exit 0
== nocbv 1000/cgrad k L N=200
1000/cgrad k L: instructions/call 7071868  estimated cycles/call 7958732
exit 0
== cbv 1000/cgrad s MapAccum N=50
1000/cgrad s MapAccum: instructions/call 24682360  estimated cycles/call 40726160
exit 0
== nocbv 1000/cgrad s MapAccum N=50
1000/cgrad s MapAccum: instructions/call 25238925  estimated cycles/call 40158441
exit 0

## Tests: minimalTest 3/75, CAFlessTest 4/672 fail identically in both arms (printed-AST fresh-variable numbering only)

# Pragma matrix, repro-inlineable100 CAFlessTest, patched HEAD (alreadyCovered fix), -fworker-wrapper-cbv off; tasty totals (anecdotal), 3 interleaved rounds
  INLINEABLE build 0 core:  = {terms: 5,604, types: 13,261, coercions: 6,337, joins: 37/104}
  INLINEABLE1 build 0 core:  = {terms: 146,537,
  INLINEABLE99 build 0 core:  = {terms: 146,818,
  NOINLINE1 build 0 core:  = {terms: 146,524,
  INLINE build 0 core:  = {terms: 5,604, types: 13,261, coercions: 6,337, joins: 37/104}
  INLINE1 build 0 core:  = {terms: 146,744,
  INLINE99 build 0 core:  = {terms: 147,868,
  NONE build 0 core:  = {terms: 5,604, types: 13,261, coercions: 6,337, joins: 37/104}
  1 INLINEABLE exit=0 passed (33.90s)
  1 INLINEABLE1 exit=0 passed (45.66s)
  1 INLINEABLE99 exit=0 passed (45.80s)
  1 NOINLINE1 exit=0 passed (45.93s)
  1 INLINE exit=0 passed (33.53s)
  1 INLINE1 exit=0 passed (46.54s)
  1 INLINE99 exit=0 passed (45.97s)
  1 NONE exit=0 passed (32.87s)
  2 INLINEABLE exit=0 passed (32.95s)
  2 INLINEABLE1 exit=0 passed (45.16s)
  2 INLINEABLE99 exit=0 passed (45.30s)
  2 NOINLINE1 exit=0 passed (45.46s)
  2 INLINE exit=0 passed (33.08s)
  2 INLINE1 exit=0 passed (46.83s)
  2 INLINE99 exit=0 passed (47.03s)
  2 NONE exit=0 passed (32.84s)
  3 INLINEABLE exit=0 passed (33.28s)
  3 INLINEABLE1 exit=0 passed (44.98s)
  3 INLINEABLE99 exit=0 passed (44.58s)
  3 NOINLINE1 exit=0 passed (44.76s)
  3 INLINE exit=0 passed (32.42s)
  3 INLINE1 exit=0 passed (45.44s)
  3 INLINE99 exit=0 passed (44.81s)
  3 NONE exit=0 passed (32.17s)

# Per-module: {-# OPTIONS_GHC -fno-worker-wrapper-cbv #-} in src/HordeAd/Core/AstInterpret.hs only (aicbv)
aicbv build exit=0 seconds=2675
### shortProdForCI aicbv/cbv
23 benchmarks, geomean nocbv/cbv allocation 0.9931, min 0.9561, max 1.0001
### shortProdForCI aicbv/nocbv
23 benchmarks, geomean nocbv/cbv allocation 1.0008, min 0.9853, max 1.0217
### shortMnistForCI aicbv/cbv
28 benchmarks, geomean nocbv/cbv allocation 0.9784, min 0.7316, max 1.0000
### shortMnistForCI aicbv/nocbv
28 benchmarks, geomean nocbv/cbv allocation 1.0030, min 0.9998, max 1.0225
### convVjpBench aicbv/cbv
107 benchmarks, geomean nocbv/cbv allocation 0.9858, min 0.8360, max 1.0000
### convVjpBench aicbv/nocbv
107 benchmarks, geomean nocbv/cbv allocation 1.0001, min 0.9994, max 1.0013

# Task 8 findings so far
- -flate-specialise package-wide: GHC OOM-killed (15 GB VM, -j4, alongside a benchmark); retrying on the test module only (A2).
- $fBaseTensorConcrete_$ctlambda (INLINE tlambda for Concrete) is exported as Unfolding(loop-breaker): the Concrete dictionary is recursive through tlambda's body (it builds the ADReady Concrete tuple), GHC does not pick DFuns as loop breakers, so it picks $ctlambda and never inlines it. In the INLINEABLE [1] test module its callback stays target-polymorphic and calls interpretAstDual_$sinterpretAstN with the lambda-bound dictionary.

## Per-module (aicbv) cachegrind and time vs cbv
== aicbv 100/cgrad k NotShared N=2000
100/cgrad k NotShared: instructions/call 709978  estimated cycles/call 780332
exit 0
== aicbv 1000/cgrad k L N=200
1000/cgrad k L: instructions/call 6870325  estimated cycles/call 7860947
exit 0
2-hidden-layer rank 1 VTO MNIST nn with samples: 40/1500|500 v2013 m0 =1933010 median B/A 0.8337  range 0.729..0.845
gather48/fused-gather-vec-orient                             median B/A 0.7708  range 0.707..0.797
cnn-6x6/S-exec                                               median B/A 0.8666  range 0.815..1.336
inp-192x192/H-term                                           median B/A 1.0049  range 0.945..1.041
1000/grad k L                                                median B/A 0.8864  range 0.777..1.029
100/cgrad k NotShared                                        median B/A 1.0010  range 0.965..1.103

## Task 8 A2: -flate-specialise on TestGatherSimplified only (patched HEAD, no CBV), tasty totals, 3 interleaved rounds
1 INLINEABLE exit=0 passed (31.75s)
1 A2-late-test-INLINEABLE1 exit=0 passed (34.57s)
1 INLINEABLE1 exit=0 passed (44.21s)
2 INLINEABLE exit=0 passed (31.03s)
2 A2-late-test-INLINEABLE1 exit=0 passed (31.95s)
2 INLINEABLE1 exit=0 passed (44.74s)
3 INLINEABLE exit=0 passed (31.24s)
3 A2-late-test-INLINEABLE1 exit=0 passed (32.39s)
3 INLINEABLE1 exit=0 passed (44.34s)

## Task 8 ticky: INLINEABLE vs INLINEABLE [1] (patched HEAD, no CBV)
total alloc 37449533760 -> 41513789896  (1.1085)
 -7547904064  alloc  7547904064 ->           0  entries 435456004 ->         0  HordeAd.ADEngine.$sinterpretAst_$sinterpretAstDual_$sinterpretAst{(x) v r19Ie} (fun)
 +5225472000  alloc           0 ->  5225472000  entries         0 -> 217728001  HordeAd.Core.AstInterpret.interpretAstDual_$sinterpretAst{(x) v r6IPU} (fun)
 +4644864000  alloc           0 ->  4644864000  entries         0 -> 108864000  HordeAd.Core.OpsConcrete.$fBaseTensorConcrete_goS{(x) v rcqRJ} (fun)
 -4644864000  alloc  4644864000 ->           0  entries 108864000 ->         0  HordeAd.Core.OpsConcrete.$fBaseTensorConcrete_goS{(x) v rcqRq} (fun)
 +3773952064  alloc           0 ->  3773952064  entries         0 -> 217728004  TestGatherSimplified.$sinterpretAstDual_$sinterpretAst{(x) v rIsS} (fun)
 +2322432000  alloc           0 ->  2322432000  entries         0 ->  36288000  interpretAst_sat_t6JxS (HordeAd.Core.AstInterpret) (fun)
 -2032128000  alloc  2032128000 ->           0  entries  36288000 ->         0  $sinterpretAst_sat_t19QsN (HordeAd.ADEngine) (fun)
 +2032128000  alloc           0 ->  2032128000  entries         0 ->  36288000  HordeAd.Core.OpsConcrete.$w$sfromLin{(x) v rcqPG} (fun)
 -2032128000  alloc  2032128000 ->           0  entries  36288000 ->         0  HordeAd.Core.OpsConcrete.$w$sfromLin{(x) v rcqPn} (fun)
 -2032128000  alloc  2032128000 ->           0  entries  36288000 ->         0  karg (HordeAd.ADEngine) (fun)
 +2032128000  alloc           0 ->  2032128000  entries         0 ->  36288000  karg (TestGatherSimplified) (fun)
 +1451520168  alloc           0 ->  1451520168  entries         0 ->         1  pap_tcZaR (HordeAd.Core.OpsConcrete) (fun)
 -1451520168  alloc  1451520168 ->           0  entries         1 ->         0  pap_tcZay (HordeAd.Core.OpsConcrete) (fun)

## Task 8 D: NOINLINE Dict0 loop breaker for the Concrete dictionary cycle (patched HEAD, no CBV, INLINEABLE [1])
- $ctlambda exported as StableUser (no longer loop-breaker); test module Core has 0 calls to unspecialised partial copies (10 before).
1 INLINEABLE exit=0 passed (32.27s)
1 D-INLINEABLE1 exit=0 passed (44.78s)
1 INLINEABLE1 exit=0 passed (44.52s)
2 INLINEABLE exit=0 passed (31.69s)
2 D-INLINEABLE1 exit=0 passed (44.47s)
2 INLINEABLE1 exit=0 passed (44.29s)
3 INLINEABLE exit=0 passed (31.25s)
3 D-INLINEABLE1 exit=0 passed (44.45s)
3 INLINEABLE1 exit=0 passed (44.41s)
- No runtime effect: the remaining dictionary-passing work is outside the test module (D-ticky queued).

## Task 8 E: unpatched nightly HEAD, INLINEABLE [1], no CBV; E2 adds -flate-specialise on the test module
1 INLINEABLE exit=0 passed (31.62s)
1 E1-nightly-INLINEABLE1 exit=0 passed (57.60s)
1 E2-nightly-late-INLINEABLE1 exit=0 passed (279.89s)
2 INLINEABLE exit=0 passed (31.56s)
2 E1-nightly-INLINEABLE1 exit=0 passed (56.91s)
2 E2-nightly-late-INLINEABLE1 exit=0 passed (283.71s)
3 INLINEABLE exit=0 passed (31.24s)
3 E1-nightly-INLINEABLE1 exit=0 passed (57.22s)
3 E2-nightly-late-INLINEABLE1 exit=0 passed (280.55s)

## Task 9: ticky E1 vs E2 (nightly, INLINEABLE [1], no CBV; E2 +-flate-specialise on the test module)
- E2: total alloc 45.6 GB -> 37.4 GB (0.82), entries 2.65 G -> 2.10 G; hot path fully specialised in the test module (435M entries). Yet 280 s vs 57 s: the time is not in allocation or entries (RTS -s queued).

## Task 8 F: {-# SPECIALISE interpretAst @Concrete #-} in AstInterpret (+ imports), INLINEABLE [1], no CBV; F1 patched, F2 nightly
1 INLINEABLE exit=0 passed (31.36s)
1 F1-patched-spec-INLINEABLE1 exit=0 passed (34.99s)
1 F2-nightly-spec-INLINEABLE1 exit=0 passed (34.65s)
1 INLINEABLE1 exit=0 passed (44.52s)
2 INLINEABLE exit=0 passed (31.31s)
2 F1-patched-spec-INLINEABLE1 exit=0 passed (35.27s)
2 F2-nightly-spec-INLINEABLE1 exit=0 passed (34.83s)
2 INLINEABLE1 exit=0 passed (44.29s)
3 INLINEABLE exit=0 passed (31.37s)
3 F1-patched-spec-INLINEABLE1 exit=0 passed (35.29s)
3 F2-nightly-spec-INLINEABLE1 exit=0 passed (34.79s)
3 INLINEABLE1 exit=0 passed (44.39s)

## Task 9: RTS -s, E1 vs E2
E1-nightly-INLINEABLE1 exit=0 passed (61.82s)
  78,953,943,624 bytes allocated in the heap
     246,512,384 bytes copied during GC
     326,800,480 bytes maximum residency (3 sample(s))
  MUT     time   61.018s  ( 60.814s elapsed)
  GC      time    1.058s  (  1.039s elapsed)
  Total   time   62.088s  ( 61.864s elapsed)
  Productivity  98.3% of total user, 98.3% of total elapsed
E2-nightly-late-INLINEABLE1 exit=0 passed (278.21s)
 748,905,087,896 bytes allocated in the heap
         662,496 bytes copied during GC
     326,799,848 bytes maximum residency (3 sample(s))
  MUT     time  278.015s  (277.151s elapsed)
  GC      time    1.077s  (  1.093s elapsed)
  Total   time  279.143s  (278.257s elapsed)
  Productivity  99.6% of total user, 99.6% of total elapsed
- E2 allocates 749 GB against E1's 79 GB (9.5x), all short-lived (662 KB copied by GC); ticky, which covers only the local packages, counts less for E2, so the extra ~670 GB is allocated in store-built dependency code.
- E2's test-module Core passes Storable dictionaries at runtime (1631 refs vs 97 in E1), e.g. orthotope's constant ($fStorableDouble |> co) ...: unspecialised generic array code inlined per scalar type into the late specialisations. Parked: the SPECIALISE workaround (F) needs no late specialisation.

## G build result (2026-09-30)
- G build 2141 s (aicbv 2675, cbv 2329). Object sizes -21.5%: the @Concrete copy of interpretAst lives once in AstInterpret
  (+760 KiB) instead of ~2.65 MB in each importer (ADEngine, every test/bench module). Benchmarks of G running.
- Queued experiment H (expH.sh, job-H.out, dist-H): no phase, INLINEABLE + SPECIALISE @Concrete; tests whether the compile-time
  win comes without the phase. Starts when job-G.out has DONE.
- G allocation, prod: every symbolic grad benchmark up (k MapAccum +43..51%, s MapAccum +16%, 1000/grad k L +7%), cgrad identical:
  the single AstInterpret copy is less optimised than the per-importer copies (suspect the tlambda callback path).
- G MNIST rank-1 VTO +5..20% (1500|500 +19.6%); conv gather48 fused +23% (worse than the cbv baseline), scatter48 +12%, cnn-6x6 +5%.
  G as is loses the CBV gains; timings pending; H (no phase) decides whether the pragma is usable at all.
- Diagnosis: @Concrete leaves span s abstract -> runtime knownSpan/dictSpanFam per call. H superseded (expH-superseded.sh, never ran).
  Queued G2 (expG2.sh, job-G2.out, dist-G2): INLINEABLE [1] + SPECIALISE per span (@Concrete @FullSpan/@PrimalSpan/@DualSpan/@PlainSpan) + @Concrete.

## Other GHC behaviour seen, none a confirmed third bug (for the final report; Mikolaj asked to record these)
1. specImport recursion guard (Note [Avoiding recursive specialisation]): with a phase on interpretAst, the recursive
   existential-span calls interpretAst @Concrete @s stay dictionary-passing at runtime (217.7M of 435M interpreter entries);
   the main remaining #26827 phase gap. Documented, deliberate; at most a feature request (let the guard admit less-specialised
   recursive calls). Not drafted.
2. -flate-specialise on unpatched HEAD: 281 s vs 57 s, 749 GB allocated vs 79 GB; late specialisations call generic orthotope
   array code with runtime Storable dictionaries. With the alreadyCovered fix the same setup runs 33 s, so most likely that bug
   amplified by #23050 rather than a separate one. UNVERIFIED: Mikolaj asked for a small reducer, with and without the fix
   (to do after G2).
3. G: a partial user `SPECIALISE interpretAst @Concrete` in the defining module stops importers making the full known-span
   specialisations they made before ("user rules dominate" in alreadyCovered): documented rule, our pragma's fault. G2 tests
   one pragma per span.
4. Loop breaker on $fBaseTensorConcrete_$ctlambda (recursive Concrete dictionary): legitimate choice; moving it (D) gained nothing.

## CBV draft fix (2026-09-30)
- Chain: c56567ec (#26722) makes mkStrictFieldSeqs add an eval on every strict CBV worker arg (before: skipped when strictly
  demanded); refineDefaultAlt refines the eval's DEFAULT to CTuple2 (05094993/#27071 exempts only unary classes); be7296c909
  removed specCase's handling. Exported worker unfolding passes the case binder in recursive calls.
- Candidate fix: `not (isDictId arg_id)` in mkStrictFieldSeqs (perf/cbv-dict-noeval.patch). Building stage1 with both fixes
  (expCBVfix.sh, job-CBVfix.out, log ghc-build-cbvfix.log); binaries: _build/stage1/bin/ghc-acfix (alreadyCovered only),
  ghc-acfix-cbvfix (both). Then: reproducer check; update draft (drop "not yet tested"), amend? (new commit, pushed already).
- Reproducer with both fixes (ghc-acfix-cbvfix, stage1 rebuild 39 s): Repro fully specialises f and g ($w$s$wf <-> $w$s$wg),
  the exported worker unfolding has no CTuple2 case. Running expPF.sh (job-PF.out, pf/): repro-inlineable100 CAFlessTest,
  plain INLINEABLE, CBV ON, PF (both fixes) vs PA (acfix only) vs NOCBV; repro worktree restored by the script.
- Dictionary shapes (nightly HEAD, -fworker-wrapper-cbv on Lib): constraint tuple, `Num t` alone, a class with 2 superclasses,
  and a UNARY class all break the cascade (unary: worker keeps `case $dU of $dU1 { DEFAULT -> ... $wg $dU1 ...}`, so DALT3
  exemption does not help; calls pass the case binder). Without the flag all specialise. Patched compiler (both fixes) fixes
  Num and unary too. => CBV draft is too narrow: not constraint-tuple specific; reproducer can use `Num t`; workarounds should
  say changing the constraint shape does not help; DALT3 remark is now demonstrated, not "probably". Tests in /tmp/claude-0/wa.
- alreadyCovered draft re-verified 2026-09-30 claim by claim (/tmp/claude-0/acv/verify.py; head, fix, fix+cbv, 9.14.1, 9.12.2):
  all hold. No duplicate found on the tracker. Edits in working tree, UNCOMMITTED: header re-verified line; 1fd259874d (#23559)
  named as what turned -fpolymorphic-specialisation on; Related adds #23559, #26827 = closed as subsumed by #26851/#26826/#26895;
  Repro rule name with @(*).
- #26895 check (pf/): NOCBV 48.78/46.54/38.57, PF 34.80/34.96/31.96, PA 60.74/57.52/60.10 s (machine noisy/slower after
  restart). Allocation check +RTS -s running.
- GHC tracker comments ARE readable: GraphQL (https://gitlab.haskell.org/api/graphql, project ghc/ghc issue notes) or
  https://gitlab.haskell.org/ghc/ghc/-/issues/N/discussions.json; the REST notes API needs a token.
- #26816 (Mikolaj): SPJ: short-cut solving is typechecker-only; the simplifier will not replace a pattern-bound Num Int dict
  by $fNumInt; cure = hand-written specialised copy + RULE (Mikolaj's experiment 3). Explains why the remaining #26827 gap
  (constructor-bound dictionaries) resists specialisation tweaks.
- G: VTO time 1.090 vs aicbv, alloc +20%; stopped. G2 (per-span SPECIALISE) queued by hand after the GHC work.

## In flight at the time of writing
- Experiment G (job /home/user/variants/job-G.out, script expG.sh): current horde-ad in /home/user/hb with interpretAst
  `INLINEABLE [1]` + `{-# SPECIALISE interpretAst @Concrete #-}` (+ imports of CarriersConcrete (Concrete) and
  OpsConcrete ()) + per-module no-CBV, nightly HEAD. Full timed build into dist-G, then allocation of the three suites
  (alloc/G-*.json, compared with alloc/aicbv-*.json by alloc-cmp.py), then tools/ab-time.py G vs aicbv on VTO MNIST
  1500|500, gather48 fused, cnn-6x6/S-exec, cnn-24x24/S-exec, inp-192x192/H-term, 1000/grad k L, 100/cgrad k NotShared.
  The script restores hb's AstInterpret.hs after the build. Fill "RESULT-G" in summary.md from its output.
- Next ideas after G: decide recommendation for horde-ad (per-module CBV opt-out: yes by the rules, +15% compile time;
  phase on interpretAst: viable with the SPECIALISE pragma if G confirms); possibly a GHC enhancement note on the
  specImport recursion guard (less-specialised recursive calls could be allowed).

## #27874 and -fpolymorphic-specialisation (checked 2026-09-30, /tmp/claude-0/psv)
- Filed reproducer (Num t, constant Double dict), Lib with -fworker-wrapper-cbv, both modules +/- -fpolymorphic-specialisation:
  9.12.2 and 9.14.1 specialise both f and g in all four cells; HEAD leaves `$wg $fNumDouble` in both cells. The flag is
  irrelevant: the prerequisite is c56567ec's eval on a strictly-demanded dictionary, absent before HEAD.
- Lazily-demanded dictionary variant (f :: Num t => t -> E -> t, L branch returns d): unaffected on all three, HEAD too.
- Polymorphic-dictionary variant (run :: RealFloat a => E -> Complex a): no specialisation of f at all on any compiler or
  flag set (also with -fspecialise-aggressively -fexpose-overloaded-unfoldings), so it says nothing either way.
- #27873 is different: it does need -fpolymorphic-specialisation on 9.12.2/9.14.x, as its draft already says (line 112, Environment).

## chain3 results (2026-09-30 evening)
- Compile (post-restart machine): base 2782 s, G2 2255 s (-18.9%), X3 2226 s (-20.0%). Importer objects identical in G2/X3.
- Allocation vs aicbv: G2 and X3 identical to 0.02%: conv neutral (107, max +0.26%), MapAccum fixed, cgrad 1.0000;
  residual: 1000/grad k L +7.5%, grad k L/R +4%, VTO 1500|500 +10.5% (VTO = artifact built once, interpreted per iter:
  pure interpretation -> banned category).
- Time (7 pairs): G2 VTO 1.057, gather48 1.064, grad k L 1.171 (noisy); X3 VTO 1.030, gather48 1.018, grad k L 1.146;
  controls within noise (X3 cnn-24x24 0.910!). cachegrind queued: /home/user/variants/cg3.sh -> job-cg3.out.
- So the #26816 hand-written-copy cure buys nothing over per-span SPECIALISE pragmas; both leave a residual on
  interpretation vs importer-side specialisation (aicbv). Cause not yet diagnosed.

## Task 10: E2 (-flate-specialise on unpatched HEAD) cause and minimal reproducer (2026-09-30 evening)
- 7x7 detSquare in /home/user/repro (late7.sh, /home/user/variants/late7/): E1 0.09 s 78 MB, E2 0.54 s 730 MB -- reproduces.
- callgrind E2: ~1/3 of instructions in Typeable TypeRep construction: __hsbase_MD5Transform 16.8%, peekW64 12.3%,
  MD5Final/Update, pokeW64, fingerprintFingerprints, mkTrCon, pinned byte arrays (564,609 MD5Final calls). E1: none.
- Core: in $sinterpretAst_$sinterpretAstDual_$sinterpretAst3, the AstCastK alternative has
  `let { $dTypeable2 = mkTrCon $tcDouble [] } in case sameTypeRep $dTypeable2 (typeRep# ..) of ... sameTypeRep (mkTrCon $tcFloat []) ..`
  i.e. the eqT dispatch of Concrete's cast, inlined from its stable unfolding into a case alternative of a late
  specialisation. No float-out runs after late specialisation, so the constant TypeReps (MD5 fingerprints) are rebuilt
  on every call. E1 has 3 mkTrCon, E2 327. (The earlier "static Storable dict" reading was a side issue.)
- Minimal reproducer: /home/user/variants/late-repro/{Lib,Main}.hs (copy of /tmp/claude-0/lt). INLINE ifDouble (eqT @a @Double),
  INLINABLE recursive sumD using it, NOINLINE h with a phase-0 RULE h xs = sumD xs 0 so that the call is missed by the
  regular specialiser and caught by the late one. `ghc -O [-flate-specialise] Lib.hs Main.hs`:
    9.12.2   plain 64 MB 0.025 s | late 560 MB 0.274 s
    9.14.1   plain 64 MB 0.023 s | late 560 MB 0.262 s
    HEAD     plain 64 MB 0.026 s | late 1232 MB 0.338 s (nightly bindist)
    HEAD+fixes plain 64 MB 0.027 s | late 568 MB 0.244 s (source build with #27873 and #27874 fixes)
  Late Core: `case sameTypeRep lvl1 (mkTrCon $tcDouble []) of` inside the loop of $ssumD.
- So E2 = #27873 leaves the interpretAst calls to the late specialiser + late specialisation's missing float-out.
  The second is old (9.12 too), independent of both filed bugs. Candidate third issue; tracker not searched for duplicates.
- Smaller reproducer (/home/user/variants/late-repro-small/, 10-line Lib + 3-line Main): INLINE isD x = typeOf x == typeOf (0 :: Double);
  INLINABLE recursive f n acc; Main `print (f 1000000 (0 :: Double))` compiled with -O -fno-specialise [+ -flate-specialise]
  (-fno-specialise stands in for "regular specialiser missed the call"). Adding -flate-specialise: 9.12.2 0.03 -> 0.245 s,
  72 -> 544 MB; 9.14.1 0.029 -> 0.244 s; HEAD 0.030 -> 0.34 s (1184 MB); HEAD+fixes 0.028 -> 0.247 s. Regular spec: 0.006 s.
  Late loop Core: `case mkTrCon $tcDouble [] of ... sameTypeRep` per iteration. Needs two modules (single-module late spec
  uses the optimised RHS, already floated) and the INLINE helper (evidence directly in f sits at the top of f's unfolding
  and the post-late-spec simplifier floats it). Pipeline.hs line 309: late spec after the last CoreDoFloatOutwards.

## Task 11: #26827 phase gap, small reproducer and a prototype GHC fix (2026-09-30 night, Mikolaj away)
- Write-up summary.md: section 4 (G, G2, X3) and section 5 (late-spec) filled; tasks 5 and 10 closed.
- cachegrind per call vs aicbv: G2 VTO +6.3% instr/+6.7% cyc, grad k L +4.8/+4.1, gather48 +1.1/+3.9;
  X3 VTO +6.25/+6.7, grad k L +4.9/+4.0, gather48 +1.1/+1.1. G2 = X3 (residual undiagnosed).
- Reproducer /home/user/variants/phasegap/{Lib,Repro}.hs (Lib has PHASE placeholder: sed to "" or "[1]"):
  interp :: (Tgt t, KS s) => Expr s -> t over GADT with Sub :: KS s2 => Expr s2 -> Expr s (existential span) and
  Prim :: Expr Full -> Expr Dual. Flags (both modules): -O -fexpose-overloaded-unfoldings -fspecialise-aggressively
  -fdicts-cheap -fkeep-auto-rules. With ghc-acfix-cbvfix (both fixes): no phase 0.010 s 7 MB; [1] 0.034 s 37 MB,
  Core `Sub @s2 $dKS e1 -> interp $fTgtD $dKS e1`. No phase: Main has "SPEC/Main interp @D @_" (reached via Lib's
  active rule interp @_ @Full -> interp_$sinterp, so interp is not on the specImport stack). Nightly: [1] blocked by #27873.
- Prototype: Specialise.hs spec_import: callers stack carries call keys; a call of a function on the stack is
  specialised iff strictlyMoreGeneral than all its stack keys (fewer Spec args, same SpecTypes) -> terminates.
  Saved pre-patch file: /home/user/variants/perf/Specialise.hs.acfix. Build: buildGuard.sh -> ghc-guard.
- 2026-09-30 night, Mikolaj asked: deleted /usr/lib/llvm-18, /usr/lib/jvm/java-21-openjdk-amd64, /usr/lib/libreoffice,
  /opt/pw-browsers (no -fllvm, no java, no Chromium/Playwright any more). Disk 4.4G -> 6.2G free.
- Guard experiment (repro-inlineable100 CAFlessTest, CBV on): builds GP1 1054 s, GP0 981 s, F1 984 s.
  Round 1: PF0 32.46, GP0 31.76, GP1 32.22, F1 46.47. Round 2: PF0 31.59, GP0 31.46, GP1 31.44, F1 46.38.
  => relaxed guard closes the phase gap: INLINEABLE [1] 46.4 s -> 31.4-32.2 s = plain INLINEABLE.
- Queued: expTSguard.sh (full GHC testsuite + perf/compiler metrics for ghc-guard) after the runs.
  Round 3: PF0 31.41, GP0 31.19, GP1 30.71, F1 45.58. Means: PF0 31.8, GP0 31.5, GP1 31.5, F1 46.1.
- LLVM deletion broke linking: every GHC here (nightly, 9.12, 9.14, stage1) links with -fuse-ld=lld and merges with
  ld.lld. Reinstalled lld-18 and libllvm18 via apt (/usr/lib/llvm-18 now 123 MB, not 388). All four GHCs link again.
  The first expTSguard run failed at once on this (all tests skipped); rerun.
- Testsuite rerun (ghc-guard, 2026-09-30 ~18:15): optllvm-way tests fail "Failed to detect LLVM version!" since llc/opt
  are gone (only lld + libllvm18 reinstalled). Filter (optllvm) failures when comparing with the cbvfix run
  (perf/ts-full-cbvfix-summary.txt, which had LLVM). The first, stale run's output is in perf/stale/.
- Draft docs/ghc-issue-specimport-recursion-guard.md (uncommitted); TESTSUITE-PENDING in header; patch = perf/guard-only.diff (Note paragraph placed after the 'callers' sentence; the built binary has it one sentence earlier, comment only). After the testsuite: move the Note paragraph in /opt/ghcsrc too.
- recursion-guard draft: first Summary paragraph added (5x alloc, MUT 0.012 vs 0.005-0.006 s = 2.0-2.4x, 5 interleaved runs, ghc-acfix-cbvfix).
- ghc-guard testsuite (18:10, 1421 s): 11777 expected passes, 25 unexpected failures, all (optllvm) for lack of llc/opt; 11777+25 = 11802 = cbvfix run's expected passes. perf/compiler step running.
- Pushed 480906a1 (guard draft + late-spec draft corrections, one commit, rebased onto 645dd5c2 'Pragma-removing work diary' from another session). Guard draft still says perf/compiler metrics not measured: update when perf-guard.tsv is in (needs go-ahead to commit). RULES/phase demo: /tmp/claude-0/rl (plain INLINABLE g: rule f/g never fires, prints 4, -Winline-rule-shadowing; INLINABLE [1]: fires, prints 0; HEAD and 9.14.1).
- perf/compiler guard vs cbvfix: 101 bytes-allocated metrics, max +0.0148% (T13701), min -0.0021% (T5837); 115 expected passes, 0 unexpected. Draft updated (uncommitted). /opt/ghcsrc Specialise.hs Note placement fixed (comment only; ghc-guard binary not rebuilt).
- Amended + force-pushed (lease on 480906a1) as 7fcca259: guard draft with perf/compiler metrics.
- FILED 2026-09-30: GHC #27879 (no float-out after -flate-specialise) and GHC #27880 (specImport recursion guard). Drafts marked filed; amended + force-pushed (lease 7fcca259) as 3a37e54d. Don't check them on the tracker.
- Pragma matrix under ghc-guard (CBV on, 3 interleaved rounds, tasty totals): builds GI1 1104 s, GN1 1049 s, GP99 1014 s.
  Means: INLINEABLE 28.30, INLINE [1] 29.68, NOINLINE [1] 28.54, INLINEABLE [99] 29.53, INLINEABLE [1] 27.84 s.
  All phase-annotated pragmas now within 5% of plain INLINEABLE (before: +36..39%). INLINE [1] and [99] are slower than
  plain in all 3 rounds (+4.9%, +4.3%): small residual, not investigated. => #26827 phase gap closed by GHC #27880's fix.
(job-hbguard.out truncated 2026-09-30: first copy's contaminated FX 2615 s discarded; its dist-FX/dist-GD deleted)
- expHBguard: first launch's deps step failed (--only-dependencies refused: local knownnat), but the script continued, so its FX build overlapped the relaunch's warm-up (FX 2615 s contaminated). All copies killed by pid, dist-FX/GD/deps deleted, script now exits on failure; relaunched once, alone. Lesson: every chained timed step must stop on failure.
- 21:03 container restart killed expHBguard during warm-up; relaunched (dist-deps reused, timed builds fresh).
- expHBguard: FX (acfix+cbvfix, hb aicbv source) whole-package build 2416 s (post-2nd-restart machine; compare only with GD of this run).
- expHBguard: GD (with #27880 guard) whole-package build 2382 s vs FX 2416 s (-1.4%, noise): no compile-time cost on current horde-ad (plain INLINEABLE).
- expHBguard DONE. GD/FX allocation (current horde-ad, aicbv source): prod 23 benchmarks max +0.03%, MNIST 28 all 1.0000,
  conv 107 within -0.06..+0.08%. So the #27880 fix is neutral on current horde-ad (plain INLINEABLE): no allocation
  change, no compile-time cost (2382 vs 2416 s). Its effect is only where a phase is used (repro: 46.1 -> 31.5 s).
- Bonus: FX (acfix+cbvfix) vs nightly aicbv, same source: prod geomean 0.992 (100/grad k list -6.9%), MNIST 0.994
  (VTA -4%), conv 0.9996: the #27873/#27874 fixes help current horde-ad a little even with per-module no-CBV.

## STATE AT THIRD COMPACTION (2026-10-01)
- Filed and pushed: GHC #27873, #27874, #27879 (no float-out after -flate-specialise), #27880 (specImport recursion
  guard). Branch drop-recursive-inline pushed at 3a37e54d, tree clean (notes file excluded). Don't check filed issues.
- #26827 phase gap: closed by the #27880 fix (ghc-guard = /opt/ghcsrc/_build/stage1/bin/ghc-guard: acfix + cbvfix + guard).
  Matrix under it (repro CAFlessTest, CBV on): all phase pragmas within 5% of plain INLINEABLE (27.8-29.7 s vs 28.3).
  Testsuite: all pass except 25 optllvm (no llc/opt installed); perf/compiler 101 metrics within 0.015%.
  Whole horde-ad (hb, aicbv source): guard neutral (build 2382 vs 2416 s; allocation identical on 3 suites).
- Running: /home/user/variants/expG2G.sh -> job-G2G.out (G2 source = per-span SPECIALISE in AstInterpret, built with
  ghc-guard; allocation vs GD = alloc/GD-*.json). Question: does #27880 remove G2's residual (+10.5% VTO alloc,
  +6% instr)? If yes, specialising once in AstInterpret (-19% compile time) becomes viable. Then: cachegrind VTO G2G vs GD
  (dist-GD kept for that), and update summary.md.
- Environment after 2 restarts: LLVM tools deleted (lld-18 + libllvm18 reinstalled, needed for linking); /opt/pw-browsers,
  JVM, LibreOffice deleted. Detached jobs do NOT survive a restart: check job outputs and relaunch.
- Lesson recorded: chained timed scripts must exit on any failure (expHBguard double-run).
- Two cabal.project.local files (repro: head.hackage stanza; hb: lean) -- historical; unify after the series.

## G2G results (2026-10-01, post-3rd-compaction)
- G2G (G2 source, ghc-guard) whole-package build 2385 s vs GD 2382 s (same compiler, same machine state):
  the 19% compile-time saving of G2 on nightly (2255 vs 2782) is GONE with the fixed compiler.
  Importers still shrink (ADEngine 2872 -> 168 KiB, convVjpBench Main 4252 -> 1532, TestGatherSimplified
  7568 -> 4852), AstInterpret 688 -> 3824 KiB; the time no longer shows.
- Allocation G2G/GD: prod geomean 1.0021 (max 1.0132; grad k L +1.2%, was +7.5% on nightly G2) -- guard fixed prod.
  MNIST geomean 1.0067, VTO 1500|500 +10.48%, 500|150 +4.9%, 300|100 +3.3% -- UNCHANGED from G2 on nightly.
- So: guard does not remove the VTO residual; and G2 has no compile-time motivation left.
- conv G2G/GD: 107 benchmarks geomean 1.0000, max +0.12% -- neutral. expG2G DONE.
- Hypothesis for VTO residual: G2's specialised copies are compiled in AstInterpret, which has
  -fno-worker-wrapper-cbv (aicbv source); GD's copies are compiled in importers with CBV on.
  Test: /home/user/variants/expG2C.sh -> job-G2C.out (G2 minus the no-CBV line, ghc-guard, dist-G2C;
  alloc MNIST + prod vs GD). Launched 2026-10-01 ~01:00 UTC. Pending user question: diagnose or stop G2 line.
- G2C (G2 minus no-CBV line, ghc-guard): build 2302 s (G2G 2385, GD 2382); MNIST alloc vs GD identical to G2G
  (geomean 1.0067, VTO 1500|500 +10.48%). CBV hypothesis REFUTED.
- cachegrind per call VTO 1500|500 (1 vs 2 iters, no cache sim; /home/user/variants/cgfun, perfn.py):
  GD 20.71 G Ir, G2G 22.00 G (+6.3%). Hot copy in BOTH is the SPAN-ABSTRACT Concrete copy
  (KnownSpan s => ...): GD ADEngine $w$w$sinterpretAst 1.79 G; G2G AstInterpret interpretAstDual_$sinterpretAst
  (from the plain `SPECIALISE interpretAst @Concrete`) 3.79 G (+2.0 G). stg_BLACKHOLE_info +0.51 G,
  GC less (evacuate -1.0 G, scavenge -0.34 G). Per-span copies are cold in both (~80-90 M).
  Same type and strictness <SP(SL)><1L><1L>; GD's is a CBV worker, G2G's has no worker (no-CBV module),
  but G2C (CBV workers present) allocates the same as G2G, so CBV is not it.
- Next: dumpCore.sh -> job-dump.out: -ddump-simpl/-ddump-stg-final of ADEngine (GD) and AstInterpret (G2G), lib only.
- Core/STG dumps (lib-only rebuilds, dist-GD ADEngine, dist-G2G AstInterpret; extracted to variants/cgfun/*-hot.{core,stg}):
  hot copies structurally near-identical (thunks 306 vs 308, lets 422/422, self calls 126/126, DualSpan copy calls 78/76).
  STG diff not decisive. BLACKHOLE +0.5 G may be the CBV difference (G2C cachegrind never run), separate from +10% alloc.
- dist-G2C deleted (disk). Running expTicky.sh -> job-ticky.out: -ticky builds (whole local pkg) dist-GDt / dist-G2Gt,
  shortMnistForCI VTO 1500|500 at 1 and 2 iters, +RTS -r -> variants/ticky/. Diff per-closure alloc to locate the +10%.
- TICKY (variants/ticky, tdiff.py; per call = 2 iters - 1 iter): hot span-abstract copy entered 51,179,120 times in both;
  alloc GD 2,048 MB vs G2G 2,866 MB: +818 MB = the whole +10% (benchmark totals 7796 -> 8613 MB), ~16 B per entry.
  CAUSE: the three `interpretAst env <$> ix` (AstInterpret.hs lines 185, 206, 242) inline to a local letrec `fmap'`
  (free var env only). In G2G (AstInterpret's copy) ONE fmap' closure is let-bound at the top of the function
  (inside the join point every alternative takes), used in 3 branches -> allocated on every entry. In GD (ADEngine's
  copy) there are three `$w$wfmap'` (InlPrag=[2], CBV workers), each inside its own branch. Looks like float-out
  lifted them to env's level and CSE merged them (float-in can't sink one binding used in 3 branches). Why the
  pipelines differ between defining module and importer: not root-caused (InlPrag=[2] in GD hints the fmap' came
  from a different unfolding path). Not CBV (G2C same alloc).
- Small program (variants/fmaprepro: Ox.hs ListX/IxX/IxS like ox-arrays, Lib.hs interp with
  `interp !env | Dict <- mkDict (sing @s) = \case` and three `interp env <$> ix`, run.sh; ghc-guard, horde-ad flags):
  * without the guard: no difference, fmap' stays in each branch in both variants.
  * with the guard, importer span-abstract copy (Main `go :: KnownS s =>`, NOINLINE): arity 3, ONE fmap' let-bound at
    the top, after the mkDict case, allocated per call: the horde-ad G2G pattern. 394 MB.
  * defining-module `SPECIALISE interp :: KnownS s => Int -> E s -> Int` + INLINABLE [1]: arity 2, not eta-expanded
    (a floated PAP thunk `interp_$sinterp $dKnownS env` blocks it), f/fmap'/lvl/lambda all allocated per call. 957 MB.
  So the class is: full laziness floats `fmap (interp env)` out of the `\case` lambda that follows non-cheap guards,
  CSE merges the copies, and nothing sinks them back. Which module shows it depends on details; not a clean GHC bug yet.
- Small program, term bound as an argument (`interp !env t | Dict <- ... = case t of`): both variants 198 MB
  (vs 394 importer / 957 defining-module with `= \case`); no hoisted fmap'.
- Running expGA.sh -> job-GA.out: aicbv source with `interpretAst !env t0 | ... = case t0 of` (only change),
  ghc-guard, dist-GA, whole-package build time + alloc on 3 suites vs GD. A horde-ad candidate (no pragma).
- GA (argument form `interpretAst !env t0 | ... = case t0 of`, ghc-guard) vs GD: allocation identical on all 3 suites
  (prod 1.0000 [0.9998,1.0003], MNIST 1.0000 [1.0000,1.0000], conv 1.0000 [0.9998,1.0004]). Build 2308 s vs 2382 s,
  but G2C (unrelated change) was 2302 s in the same late window, so likely machine drift, not the change. No gain
  for current horde-ad; it would only matter for G2-style specialisation. dist-GA deleted (disk).
- Small program flag toggles (variants/fmaprepro/run2.sh; `\case` form; importer GD / defining-module G2G, MB):
  default 394 / 957; -fno-full-laziness 1027 / 1291; -fno-cse 198 / 4683; -fno-dicts-cheap and
  -fno-specialise-aggressively no change. So in the importer variant CSE is what merges the floated fmap's into one
  per-call closure (without CSE: 198, same as the argument form). The defining-module variant is a different
  problem (copy not eta-expanded; -fno-cse makes it far worse). Possible GHC issue draft, pending the user's answer.
- Importer variant across GHCs (run3.sh; `\case` vs argument form, MB): 9.12.2 2272 / 1283, 9.14.1 2272 / 1283,
  nightly 394 / 198, ghc-guard 394 / 198. The `\case`-after-guards penalty is old (all versions ~1.8-2x); 9.12/9.14
  allocate more overall because they don't specialise the span-polymorphic call (no -fpolymorphic-specialisation).
- Single-module attempt (variants/fmapmin: `eval k | check k = \case`, NOINLINE check, three `mapS (eval k) ix`):
  5x more allocation than the argument form on 9.12.2/9.14.1/nightly (560 vs 112 MB), but the cause there is
  plain arity: $weval has arity 1 because GHC won't eta-expand over the non-cheap guard (correct, not a bug).
  -fno-cse 4147 MB, -fno-full-laziness 1101 MB. horde-ad's copies have arity 3 (dictSpanFam returns a dict, cheap
  under -fdicts-cheap), so the horde-ad-relevant case is the 3-module importer one, where CSE merges the floated
  fmap's. Not yet a clean GHC issue. Lesson for horde-ad style: avoid `= \case` after non-cheap guards.
- 2-module program (variants/fmap2m, plain lists, Lib/Main, `run :: KnownS s =>` NOINLINE in Main), -O -fexpose-overloaded-unfoldings:
  nightly `\case` 518 MB, argument form 323, `\case -fno-cse` 323. 9.12/9.14: 2272 / 1283 / 8656 (different effect).
  Pass trace (nightly, -dverbose-core2core): after Specialise `$sinterp = \s d env -> case mkDict.. of Dict -> \ds -> case ds
  of {I1 -> letrec go..; I2 -> letrec go..; I3 -> letrec go..}`; FIRST float-out lifts all three `go` to env's level
  (out of \ds); post-call-arity simplifier eta-expands $sinterp to arity 3 (Call Arity sees all its calls: it's a local,
  non-exported specialisation), so the float shares nothing; late float-out no change; CSE merges the three `go`s
  (`go = go` aliases); float-in can't sink one binding used in 3 alts -> one closure per call.
- The "different effect" (9.12/9.14, no specialisation): exported Lib.interp has arity 3 (dNum dKnownS env), NOT
  eta-expanded over the NOINLINE mkDict call (Call Arity can't see external callers; eta-expanding could duplicate
  mkDict work for shared partial apps), so every call returns a closure and allocates k, f, go, lvl1, lvl2 (~6 closures).
  By design; possible improvement: arity worker/wrapper so the (saturated) self-recursive calls use an eta-expanded worker.
- GHC prototypes (source /opt/ghcsrc, backups variants/perf/{CSE,Pipeline}.hs.orig; --freeze1 rebuild ~55 s):
  * ghc-cselam = ghc-guard + CSE skips local let-bound lambdas (Rec). fmap2m (-O -fexpose-overloaded-unfoldings)
    518 -> 323 (= arg form); -O only 1083 -> 851; fmaprepro importer 394 -> 198 (= arg form), but the
    defining-module (not eta-expanded) variant 957 -> 1264 WORSE (there all copies are allocated per call anyway,
    so merging helped). CSE.hs restored.
  * STALE-OBJECT TRAP: fmaprepro/run.sh reused .o/.hi across compilers with the same version string -> fixed (rm -rf).
  * Next: ghc-fibcse = ghc-guard + an extra float-in pass before the late CSE (Pipeline.hs), building.
- User 2026-10-01 ~07:50: "think and experiment harder so that you find obvious solutions, not patches over patches".
  ghc-fibcse (extra float-in before late CSE): importer 394 -> 262, 2-mod 518 -> 387, -O 1083 -> 755; a patch.
  ROOT: SetLevels floats a let-bound FUNCTION out of a value lambda to an intermediate level (wantToFloat only asks
  profitableFloat = escapes a value lambda). That saves no work, only closure allocation, and only if the escaped
  lambda is applied more than once per outer application; out of a case alternative it adds an allocation on every
  path. The first float-out runs right after Specialise with inaccurate arity (its own comment says so for
  over-saturated apps), and the copy is eta-expanded later anyway.
- ghc-funtop = ghc-guard + SetLevels.wantToFloat: `| is_fun, not (isTopLvl dest_lvl) = False` (backup
  variants/perf/SetLevels.hs.orig; Pipeline.hs and CSE.hs restored). Results (MB):
  fmaprepro importer 394 -> 198 (= arg form), defining-module 957 -> 886; fmap2m -O -fexpose 518 -> 323 (= arg),
  -O 1083 -> 707; fmapmin2 -fno-specialise 912 -> 842; arg forms unchanged. No regression in these.
- Next: horde-ad G2 + GD with ghc-funtop (alloc vs GD), then GHC testsuite perf with ghc-funtop.
- ghc-funtop (blunt) REGRESSES a many-shot lambda: funtopneg/Neg2.hs (`map (\y -> let go = ..x.. in go a * go b)`)
  304 -> 336 MB. ghc-funtop1 = rule only in the EARLY float-out (`not (floatOverSat env)`, the pass GHC itself
  says lacks accurate arity info): Neg2 304 (no regression); fmaprepro importer 394 -> 262 (arg 198), 2-mod
  518 -> 387 (arg 323), -O 1083 -> 755; min2 912 unchanged.
- Remaining 262-vs-198 in fmaprepro: the 'P copy. Lib's own spec `interp_$sinterp` (s='P, Num a polymorphic) is
  NOT eta-expanded in Lib (floated `fromInteger $dNum 0` is a real call between the lambdas), so Lib's LATE
  float-out rightly floats fmap' out of \ds and CSE merges; -fexpose-overloaded-unfoldings exports that optimised
  RHS (vanilla unfolding); Main specialises it at Int, eta-expands it, merged fmap' stays on top. Two causes:
  (1) early float of functions out of a lambda later eta-expanded (funtop1 fixes); (2) float that was right in a
  non-eta-expanded polymorphic copy, carried through the unfolding into an eta-expanded specialisation.
- Queued expFuntop.sh switched to ghc-funtop1 (G2F, GDF vs GD), waiting for dumpPasses.
- horde-ad per-pass dumps (dumpPasses.sh; ghc-guard; -ddump-spec/-float-out/-cse/-float-in):
  GD (ADEngine): right after Specialise the span-abstract copy is `\ @s @y $dKnownSpan env term ->` -- it is
  specialised from interpretAst's STABLE INLINABLE unfolding, which AstInterpret's simplifier had already
  eta-expanded; fmap's sit in their alternatives, no float-out ever crosses a lambda.
  G2G (AstInterpret): the SPECIALISE copy is made from the RHS at the first specialise pass:
  `\ @s @y $dKnownSpan env -> <dict lets, cases> -> \ (ds :: AstTensor ..) -> case ds of ...` (gentle mode does
  eta-expand, but lemPlainOfSpan/dictSpanFam aren't inlined yet so they don't look cheap). FIRST float-out lifts
  the three `interpretAst env <$> ix` fmap's (body lines 104/209/314) above the term lambda (line 591); by the
  late float-out the copy is eta-expanded (no term lambda) with the three fmap's on top; CSE merges.
  => horde-ad's VTO residual is cause (1) exactly; ghc-funtop1 should remove it (G2F running).
- Small single-module reproducer (variants/fmap1s/Repro.hs, 35 lines: `eval k | check k = \case`, NOINLINE check/ev,
  INLINE mapS, three `mapS (ev k) ix`): 582 MB vs 320 MB argument form on 9.12.2, 9.14.1, nightly, ghc-guard;
  -fno-cse 320 on all; three different ev's (no CSE merge) 320; ghc-funtop1 320. Pass trace (nightly):
  gentle -> go's in alts; FIRST float-out lifts 3 go's above \ds; post-call-arity simplifier eta-expands to \k eta;
  CSE merges; float-in leaves one go on top.
  Variants that did NOT isolate cause (1): fmapdef/fmapdef-err (INLINE case guard: gentle eta-expands, no effect),
  fmap1c (same-span index terms: arity effect), fmap1m without run wrapper (spec at known span, eta-expanded early).
- GHC issue DRAFT written: docs/ghc-issue-float-out-before-eta-expansion.md (untracked; staged 2026-10-01, not filed;
  tracker not searched). Prototype diff = variants/perf/funtop1.diff (SetLevels comment shortened to match the draft;
  code identical to the ghc-funtop1 binary). Pending in it: testsuite/perf with prototype, horde-ad G2F/GDF results.
- G2F (G2 source, ghc-funtop1): build 2155 s (G2G 2385, GD 2382, G2C 2302, GA 2308 -- later builds run faster;
  same-compiler comparison will be GDF). Allocation vs GD: prod geomean 0.9999 (max 1.0000; G2G's grad k L +1.2% gone);
  MNIST 1.0000 [0.9998, 1.0001]; VTO 1500|500 rank 1: GD 7,796,523,218 / G2G 8,613,367,694 (+10.48%) /
  G2F 7,796,522,534 (= GD). The VTO residual is entirely the early function float; the prototype removes it.
- G2F conv vs GD: geomean 0.9998 [0.9984, 1.0005]. G2F = GD on all three suites. GDF (aicbv source, ghc-funtop1) building.
- dist-G2G deleted (disk; results recorded).
- User 2026-10-01 ~09:00: "try adversarially to find repros where your change makes performance worse".
  Battery variants/adv (11 many-shot patterns: fused map, comprehension, foldl', loop, IO forM_, NOINLINE HOF,
  shared PAP, nested, one-branch, map, zipWith): all identical guard vs funtop1 EXCEPT H_nested
  (map (\y -> sum (map (\z -> let go .. x .. in go (z mod 3) * go (y mod 5)) [1..10])) ys): 35.4 -> 38.6 MB (+8.8%).
  variants/adv/const (constant calls go 1000 in loops): all identical. variants/adv/heavy:
  H2_heavy (go (1000 + z mod 3) * go (y mod 5)) 2887 -> 3204 MB (+11%), 622 -> 695 ms (+12%);
  H3 (go (1000 + z mod 3) * y) 2886 -> 3203 MB, 636 -> 682 ms (+7%); H4 depth3, H5 identical.
  Mechanism: with go floated early (to x's level), the simplifier shapes the inner loop so the peeled last iteration
  (exitification) calls `$wgo 1001#` with a constant, which the late float-out floats out of the outer loop
  (lvl3 = $wgo 1001#, shared across all y); with go local until the late pass, the call happens before the
  loop-end test and its result is passed to the exit -> 1/10 of the inner work redone per y. So "floating a
  function saves no work" is false in general: an early float can enable later work sharing.
- Refined rule = "spine lambdas": GHC already doesn't split ADJACENT lambdas ("partial applications are fairly
  rare"); a lambda separated from the binding's own lambdas only by lets/cases (\ds after the guard) is the same
  case. Patch (on SetLevels.hs.orig; funtop1 version saved as perf/SetLevels.hs.funtop1): LevelEnv.le_spine
  (True in a binding's body after its own lambdas, through let bodies / case alts / casts / ticks / lambda bodies;
  False in app args/fun and case scrutinee); in the FIRST pass a lambda reached with le_spine bumps only a minor
  level (like one-shot). H's lambdas are map arguments -> unaffected. NOT BUILT YET (waiting: GDF build is timed).
- nofib at /opt/ghcsrc/nofib; nofib-run plan resolves with /opt/ghchead/cabal -w /opt/ghc912/bin/ghc (~40 deps to
  download/build). Do after GDF.
- GDF (aicbv source, ghc-funtop1) build 2478 s vs G2F 2155 s (same compiler!) -- overlapped with my small adversarial
  runs; needs a clean re-timing. With ghc-guard G2G 2385 = GD 2382.
- ghc-spine BUILT (= ghc-guard + spine-lambda rule; ghc lib db now spine). Reproducers (MB): fmap1s 582 -> 320 (=arg),
  fmaprepro importer 394 -> 198 (=arg; funtop1 262), fmap2m -O -fexpose 518 -> 323 (=arg), -O 1083 -> 403 (=arg;
  funtop1 755), fmapev 838 -> 707 (=arg); fmaprepro defining-module 957 unchanged.
  Adversarial: all 20 programs (adv, const, heavy) identical to ghc-guard (H2 605/608 ms, H3 600/585 ms);
  adv/spine P1-P5 (spine lambda surviving with shared PAP, eval PAP, guard + shared PAP, heavy inner loop) identical.
- nofib-run build started (/opt/ghchead/cabal, -w ghc912) -> variants/nofib-build.log.
- nofib A/B (variants/nofibAB3.sh -> nofib-AB3.log, nofib3-{guard,spine}.log; _make/{guard,spine}; nofibcmp.py):
  pitfalls: (1) never edit a running bash script (old process read new lines -> two nofib-run on one Shake db);
  (2) _make/<o>/run.results.tsv aggregate must be deleted before each per-benchmark nofib-run, else Shake skips runs;
  (3) dep-packages are installed from the FIRST invocation's test set (guard lacks random, old-time): retry failures
  after deleting _make/<o>/dep-packages/{.stamp,*.env-file}. I killed my own shell once with a pattern kill (exit 144).
  First 62 benchmarks: spine never worse; spectral/ansi 1266 -> 845 MB (0.668), spectral/lambda 0.9987, rest 1.0000.
  ansi by hand (-O2, arg 400): guard ~1060 ms, spine ~645 ms (-38%); STG: spine specialises `return` to a loop on a
  constant and shares it as a CAF (prog = $sloop1 0#) -- a second-order effect, positive here.
- nofib COMPLETE (118 single-threaded benchmarks, Fast, minus spectral/hartel which doesn't build; 4 guard
  failures retried with refreshed dep-packages): spine/guard allocation geomean 0.9966; spectral/ansi 0.668,
  spectral/lambda 0.9987, real/scs 1.0006 (only regression), all others 1.0000.
- GDF (aicbv source, ghc-funtop1) vs GD alloc: prod 0.9999 [0.9988,1.0003], MNIST 1.0000 [0.9997,1.0001],
  conv 0.9999 [0.9992,1.0005] -- neutral. (funtop1 superseded by spine.)
- Running expTSspine.sh -> job-tsspine.out: full testsuite + perf/compiler metrics with ghc-spine (~25 min + perf).
  Then: horde-ad G2 + baseline with ghc-spine, timed alone in fresh builddirs (G2S, GDS), alloc vs GD.
- TESTSUITE with ghc-spine: 11777 expected passes, 25 unexpected failures = the same optllvm ones (LLVM not
  installed), 0 stat failures. perf/compiler metrics running. dist-GDF deleted; nofib _make binaries/.o deleted
  (results .tsv kept).
- Queued expSpine.sh -> job-spine-hb.out: waits for expTSspine DONE, then G2S (G2 source) and GDS (aicbv source)
  with ghc-spine, each timed alone in a fresh builddir, alloc vs GD. Draft updated to the spine rule + nofib.
- perf/compiler with ghc-spine vs ghc-guard (perf/perf-{guard,spine}.tsv): 147 metrics geomean +0.058%;
  T10370 peak MB +3.2% (noisy), T18698a +1.7% / T18698b +1.4% compile bytes allocated, MultiLayerModulesDefsGhciReload
  peak MB +1.1%; everything else within 0.25%. 0 stat failures.
- 2026-10-01 ~11:20, Mikolaj asked: reinstalled LLVM (apt-get install --reinstall llvm-18 llvm-18-linker-tools
  llvm-18-runtime clang-18 libclang* clang-tools-18 clang-tidy-18 clang-format-18 lldb-18 liblldb-18 python3-lldb-18
  lld-18). /usr/lib/llvm-18 388 MB again; opt/llc/clang 18.1.3 on PATH; -fllvm build with ghc-spine works.
  Remaining dpkg -V "missing" are only man pages (image's dpkg path-exclude). optllvm tests can run again.
- G2S (G2 source, ghc-spine) build 2177 s; prod alloc vs GD geomean 0.9844 (grad k list 0.895, cgrad k list 0.916,
  grad k R 0.945, grad k L 0.948; none worse). MNIST/conv and GDS pending.
- G2S alloc vs GD: MNIST 0.9888 [0.9620, 0.9999]; conv 0.9964 [0.9671, 1.0000] (scatter48 -3.3%). G2S better than GD
  on all three suites, nothing worse. GDS (aicbv source, ghc-spine) building to separate source vs compiler effect.

## STATE AT FOURTH COMPACTION (2026-10-01 ~11:55 UTC)
- VTO residual of G2 DIAGNOSED: first full-laziness pass (right after Specialise, before arity analysis) floats the
  three `interpretAst env <$> ix` local fmap' functions out of the `\case` term lambda of AstInterpret's SPECIALISE
  copy (made from the RHS before eta-expansion); later eta-expanded; CSE merges the copies; float-in can't sink ->
  one closure per call (ticky: +818 MB = whole +10%). GD avoids it: importer specialises the already eta-expanded
  stable unfolding.
- GHC fix candidate = ghc-spine (variants/perf/spine.diff on /opt/ghcsrc; SetLevels le_spine): in the FIRST
  float-out, a lambda on a binding's RHS spine (reached via let bodies / case alts / casts / ticks / lambda bodies)
  starts no new major level; precedent: GHC already doesn't split adjacent lambdas. Superseded ghc-funtop1 (blunt
  "functions only to top level early": regressed H2/H3 by ~11% alloc, ~10% time).
  Evidence: reproducers all = argument form; 25 adversarial programs (variants/adv/{.,const,heavy,spine}) identical
  to ghc-guard; nofib 118 benchmarks geomean 0.9966 (ansi -33% alloc -38% time, lambda -0.13%, scs +0.06% only
  regression); testsuite clean (25 optllvm failures = no LLVM then); perf/compiler geomean +0.058%, max T18698a
  +1.7% bytes, T10370 peak MB +3.2%.
- horde-ad with ghc-spine: G2S build 2177 s; alloc vs GD prod 0.9844, MNIST 0.9888, conv 0.9964, none worse.
  IN FLIGHT: expSpine.sh -> job-spine-hb.out building GDS (aicbv source, ghc-spine) timed alone, then alloc vs GD.
  Compare GDS vs G2S build time (same compiler) and GDS alloc (does spine alone improve GD?).
- GHC issue draft docs/ghc-issue-float-out-before-eta-expansion.md (untracked, in .git/info/exclude; not filed,
  tracker not searched): updated to the spine rule + nofib; still says testsuite/horde-ad pending -> update with
  testsuite/perf results above and horde-ad G2S/GDS. Reproducer variants/fmap1s/Repro.hs (582 vs 320 MB).
- Notes: LLVM reinstalled at user request (optllvm tests can run again). /opt/ghcsrc/_build/stage1/bin/ghc = spine;
  ghc-guard etc. kept. GHC source has spine patch applied (SetLevels.hs), backups in variants/perf/.
- Open questions to user: none pending (they asked: keep diagnosing + draft issue + adversarial testing).
- 2026-10-01 ~13:10: GDS (aicbv source, ghc-spine) build 2436 s (timed alone) vs G2S 2177 s (same compiler);
  under ghc-guard G2G/GD were 2385/2382 s. Object sizes same as under guard (AstInterpret 3831/686 KiB, ADEngine
  166/2873 KiB), so the 10.6% compile-time gap is unexplained: single measurements, not established.
  GDS alloc vs GD: prod 0.9843, MNIST 0.9888, conv 0.9965 (max 1.0002) = G2S to 0.04% (except S-fullpipe-honest
  cnn-12x12 +0.36%, cnn-24x24 +0.11%). So the savings (grad k list -10.5%, cgrad k list -8.4%, grad k R/L -5%,
  VTC -3.8%, scatter48 fused -3.3%) come from the spine compiler alone, on either source; G2's VTO residual is gone.
  Recorded in variants/summary.md section 4 (also root cause written in). dist-G2S deleted (disk 3.7 GB free).
- Running expLLVMspine.sh -> job-llvmspine.out: the 25 optllvm tests with ghc-spine now that LLVM is back.
- 12:27: optllvm rerun with ghc-spine (LLVM 18 back): 25 tests, 32 expected passes, 0 unexpected failures
  (perf/ts-llvm-spine-summary.txt). Testsuite now fully clean with the prototype.
- Draft docs/ghc-issue-float-out-before-eta-expansion.md updated: header (horde-ad G2S/GDS result, no pending runs
  but the duplicate search), testsuite + perf/compiler paragraph, Related horde-ad bullet (savings in either
  build, origin not analysed). Re-read end to end; check-doc-refs --without-siblings and citations clean (wrap
  check can't classify an uncommitted file). Remaining before filing: tracker duplicate search (only when asked).
- Open: G2S vs GDS compile time (2177 vs 2436 s) unexplained, single measurements; re-timing offered to Mikolaj.
- 13:5x Mikolaj: "when I'm not here, find yourself useful work"; order: the compile-time gap, then ironing out the
  draft, then report what else. Launched expRetime.sh -> job-retime.out: GDSr, G2Sr (ghc-spine), G2Gr, GDr
  (ghc-guard), each timed alone in a fresh builddir, sizes recorded, deleted after (dist-aicbv deleted for disk;
  dist-GD and dist-GDS kept for a possible wall-time A/B).
- Draft ironing: GitLab link ranges normalised (#L356-361); cited lines re-verified at 9f48a5b908. Table: added a
  row "HEAD with the fixes of #27873, #27874 and #27880" 582 / 320 / 320 -- its -fno-cse cell (320) is NOT measured
  (no b-guard-nocse run; notes' "on all" meant 9.12/9.14/nightly): TODO run fmap1s with ghc-guard -fno-cse after the
  re-timing (no compiles during timed builds).
- Mikolaj's order after -fno-cse cell: 5 (tracker duplicate search), 4 (fmaprepro defining-module 957 / arity
  effect), 3 (T18698a/b +1.7/1.4%, scs +0.06% explanation), 1 (wall-time A/B GDS vs GD), 2 (origin of horde-ad
  savings beyond VTO).
- 5 DONE (no CPU, during re-timing): GHC tracker searched via REST API (curl; glab not installed here; notes need
  auth, discussions.json is public). HIT: #15606 "Don't float out lets in between lambdsa" (simonpj 2018-09-05,
  open, no comments, no MR, last update 2019): proposes exactly the spine rule ("not float out between two lambdas,
  even if separated by lets/cases"; same level number for \x.let..in \y and \x.case..of p -> \y), in every pass,
  motivated by non-confluence; "probably won't make a lot of difference, but it'd be worth trying". Related:
  #24466 (open: float-in into several case branches -- would undo step 4), #24655 (closed: float-out of lambdas
  can increase allocation), #19230 (cheapness W/W; relevant to the arity effect, item 4). Draft updated: header
  (suggests posting as a comment on #15606), body references #15606 and #24466.
  FOLLOW-UP: test #15606's exact proposal = spine rule in EVERY pass (drop `not (floatOverSat env)`) as
  ghc-spineall: build after the re-timing; reproducers + adversarial + nofib, to justify "first pass only".
- Item 4 reading (no CPU; fmaprepro/G2G/Lib.dump-stg-final): in the defining module EVERY copy of interp keeps the
  `\case` lambda unexpanded: interp Arity=3 = dNum,dKnownS,env; $sinterp (KnownS s =>, from SPECIALISE) Arity=2 =
  dKnownS,env. The guard `mkDict (sing @s)` is a NOINLINE call (not cheap) and the copies are exported (or kept
  alive by rules), so GHC may not eta-expand over the guard (a shared partial application would redo it).
  Self-reinforcing: with arity 2 the recursive call `$sinterp d env` (env-only prefix of `interp env a`) is a
  SATURATED call, i.e. work, so full laziness floats it as a thunk `lvl = $sinterp d env` above `\case`; per call:
  the \case closure + lvl thunk + f + fmap' + ... = 957 MB vs 198 argument form. Importer (GD Main.$sinterp, local,
  all calls saturated) gets Arity=3 with eta. So item 4 = classic "can't eta-expand an exported function over
  expensive work"; not a bug. Improvement idea ("saturation worker/wrapper"): for f = \xs -> case e of K -> \ys -> b
  with e not cheap, make $wf = \xs ys -> case e of K -> b (full arity) and have saturated calls use it: inside the
  module directly (recursive calls are saturated), outside via an auto RULE `f xs ys = $wf xs ys` (a RULE matches
  only applications with enough args), keeping f itself for partial applications; one body if b goes into a shared
  worker taking the case binders. Related: #19230 (cheapness W/W, sgraf), #18356, #20273. To test after the
  re-timing (no compiles during timed builds): manual version in fmaprepro (interp_sat + RULE) -> expect ~198 MB.
- #19230 (open, sgraf 2021, "Cheapness Worker/Wrapper to support eta expansion") IS the item-4 idea: go = \x -> let
  tmp = <not cheap> in \a -> $wgo x tmp a; recursive calls inline the wrapper so they call the full-arity $wgo;
  "kind of like arity worker/wrapper ... but for recursive call sites"; simonpj/sgraf discussion about LetUp DmdAnal
  vs Call Arity; not implemented. fmaprepro defining-module (957 vs 198 MB, 4.8x) is a concrete motivating example
  for it (exported specialisation, NOINLINE guard). Plan: manual W/W in Lib (wrapper + $winterp) to confirm ~198 MB,
  then maybe a comment on #19230 (needs Mikolaj's go-ahead; nothing posted).
- Item 3 reading: T10370 peak MB 62->64 and MultiLayerModulesDefsGhciReload 184->186 are noise: max_bytes_used
  unchanged (22975072 vs 22973936; 69335024 vs 69335000), so only block-granular peak moved. Real: T18698a bytes
  196222080 -> 199546280 (+1.69%), T18698b 176663848 -> 179097656 (+1.38%). T18698.hs = Semigroup instance for a
  21-field StrictData record, `f` local (Maybe a -> Maybe a -> Maybe a, via coerce under -DCOERCE), -O2.
  To do after timing: compile with ghc-guard vs ghc-spine, -dverbose-core2core sizes / -ddump-simpl-stats per pass.
- Mikolaj (~15:00): after the queue, for each ticket proposing our solution, read its worries, build small examples,
  test with our patch: does it kill the patch or make it a doubtful trade-off?
  * #24655 (closed 2024, simonpj): fixed by 55a9d69933 "Do not float HNFs out of lambdas" unless to top level
    (MFEs only; nofib -0.09%, cichelli +4.8% "allocate the pair every time around the inner loop"). Extending it to
    let-bound functions = our earlier funtop rule, which lost H2's saving -> already tested, recorded.
  * #15606's implicit worry = losing work sharing for a shared partial application. Earlier spine tests P1-P5 all
    had NON-cheap separators (check/expensive), which block eta-expansion so the late pass still splits. UNTESTED
    risk: cheap separator (case on a var, cheap guard) + expensive work in the inner lambda + shared PAP: guard
    floats the work in pass 1 and keeps arity 1 (sharing); spine doesn't, eta-expands to arity 2, recomputes per
    application (possibly asymptotic). Programs adv/t15606/W1-W9 (W1 cheap case PAP, W2 saturated, W3/W4 the
    ticket's own example with <blah> a call / Just x, W5/W6 the ticket's "new level" cases, W7 user let, W8 cheap
    guard PAP, W9 cheap case PAP with a local function). Queued: chain2.sh -> job-chain2.out after chain1
    (guard, spine, spineall, -O). If W1/W8 lose: refine the rule to block only value (HNF/function) floats out of
    spine lambdas, still floating work (redexes) -- floating a value saves only allocation, and only for a shared
    PAP; floating work can save unbounded work.
- GDSr (retime) 2624 s vs GDS 2436 s: 7.7% spread on identical builds.
- ~15:05-15:20 (overlapping the timed G2Sr build, small CPU, Mikolaj: "prioritize the small programs"):
  t15606 W1-W9 with guard/spine: W3 (#15606's own example, blah a call) guard 0.004 s vs spine 0.256 s (64x),
  W8 (cheap guard + shared PAP) guard 0.003 s vs spine 0.131 s (40x): spine loses work sharing. Others identical.
  => the spine rule as is is NOT an obvious choice. Refinement = ghc-spine2 (perf/SetLevels.hs.spine2, spine2.diff
  vs orig; built 59 s, buildSpine2.sh restores spine src+binary): spine lambdas get a major level again (work floats
  as before); a LET-BOUND VALUE (exprIsHNF rhs, not bottoming) can't float out of the nearest enclosing spine
  lambda (le_spine_lvl) in the first pass unless to top level (spineClamp in lvlBind). = #24655's 2024 HNF rule
  extended to let-bound values, but only for spine lambdas. Results: W3 0.004 s, W8 0.005 s (= guard), fmap1s
  320 MB (= arg form), W others same alloc. Running smallAll.sh "guard spine spine2" -> job-small1.out (all
  adversarial dirs + t15606 + Neg2 + fmap2m + fmapev + fmaprepro + fmap1s).
- smallAll "guard spine spine2" (job-small1.out): spine2 = guard on all 25 adversarial + t15606 + Neg2 (W3/W8
  sharing kept); fmap1s 320 (fixed); but fmap2m -O -fexpose 387 (spine 323, arg 323), -O 755 (403), fmaprepro
  importer 262 (198) = the same partial numbers as fibcse and funtop1. W11 (closure value + shared PAP, NOINLINE
  HOF) identical for all three: a floated value never blocks eta-expansion, so with a cheap separator it was
  allocated per call anyway, and with a non-cheap one the lambda survives and the late pass floats it -> blocking
  value floats in pass 1 cannot lose sharing (argument). W12 (con with expensive field) identical (GHC optimises).
- Residual of spine2 (fmaprepro, dumps in scratchpad/fr2): in Lib (-fspecialise-aggressively), pass 1 floats the
  recursive self-call `lvl = interp_$sinterp dNum env` (saturated at arity 2 before eta-expansion = "work") out of
  \ds; that let blocks eta-expansion in Lib; the late pass then floats fmap' (value) out of the surviving \ds; the
  exposed (optimised) unfolding carries it to Main, which specialises + eta-expands -> per-call fmap'.
- ghc-spine3 = spine2 + in pass 1, a call to the enclosing recursive group with fewer value args than the callee's
  spine arity (own lambdas + spine lambdas through let/case(min over non-dead-end alts)/cast/tick) counts as an HNF
  in lvlMFE (isSpinePap; le_rec_spine set in lvlTopBind Rec and lvlBind AnnRec). Argument: floating it can save at
  most the work before the callee's spine lambda; if cheap, eta-expansion makes it a PAP allocated per call; if
  not, the lambda survives and the late pass floats it. perf/SetLevels.hs.spine3, spine3.diff; buildVariant.sh.
  Running smallAll "guard spine spine2 spine3" -> job-small2.out.
- smallAll "guard spine spine2 spine3" (job-small2.out): spine3 = spine2 on EVERYTHING (residual 387/755/262
  unchanged). Cause (scratchpad/fr3, Lib first float-out): the escaping call is `f = interp $dNum (C:KnownS $WSP)
  env` inside Lib's specialisation $sinterp: not syntactically recursive at pass 1 (the specialisation's RULE
  rewrites interp -> $sinterp only in the simplifier AFTER the first float-out), so isSpinePap's Rec-group map
  never sees it. Widening to all calls breaks the safety argument (caller-side W8 analogue: a cheap-separator
  caller would be eta-expanded and lose sharing of a callee's expensive guard). Stopped there: spine3 dropped
  (kept in perf/ as a negative result). CONCLUSION on the worries: spine (as drafted) is a doubtful trade-off
  (W3 = #15606's own example 64x slower, W8 40x); spine2 is safe on all 36 small programs (+ argument) and fixes
  the single-module reproducer, partially the multi-module ones (same residue as funtop1/fibcse; funtop1 fully
  fixed horde-ad G2F, so spine2 probably does too: to measure).
- 15:25 queued chain3.sh -> job-chain3.out (after chain2): horde-ad G2S2 + GDS2 with ghc-spine2 (timed alone, alloc
  vs GD, dist deleted after), nofib Fast with ghc-spine2 (_make/spine2, nofib-guard-spine2.cmp), then testsuite +
  perf/compiler with spine2 source installed in /opt/ghcsrc (restores spine source + binary at the end).
  Running jobs: expRetime (G2Sr now), chainAfterRetime (waiting), chain2 (waiting), chain3 (waiting).
- Mikolaj agreed to rescope items 3/1/2 to spine2 (tasks 17-19):
  3: spine2's compile-time cost from chain3's perf-spine2.tsv (+ nofib); explain only what exceeds noise (peak MB
     counts only if max_bytes_used moves too).
  1: wall-time A/B dist-GDS2 (kept by chain3) vs dist-GD, on the benchmarks whose allocation moves, plus controls.
  2: origin of horde-ad allocation changes with spine2 (do spine's grad k list -10.5% etc. survive?).
  Order after chain3: 3, 1, 2 (then the draft rewrite around spine2 + #15606).
- 15:40 disk hit 1.4 GB free during G2Sr: deleted binaries/objects of small-* and adv/t15606/out, and dist-GDS (spine baseline; A/B now uses GDS2). 6 GB free.
- Mikolaj (~15:45): ONLY when out of agreed work: try improving spine2 in a non-ad-hoc, succinct way; read issue
  comments and papers for inspiration (e.g. #19230). The "tiny improvement" sentiment of #24655 note_557764
  (simonpj: "meanwhile !12410 is a tiny improvement") is fine for us, if it also matches horde-ad's use case and
  related cases (horde-ad evolves, so related cases must be covered). Task #20.
- G2Sr 2673 s (15:41) vs GDSr 2624 s: +1.9% (G2Sr overlapped ~2 min of -j4 GHC builds + ~5 min single-core small runs). First sample 2177 vs 2436 was an outlier: no compile-time saving of G2 source established.
- Task #20 candidate "coldalt" (perf/SetLevels.hs.coldalt, coldalt.diff vs HEAD, 72 lines; NO spine concept, all
  passes): (SW2) of Note [Saving work] (the #24655 fix's own rationale: floating an HNF out of a cold path
  allocates it always) extended from MFEs to LET-BOUND values, but only for real cold paths: a let-bound HNF does
  not float out of an alternative of a case with >= 2 non-dead-end alternatives unless to top (le_alt_lvl set in
  lvlCase, altClamp in lvlBind, reset in lvlFloatRhs when the RHS floats out). May still float out of lambdas
  inside the alternative (keeps H2/Neg2-style loop savings: no case crossed). Work still floats (W3/W8 safe).
  Single-alt cases (horde-ad's Refl/Dict evidence guards) are not cold paths. Applies to the late pass too, which
  may cover spine2's cross-module residual (Lib's LATE pass floated fmap' out of the \case alternatives).
  Queued chain4.sh -> job-chain4.out after chain3 (agreed work first): build ghc-coldalt + smallAll "guard spine2
  coldalt" -> job-small3.out. Not built yet (would disturb the timed G2Gr/GDr builds).
- RE-TIMING DONE (17:00). Two samples each (s): GD 2382 / 2530, G2G 2385 / 2226, GDS 2436 / 2624, G2S 2177 / 2673.
  Spread within a variant up to 23% (G2S); means GD 2456, G2G 2306, GDS 2530, G2S 2425. Nothing established:
  build-time differences between these variants are below this machine's noise (~10-20%), even timed "alone"
  (G2Sr overlapped ~7 min of my small runs/GHC builds; G2Gr/GDr had nothing of mine running).
- chain1: fmap1s ghc-guard -fno-cse = 320,051,688 (draft table cell confirmed). Item 4 (run4.sh, MB): \case form
  importer guard 394 / spine 198, defining-module 957 / 957; MANUAL ARITY W/W (wrapper interp env | Dict <- .. =
  \t -> winterp env t, INLINE; worker winterp INLINABLE + SPECIALISE) 192 in all four cells (guard/spine x
  imp/def), below the argument form (198). So #19230's arity worker/wrapper removes the defining-module 4.8x
  entirely, independently of the float-out rule.
- BUG: run4.sh prints its own "DONE", which released chain2 early (chain2 waits for ^DONE in job-chain1.out):
  chain2 ran t15606 with ghc-spineall before buildSpineall finished -> spineall column invalid, rerun by hand.
  chain3 (waits for chain2 DONE) may overlap the tail of buildSpineall (~1 min -j4) with its timed G2S2 build.
- chain1 end: ghc-spineall built (34 s); fmap1s spineall 320 / arg 320. chain2 (t15606 guard/spine/spineall; rows
  W1-W6, W11, W12 spineall BUILD-FAILED = built before the compiler existed): W8 spineall 0.131 s (loses sharing
  like spine), W7/W9 same. Spineall = spine's flaw; superseded; not rerun. chain3 started ~17:03 (G2S2 timed).
- G2S2 (G2 source, ghc-spine2) build 2178 s; alloc vs GD: prod 1.0000 [0.9997,1.0001] (G2G was 1.0021), MNIST 1.0000 [1.0000,1.0000] (G2G VTO +10.48%): spine2 FULLY fixes horde-ad's G2 residual. Spine's extra savings (grad k list -10.5% etc.) are gone with spine2 -> they came from blocking WORK floats.
- G2S2 conv 1.0000 [0.9984,1.0007]. All three suites = GD. GDS2 build next (timed).
- GDS2 (baseline source, ghc-spine2) build 2472 s; alloc vs GD: prod 1.0000 [0.9998,1.0003], MNIST 1.0000
  [1.0000,1.0000], conv 1.0000 [0.9991,1.0004]. spine2 leaves the baseline unchanged (as expected) -> item 1
  (wall-time A/B GDS2 vs GD) is moot: identical allocation everywhere.
- chain3 nofib BROKEN (my bug): deleting dep-packages/*.env-file before every benchmark while Shake's .stamp says
  done -> "Package environment ... not found" for all but the first. Fix: nofibOne.sh NAME (rm -rf _make/NAME once,
  no per-benchmark env-file deletion). Queued chain5.sh -> job-chain5.out: after chain4, nofib spine2 then coldalt.
  (chain5 waits for ^DONE in job-chain4.out, which buildVariant.sh also prints -> it may start during chain4's
  small runs; both untimed, allocation unaffected.) chain3 now running testsuite + perf with spine2.
- TESTSUITE with spine2 (19:19): 11802 expected passes (= 11777 + the 25 optllvm now that LLVM is installed), 0 unexpected failures, 0 unexpected stat failures. perf/compiler running.
- perf/compiler spine2 vs guard: 147 metrics geomean +0.045% (spine was +0.058%); T18698a/b no longer move (their
  +1.7/+1.4% came from spine's blocking of work floats); largest bytes-allocated: T9961 +0.21%, WWRec +0.15%,
  T15164 +0.12%; peak MB T10370 +3.2%, MultiLayerModulesDefsGhciReload +1.1% (same as spine's run: check
  max_bytes_used). 0 stat failures. Item 3 (spine2's compile-time cost): nothing beyond noise.
- 19:3x RESULTS (task #20 exploration, agreed queue done except draft rewrite which now waits for the design):
  * nofib spine2 (fixed runner nofibOne.sh; ~5 min per compiler in Fast mode): 114 benchmarks geomean 1.0000
    [1.0000,1.0001]; ansi's -33% (spine) gone -> came from blocking work floats. 4 failed = secretary,
    ben-raytrace, smallpt, gc_bench (need random/old-time dep packages; same for every compiler).
  * coldalt small runs (job-small3.out): reproducers fixed further (fmaprepro importer 198 = arg, fmap2m -O -fexpose
    323 = arg, -O 707, defining 886) BUT L5_const_loop 12.9 MB/0.005 s -> 3.2 GB/0.68 s (the value `go` pinned in
    the `otherwise` branch of a loop, so the loop-invariant WORK `go 1000` can't float either), D_looprec +33%,
    I_onebranch +6.6%, P3 +5%. KILLED. nofib coldalt geomean 1.0001, max +0.51% (constraints).
  * Same lesson kills spine2: W13 (cheap guard + local go + constant call `go 1000` + shared PAP): guard 0.005 s,
    spine 0.277, spine2 0.260 s (52x), coldalt 0.005. Pinning a value pins the work that depends on it, and that
    work float was what blocked eta-expansion and kept the sharing. My "values can't lose sharing" argument was
    WRONG. => every float-out restriction tried (spine, spine2, coldalt) has an unbounded loss somewhere.
  * New direction: leave float-out alone; fix step 4 (float-in can't sink a binding used in several alternatives).
    FloatIn already duplicates into several alternatives if exprIsDupable (tiny exprs only). ghc-dupvalue
    (perf/FloatIn.hs.dupvalue, dupvalue.diff 34 lines, SetLevels = HEAD): also duplicate a let-bound HNF that is
    couldBeSmallEnoughToInline (default threshold) into the (not all) alternatives using it. No work duplicated
    (one alternative runs), no path allocates more; float-out untouched so no sharing can be lost.
    Results: ALL 38 adversarial/worry programs = guard (W3, W8, W13, L5 included); fmap1s 320 (=arg), fmaprepro
    importer 198 (=arg), fmap2m -O -fexpose 323 (=arg); NOT fixed: fmap2m -O 755 (arg 403), fmapev 838 (arg 707),
    defining-module 957 (arity effect, separate). nofib dupvalue geomean 1.0000 [0.9990, 1.0001].
  * #24466 discussion shows "[sys] 2026-10-01 marked this issue as related to #15606" (today; not by me: I only
    read). #24466 = SPJ's "Improve FloatIn for case expressions" (thunks into branches; worry: join points can
    lose sharing for thunks -- not for values). sgraf there points to #20378 / !6541 (hot-path-aware floating).
- dupvalue's misses explained: fmap2m -O (755 vs arg 403): Main's copy is fine (go inside its alternative); the
  extra is in Lib's exported interp_$sinterp (Arity=2, not eta-expanded): a floated self-call thunk
  `lvl2 = interp_$sinterp $dNum env` blocks eta-expansion (circular: with arity 3 it would be a cheap PAP) ->
  the ARITY EFFECT (item 4, #19230; manual W/W gave 192). So dupvalue covers the whole float/CSE class; the
  rest is #19230's. (fmapev presumably the same; not dumped.)
- 19:38 launched chain6.sh -> job-chain6.out: horde-ad G2DV (G2 source) + GDDV (baseline) with ghc-dupvalue, timed,
  alloc vs GD (dist-G2DV deleted after, dist-GDDV kept); then GHC testsuite + perf with dupvalue (FloatIn
  dupvalue + SetLevels HEAD installed in /opt/ghcsrc, restored after). dist-GDS2 deleted (moot A/B).
- G2DV (G2 source, ghc-dupvalue) build 2211 s. t15606 W1-W16 (W15 value depending on loop var in 2 of 3 alts, W16 loop-invariant value bound outside a tail-recursive loop, used in 2 of 3 alts): dupvalue = guard on all 15 (alloc identical); spine2 loses W13 (0.262 vs 0.004 s).
- G2DV alloc vs GD: prod 1.0000 [0.9997,1.0001], MNIST 1.0000 [1.0000,1.0000] -> dupvalue FULLY fixes horde-ad's G2 residual (VTO +10.48% gone), like spine2, without touching float-out.
- DRAFT REWRITTEN (~20:45) around dupvalue (old spine version saved as variants/draft-spine-version.md): mechanism
  unchanged; fix = FloatIn duplicates small values into the alternatives using them (narrow case of #24466,
  suggests posting there); "Alternatives considered" = #15606's float-out rule loses sharing (W3 = #15606's own
  example 60x, values-only W13 60x, SW2-for-lets L5 3.2 GB vs 13 MB); Related = arity effect/#19230 (manual W/W
  957 -> 192) and horde-ad (G2DV = GD on 158 benchmarks). Pending (stated in header): testsuite + perf with
  dupvalue (chain6), GDDV, fmapev analysis. doc-refs (--without-siblings) and citations checkers clean.
- ~20:55 CONTAINER RESTART killed chain6 during the GDDV build (G2DV results complete). Source tree intact (SetLevels spine-src, FloatIn orig, ghc = spine). Relaunched as chain6b.sh -> job-chain6b.out (21:00): GDDV fresh build timed + alloc, then testsuite + perf with dupvalue.
- G2DV conv 1.0000 [0.9990,1.0004]. GDDV (baseline, dupvalue) build 2324 s; alloc vs GD prod 1.0000 [0.9997,1.0003],
  MNIST 1.0000 [1.0000,1.0000] (conv, testsuite, perf pending in chain6b).
- fmapev ANSWER (Mikolaj asked): traced with ghc-dvdbg2 (pprTrace in sepBindsByDropPoint): the merged `go` (used in
  3 of 6 alts, HNF) fails the size test: sizeExpr = 110 > unfoldingUseThreshold 90 (the extra `ev @Int $fNumInt env
  x` call); fmaprepro's go calls a local var and is < 90. The inline-at-call-site threshold is the wrong yardstick
  (unbounded copies + argument discounts there; here at most n-1 copies). Proposed: budget (n_used_alts - 1) * size
  <= unfoldingCreationThreshold (750), or per-binding creation threshold. Awaiting Mikolaj's pick.
- Mikolaj: add worst cases around the size threshold (just under/over; some small floats dup'd "start well", a big
  one stays so we pay without the reward). adv/size/gen5.py + sizerun.sh (alloc, Main.o .text, compile s):
  S1 cliff (go in 3 of 6 alts, 0..12 extra NOINLINE calls), S2 small+big independent, S3 big captures small,
  S4 small in 20 of 21 alts, S5 ten values each in 9 of 10. guard vs dupvalue (MB alloc, text bytes):
  S1_00 582->320 (+14% text); S1_01..12 unchanged (sizes 130..691 > limit; basic go = 100 [size 100, discount 10],
  passes only via the discount); S2 2378->2246 (-5.5%) for +11% text (big 691 stays: pays w/o full reward);
  S3 identical; S4 582->320 for +56% text; S5 3331->3005 (-10%) for +10% text (only one of ten go's, size 100,
  dup'd; nine are 120).
  Variants written (build after chain6b, which swaps the same files): dupbudget ((n-1)*size <= creation threshold
  750; predicted: S1 up to ~375 fixed, S4/S5 refused) and dupcreate (per-binding size <= 750; all dup'd).
- TESTSUITE with dupvalue (chain6b): 11800 expected passes, 2 unexpected failures, both Core-shape greps:
  T18903 (dmdanal: NOINLINE local worker $wg duplicated into 2 alts) and T26709 (simplCore: NOINLINE join point j
  duplicated into the B and C alts). Fix applied to the dupvalue/dupbudget/dupcreate SOURCES before chain7 builds
  them: dup_ok b = not join point (not allocated: nothing saved) && not NOINLINE (programmer wants one copy).
  isNoInlinePragma is in GHC.Types.InlinePragma in this HEAD. ghc-dupvalue BINARY predates the fix.
- Mikolaj (~22:00): try budget AND dupcreate; rewrite the draft as a COMMENT for #24466, biggest value = the
  worst-case collection + analysis of a few obvious solutions (design space); then COMMIT AND PUSH (go-ahead given)
  after the rewrite and the dupbudget/dupcreate results. Branch fast-forwarded to origin (20278efb).
- perf/compiler dupvalue vs guard: 105 bytes-allocated metrics geomean +0.039%; T15630 +4.23% (code duplication's downstream cost; to check under dupbudget/dupcreate); 0 stat failures. chain6b DONE ~22:45; chain7 started.
- chain7 (22:24-22:33): dupbudget/dupcreate built with dup_ok (join points, NOINLINE excluded).
  Size worst cases (MB alloc / Main.o text bytes): guard | dupvalue(inline thr.) | dupbudget | dupcreate
  S1+0 (size 100) 582/4687 | 320/5359 | 320/5359 | 320/5359; S1+1 (130) 646/4719 | = guard | 384/5455 | 384/5455;
  S1+4 (283) 1030/4983 | = | 768/6247 | 768/6247; S1+6 1286/5159 | = | = guard | 1024/6775; S1+12 (691) 2054/5687 |
  = | = | 1792/8359; S2 2378/6631 | 2246/7375 | 2246/7375 | 1984/10207; S3 all 2875/6327; S4 582/12127 |
  320/18919 | 582/12127 (refused) | 320/18919; S5 3331/28759 | 3005/31639 | 3331/28759 (refused) | 1824/64479.
  smallAll: all 41 programs = guard for both; reproducers: fmap1s 320, fmaprepro imp 198, fmap2m -fexpose 323,
  fmapev 707 (= arg; FIXED by both), fmap2m -O 755 (arity effect), defining 957. nofib: dupbudget geomean 1.0000
  [0.9988, 1.0000], dupcreate 1.0000 [0.9999, 1.0000].
- Disk: deleted dist-GDDV and all .o/.hi/ELF binaries under variants (4.0 -> 0.8 GB); 6.9 GB free.
- chain8.sh -> job-chain8.out (after chain7): tsFI.sh dupbudget, tsFI.sh dupcreate (testsuite+perf), hbG2.sh
  dupbudget 2, hbG2.sh dupcreate 2, hbG2.sh dupcreate D (horde-ad, timed, alloc vs GD, dist deleted after).
- 23:0x COMMITTED + PUSHED 9fa71f92 on drop-recursive-inline (fast-forwarded first to 20278efb): docs/ghc-issue-
  floatin-duplicate-values-comment.md (comment for #24466; not posted): the case, design-space table (#15606 rule
  first pass / every pass / values only, SW2-for-lets, CSE no-merge, float-in before CSE, float-in duplication,
  arity W/W) with worst losses, size-policy table S1-S5 x guard/inline/budget/creation, nofib, horde-ad, budget
  diff + program collection in <details>. Old issue draft deleted (backups variants/draft-*-version.md) and its
  .git/info/exclude line removed. Header states pending: testsuite/perf with budget/creation, horde-ad with them.
- 23:3x pushed c39e657e: worst cases added to the #24466 comment draft (argument-form column; S1 793/895, S3 773, S6/S7 user-single-copy; 10 programs verbatim). S6/S7 arg form not measured.
- TESTSUITE dupbudget (with dup_ok): 11802 expected passes, 0 unexpected failures (T18903/T26709 pass now), 0 stat failures.
- Mikolaj: amend instead -> squashed c39e657e into the first commit: 994fac06, force-pushed with lease on c39e657e.
- perf/compiler dupbudget vs guard: 105 metrics geomean 1.00000 (T15630's +4.2% under dupvalue came from
  duplicating join points; gone with dup_ok). Testsuite dupbudget clean (11802, 0 unexpected).
- Mikolaj: "measure enough that your table in the comment draft is full". variants/fill/: ReproWW (hand-written
  arity W/W of the case) guard 291 MB (arg 320); S6/S7 arg forms 1958 MB (text 11183 / 7327) -- worse than guard's
  \case 1798 (user's let above `case t` allocated per call). fibcse and cselam (binaries from 07:4x) on the size
  family: = argument form EVERYWHERE incl. S1 793/895 and S3 (no cliff, code = source's); S6/S7 1958 (+9% vs guard);
  smallAll: fibcse = guard on all 41; cselam P3 64 -> 88 MB (+37%), the only diff; reproducers: case 320 both;
  fmaprepro importer fibcse 262 / cselam 198, defining fibcse 957 / cselam 1264; fmap2m -fexpose 387 / 323,
  -O 755 / 851; fmapev 707 both.
- Tables filled (fibcse/cselam columns + rows, W/W 291, S6/S7 arg 1958); amended + force-pushed (lease 994fac06) as dad5f949.

## STATE AT FIFTH COMPACTION (2026-10-01 ~23:20 UTC)
- Direction changed: float-out rules (spine = #15606 rule 1st pass, spineall, spine2 values-only, coldalt = SW2 for
  lets) ALL lose unboundedly (W3 60x, W8 35x, W13 60x, L5 250x alloc). Fix candidates are at float-in:
  FloatIn duplication of small values into the alternatives using them (narrow case of #24466), policies:
  dupvalue (inline threshold; superseded), dupbudget ((n-1)*size <= 750), dupcreate (size <= 750); both latter with
  dup_ok (no join points, no NOINLINE). Sources: variants/perf/FloatIn.hs.{orig,dupvalue,dupbudget,dupcreate},
  dupbudget.udiff; build: variants/buildFI.sh NAME (restores spine SetLevels + orig FloatIn + ghc-spine binary).
  Also measured as alternatives: ghc-fibcse (float-in before CSE), ghc-cselam (CSE skips lambdas): no size cliff,
  = argument form on the whole size family, but S6/S7 +9%, fibcse half-fixes cross-module, cselam P3 +37%.
- COMMITTED+PUSHED (amend + force-with-lease each time, per Mikolaj "amend instead"): dad5f949 on
  drop-recursive-inline = docs/ghc-issue-floatin-duplicate-values-comment.md (comment for #24466, not posted):
  case, design-space table (8 fixes, worst loss each, all cells measured), size table (S1..S7 x guard/inline/
  budget/creation/fibcse/cselam/argument form, all measured), nofib, horde-ad, budget diff, program collection
  (W3, W8, W13, L5, size family, D, I, P3 verbatim). Header says: budget testsuite clean + perf unchanged;
  still running: creation-threshold testsuite/perf and horde-ad with both.
- Results so far: dupbudget testsuite 11802/0 unexpected; perf/compiler 105 metrics unchanged. nofib: dupbudget,
  dupcreate geomean 1.0000. horde-ad with dupvalue: G2DV = GD on 158 benchmarks; GDDV = GD.
- IN FLIGHT: variants/chain8.sh -> job-chain8.out: tsFI.sh dupcreate (testsuite+perf), then hbG2.sh dupbudget 2,
  hbG2.sh dupcreate 2, hbG2.sh dupcreate D (horde-ad G2/baseline, timed, alloc vs GD into alloc/<T>-*.cmp).
- NEXT: when chain8 lands: update the comment header (creation-threshold testsuite/perf; horde-ad with both
  policies: G2 source should = GD), re-read, amend + force-with-lease push; check CI on the new head.
- Open/optional: commit the program collection (variants/adv/{.,const,heavy,spine,t15606,size}) into the repo if
  Mikolaj wants; the #24466 comment and posting are Mikolaj's call. Item 4 (arity effect, #19230) documented in
  the comment; task #16 can be closed. Disk ~7 GB free; variants binaries deleted.
- 23:45: dupcreate testsuite 11802/0 unexpected; perf/compiler 115 passes, 105 bytes-allocated metrics within
  +-0.015% of unpatched/guard/dupbudget. chain8 now on hbG2.sh dupbudget 2 (timed; keep CPU idle).
- 2026-10-02 ~00:20. Mikolaj: program collection will NOT be committed; keep breaking the fixes, improvements welcome.
  NESTED FAMILY variants/adv/nest (gen6.py, nestrun.sh): one shared g in an alt, used at every leaf of a depth-d
  tree of 3-way cases (2 alts use g; a case where ALL alts use g never pushes). Per-level checks compound:
  N_s12_d8 text 71k (guard) -> 426k (dupbudget = dupcreate, 6x), ct 2.0 -> 3.5 s; alloc 160 -> 96 MB.
  FIX dupshare (variants/perf/FloatIn.hs.dupshare, dupshare-vs-dupbudget.udiff): FB carries an Int budget
  (starts at unfoldingCreationThreshold); pushing into n alts spends (n-1)*size, each copy gets
  (budget - spent) div n. Total extra code per binding per pass <= 750. N_s12_d8 text 75k, ct 2.2.
  dupshare = dupbudget exactly on size family S1..S7 and all 41 small programs + fmap*/fmaprepro.
  Bounded loss found: N_s12_d2 dupshare 736 MB vs guard 704 (+4.5%): g copied into 2 top alts but budget stops
  short of leaves, so each copy has 2 uses (two go loops), isn't inlined, costs an extra closure per call
  (guard: CSE merged the go loops and g inlined into the single go). Any budget stopping halfway can do this.
  chain9.sh -> job-chain9.out (waits for chain8 DONE): tsFI dupshare, hbG2 dupshare 2.
- 00:50 chain8: 2dupbudget alloc = GD on all 158 (prod 0.9998, MNIST 1.0000, conv 1.0000 [0.9992,1.0006]);
  2dupcreate build 1949 s (2dupbudget 2006 s). M FAMILY (adv/nest/gen7.py, mrun.sh): top 3-way case (2 use g),
  nested case 3-of-4 or 2-of-3. MB: M_s04_3of4 guard 464 / dupbudget 432 / dupcreate 432 / dupshare 523 (+13%);
  M_s12_2of3 704 / 661 / 661 / 736 (+4.5%); M_s12_3of4 976 / 1035 (+6%) / 944 / 1035 (+6%).
  => the draft's "allocation can only go down" is FALSE for any policy that stops partway. Mechanism: at late
  float-in g's only use is the CSE-merged go float (simplifier would inline g into it next); dup of go adds uses
  of g; budget stops g's dup above the leaves; copies keep 2+ uses, not inlined -> extra closure per call.
  Bounded: <= one closure per dup'd binding per call. Occurrence-count budget ((occ-1)*size) does NOT fix it
  (consumer floats' later dup increases occ at nested level). dupcreate: size-only test, same answer at every
  level, no partway loss found. No dominant policy: budget (compounds + partway), creation (compounds 6x, S6 2.3x),
  shared (no compounding, more partway).
- 01:15 PASS-ORDER FIX. -dverbose-core2core (adv/nest/core/v): after late CSE, $wg is used ONCE, by the merged go
  (+ `go = go` aliases); no simplifier runs between CSE and float-in, so float-in dups go and g separately.
  perf/Pipeline.hs.postcse adds `runWhen cse (simplify "post-late-cse")` before the late CoreDoFloatInwards.
  buildPL.sh FI NAME builds FloatIn.FI + postcse: guardsimp (orig), budgetsimp (dupbudget), sharesimp (dupshare).
  guardsimp = guard on M, N, S. budgetsimp: fixes M partway loss (M_s12_3of4 955) but N still 426k.
  SHARESIMP: never above guard on M and N (M_s04_3of4 443 vs 464; N_s12_d8 139 MB, 74k text vs 71k);
  = dupbudget on size family and on all 51 small-program measurements. Candidate now = sharesimp.
  chain9 killed while waiting (never ran). chain10.sh -> job-chain10.out: tsPL dupshare sharesimp (testsuite +
  perf), tsPL orig guardsimp perf (cost of the extra simplifier alone), hbG2 sharesimp 2, hbG2 sharesimp D.
- 01:55 chain8: 2dupcreate alloc = GD (prod 0.9998, MNIST 1.0000, conv 0.9999 [0.9970,1.0006]); Ddupcreate build
  2219 s; Ddupcreate prod 0.9998. Build times of all dup builds (1949-2219 s) are within the spread of earlier
  guard/GD builds (2141-2530 s): no compile-time cost visible, no speedup claimable.
  chain11.sh -> job-chain11.out (waits chain10 DONE): nofibOne sharesimp; hbTests.sh sharesimp (minimalTest +
  CAFlessTest of unmodified tree with ghc-sharesimp vs dist-GD binaries; compares failing sets; hbt/).
  Deleted variants/small-dupbudget-dupshare and small-sharesimp (results kept in small-dupshare.out,
  small-sharesimp.out).
- 02:02 AMENDED + PUSHED 66675690 (force-with-lease over dad5f949): header (testsuite 11802/0 + perf <=0.015% for
  budget AND creation), fixes-table FloatIn row (partway loss up to 13%, 6x code nested), corrected "allocation
  can only go down", new "### Nested cases" (N, M table: guard/budget/creation/shared/shared+simp; sizes of g =
  unfolding sizes 253 and 661, read off Guidance of top-level copies, adv/nest/core/gsz), "### nofib and
  horde-ad" (G2 with DV/budget/create = GD, extremes 0.9970/1.0006; D with DV/create extremes 0.9982/1.0004;
  build times 1949-2324 dup vs 2226-2530 guard), shared-budget + pass described under the budget diff, N and M
  programs. Header says still running: testsuite/perf, nofib, horde-ad for sharesimp. CI on 66675690 queued.
  NEXT after chain10/11: header with sharesimp results; maybe replace the budget diff by the sharesimp diff.
- 02:45 CI green on 66675690 (both workflows). chain10: sharesimp testsuite 11800 pass, 2 unexpected: inline-check
  (one more "Considering inlining" block = the extra pass) and rule2 (SimplifierDone 8 -> 9): expected-output
  changes from the pass, not bugs. PERF (vs perf-unpatched.tsv; no git-notes baselines here, so the perf suite
  can't fail): guardsimp = sharesimp: compile bytes allocated geomean +0.92%, 40/101 above +1%, max +4.9% (T9961).
  The extra pass costs ~1%. Cheaper idea: Pipeline.hs.latefi = late float-in moved AFTER simplify "final"
  (no extra pass; but float-in output then gets no simplifier at -O). buildPL.sh FI NAME [PL] now takes the
  pipeline variant. Build sharelate (dupshare+latefi) + guardlate (orig+latefi) in an untimed window; run M/N/S/
  small; then perf.
- 03:20 2sharesimp build 2036 s. LATE FLOAT-IN (Pipeline.hs.latefi: late CoreDoFloatInwards moved after simplify
  "final"; no extra pass): sharelate = sharesimp byte-identical (alloc AND text) on all M, N, S programs;
  sharelate = dupbudget on all small programs + fmap*/fmaprepro; guardlate = guard everywhere (fmaprepro GD 393
  is guard's own number, job-small1..3). => sharelate is the candidate if its testsuite/perf are clean (should
  cost no compile time). tsPL.sh takes PLV=latefi. chain12.sh -> job-chain12.out (waits chain11 DONE):
  PLV=latefi tsPL dupshare sharelate; nofibOne sharelate; hbG2 sharelate 2.
- 04:35 chain10 DONE: 2sharesimp alloc = GD (prod 0.9998 [0.9984,1.0000], MNIST 1.0000 [1.0000,1.0001], conv 1.0000
  [0.9984,1.0005]); Dsharesimp build 2326 s, alloc = GD (prod 0.9998, MNIST 1.0000, conv 0.9999 [0.9982,1.0005]).
  chain11: nofib sharesimp 108 ok (4 need packages), geomean 1.0001, spectral/mate +0.68%, k-nucleotide -0.11%.
  hbTests sharesimp running. Deleted variants/small-guardlate-sharelate (results in small-late.out).
- 05:03 chain11 DONE: hbTests sharesimp: minimalTest 3/75 and CAFlessTest 4/672 fail, SAME failing sets as GD
  (guard). chain12 (sharelate testsuite+perf, nofib, horde-ad G2) starts now.
- 05:30 SHARELATE REJECTED: testsuite 11800, 2 unexpected = REAL regressions: T14152 (exitification test: "dead
  code" stays in -ddump-simpl; float-in sinking `thunk` needs a simplifier AFTER it for case-of-known-con) and
  T22241 (demand sig g <ML> -> <L>, demand analysis sees unsimplified float-in output). Killed chain12 script
  (nofib/hbG2 sharelate pointless); its tsPL perf step left running to finish + restore the tree.
  Next: Pipeline.hs.postcse1 = extra simplifier with ONE iteration (simpl_phase FinalPhase "post-late-cse" 1):
  build sharesimp1 / guardsimp1 after tsPL restores; M/N/S/small; then testsuite + perf (cost vs ~0.92%).
- 06:10 sharesimp1 (dupshare + Pipeline.hs.postcse1, one-iteration simplifier after late CSE): = sharesimp
  byte-identical on M, N, S; = dupbudget on all 51 small-program measurements. chain13.sh -> job-chain13.out:
  PLV=postcse1 tsPL dupshare sharesimp1 (testsuite + perf), nofibOne sharesimp1, hbG2 sharesimp1 2.
- 06:55 sharesimp1: testsuite 11800, same 2 expected-output failures as sharesimp (inline-check; rule2 9 vs 8
  SimplifierDone). perf: compile bytes allocated geomean +0.59% (sharesimp +0.92%), 25/101 above +1% (40),
  max +4.9% T9961 unchanged (first iteration dominates). sharelate perf geomean 1.0000 [0.9992,1.0016] but
  rejected (T14152, T22241). FloatIn-local alternative (a value used only by one other float travels with it)
  needs occurrence counts FloatIn lacks; ad hoc vs the obvious simplifier pass -> present the trade-off in the
  draft. chain13 continues: nofib sharesimp1, hbG2 sharesimp1 2. Then amend the draft (header + nested section
  cost paragraph + testsuite/nofib/horde-ad for the pass variants) and push.
- (timestamps of the two previous entries were off: written ~05:58-06:03.) 06:03 nofib sharesimp1 = sharesimp
  (geomean 1.0001, mate +0.68%). Draft edited (not committed yet): header points to Nested cases; fixes-table
  row adds 0.6-0.9% compile cost; nested section adds pass cost (+0.92%, +0.59% one iteration, max 4.9%
  T9961; rule2/inline-check) and the rejected late-float-in alternative (T14152, T22241); nofib/horde-ad
  paragraph adds sharesimp nofib, horde-ad both builds [0.9982,1.0005], same failing tests; build times
  1949-2326. Commit message draft /tmp/claude-0/msg2.txt. Waiting for hbG2 sharesimp1 2, then amend + push.
- AMENDED + PUSHED ef89e7c1 (force-with-lease over 66675690): pass cost, late-float-in rejection, sharesimp
  nofib/horde-ad/tests in the draft; "With or without the pass"; ``div`` code span fixed. CI to check.
  hbG2 sharesimp1 2 still running (chain13); draft doesn't depend on it.
- 06:55 chain13 DONE: 2sharesimp1 build 2104 s, alloc = GD (prod 0.9998 [0.9984,1.0000], MNIST 1.0000
  [1.0000,1.0001], conv 1.0000 [0.9983,1.0001]). CI green (both workflows) on ef89e7c1.
  STATE: draft pushed ef89e7c1 is complete w.r.t. all measurements; nothing running. Candidate design for the
  GHC side: FloatIn dupshare (shared budget, join points + NOINLINE excluded) + one-iteration simplifier after
  late CSE (+0.59% compile alloc geomean, max 4.9% T9961); rejected: late float-in after "final" (T14152,
  T22241). Variants: perf/FloatIn.hs.dupshare, perf/Pipeline.hs.{postcse,postcse1,latefi}, buildPL.sh, tsPL.sh.
- Mikolaj: "yes" to replacing the prototype diff; asked whether patched HEAD + patches are mentioned. They were
  only in the HEADER (not posted) and the body used "guard" undefined -> moved into the body intro: HEAD
  9f48a5b908 (10.1.20260925) + fixes proposed in #27873, #27880 (Specialise) and #27874 (Core.Utils) = guard;
  perf/compiler + nofib relative to guard (recomputed vs perf-guard.tsv: identical figures; unpatched = guard
  within 0.015%). Testsuite results and horde-ad tree (-fno-worker-wrapper-cbv in AstInterpret, inspection-
  testing disabled; tree commit c05d3745 not on master, so no hash) moved into "### Testsuite, nofib and
  horde-ad". Prototype details now = shared budget + one-iteration pass diff (FloatIn.hs.dupshare with comment
  fixes only vs measured FloatIn.hs.dupshare.measured; Pipeline.hs.postcse1). Pushed 2cab4e66.
- Mikolaj: "does shared-budget speed up any examples from the related issues? If so, table; if not, investigate
  each. After that, repeat the main measurements on pure HEAD and report in the draft."
  RELATED (variants/adv/related, R1..R10, run.sh): #24466 f (R1), foo1 (R2), foo2 (R3); #2988 cascade (R4), hot-C
  with a function (R5) / thunk (R6); #24655 loop (R7), lvl (R8, my construction); #19230 e5'1 (R9); #15606 W3 (R10).
  sharesimp1 = guard on ALL (alloc). Why: R1 y is a THUNK (values only); R2/R3 x strict (all paths use it) ->
  no thunk; R4 all alternatives use the cascade; R5 x inlined into both branches + fused (no closure); R6 thunk
  already postInlineUnconditionally'd; R7 HEAD already puts (x,x) in the loop's exit join point (#24655 fix);
  R8 fused away; R9 arity, float-in irrelevant; R10 float-out work sharing.
  FIX: perf/FloatIn.hs.sharethunk = dupshare without exprIsHNF (thunks too; one alternative runs, binding not in
  scrutinee/outside -> no work dup). sharethunk1 (+postcse1): R1 472 -> 280 MB, MUT median of 7: 0.072 -> 0.055 s
  (guard), 0.067 -> 0.051 (pure HEAD); = sharesimp1 on M/N/S (30 rows) and all 51 small-program measurements.
  PURE HEAD (buildHead.sh FI PL NAME; perf/{Specialise,Utils}.hs.{head,guard}, guard-fixes.patch): headpure,
  headshare1, headthunk1: = guard / = guard-based variants on S, M, N, R, all 51 small (fixes don't matter here).
  chain14.sh -> job-chain14.out: tsPL sharethunk1 (ts+perf), nofib sharethunk1, hbG2 sharethunk1 2, hbTests
  sharethunk1; tsHead headpure perf; tsHead headthunk1 (ts+perf); nofib headpure, headthunk1 (+ cmp); hbG2
  headpure D, headpure 2, headthunk1 2 (compare 2* vs Dheadpure afterwards with alloc-cmp.py).
- ~09:40 sharethunk1: testsuite = sharesimp1 (same 2 expected-output diffs, identical), perf = sharesimp1 (all
  metrics within 0.01%; geomean +0.59% vs guard). Prototype renamed helpers (floatCopySize, copySize,
  small_enough) + Note text for thunks; compile-checked (sharethunkR, R1 280 MB) and deleted. Measured file kept
  as FloatIn.hs.sharethunk.measured / .prerename. PUSHED 035c1d59: related-tickets section (table R1..R10),
  prototype diff = sharethunk + postcse1, "restricted at first to values", header lists what is still running
  (nofib + horde-ad for thunks; pure-HEAD measurements). chain14 continues (nofib sharethunk1 now).
- ~10:30 Mikolaj: check small relaxations of the thunk variant reusing existing mechanisms (no special cases;
  separate fixes rather than bloat). Then: "rework the draft comment to be a comment for !12121 and make it as
  helpful as possible; commit every time you gather significant new data/ideas, but don't push until I tell
  you"; "make the reframe of the draft a new commit and then amend it".
  FOUND: !12121 "Try improving FloatIn" (simonpj, wip/T24466, opened 2024-02-22, updated 2026-08-10, open),
  linked from #24466 discussion (web JSON: gitlab.haskell.org/ghc/ghc/-/issues/24466/discussions.json; API notes
  need auth). Also sgraf: #20378 (static branch frequency). MR: FloatIn pushes thunks too (not strict thunks),
  pushes even when used in ALL alternatives, size test sizeExpr <= unfoldingUseThreshold (no discounts) per copy,
  occurrence analysis first (OneOcc lets into non-case forks, join points), floatIsDupable for FloatCase by size;
  postInlineUnconditionally: drops "inline small things to avoid thunk"; Pipeline: float-in after -O2 CSE.
  Rebased on HEAD: 2 hunks by hand (floatIsDupable keeps FloatTick panic; SimplUtils where-block).
  perf/{FloatIn,Pipeline,SimplUtils}.hs.mr12121, SimplUtils.hs.orig; buildMR.sh (guard base -> ghc-mr12121),
  buildHeadMR.sh NAME OUT (pure HEAD -> ghc-headmr). Relaxation: FloatIn.hs.sharethunkall = sharethunk minus
  the "used in all alternatives" guard (headthunkall1, sharethunkall1).
  RESULTS (pure HEAD, alloc): R11 (#24466 strict-use remark): 773 -> 560 MB with headthunk1 AND headmr (CBV via
  final simplifier). R12 (foo1 + unused branch): HEAD already optimal (x computed in j and C separately). R13
  (MR's own comment example x = Just y nested): HEAD already makes x a nullary JOIN POINT -> no change anywhere.
  headmr on S family, M, N = headpure (MISSES THE CASE: S1 size 100 fails its no-discount size test); fmap1s 582
  (not fixed); fmap2m -fexpose 323 (fixed), -O 755 (partial), fmapev 838 (not); fmaprepro GD 330 (HEAD 393, arg
  198); R1/R11 fixed. headmr and headthunkall1 both: H4 813 -> 650 MB (-20%), L4 11.9 -> 11.0 MB (indirect:
  pushing into all alternatives changes loop/exit structure, `lvl4 = $wgo 102#` floats out; Core 237 -> 307
  terms); headthunkall1 else = headthunk1 (+16..80 bytes static on ~18 programs).
  chain14 killed after hbTests started (hbTests sharethunk1 still running, output into job-chain14.out).
  chain15.sh -> job-chain15.out: waits hbTests; tsHead headpure perf; tsHead headthunk1, headthunkall1,
  headmr (SUV=mr12121) ts+perf; nofib x4 (+ cmp vs headpure); hbG2 mr12121 2; hbG2 sharethunkall1 2.
- ~11:20 COMMITTED LOCALLY (not pushed, per Mikolaj) 8528cf1c "Rework the GHC #24466 comment draft into a comment
  for GHC !12121" on top of pushed 035c1d59. From now on: AMEND 8528cf1c with new data; no push until told.
  Medians (pure HEAD, 7 runs): R1 472/0.067 -> MR 280/0.050, proto 280/0.052; R11 773/0.116 -> 560/0.095 (MR),
  560/0.090 (proto); H4 813MB/0.176s/2066 text -> MR 650/0.143/2330, thunkall 650/0.137/2786; L4 11.9 -> 11.0.
  Cross-module (MB): fmap1s HEAD 582 MR 582 proto 320 arg 320; fmap2m -fexpose 518/323/323/323; -O 1083/755/755/
  403; fmapev 838/838/707/707; fmaprepro importer 393/330/198/198.
- hbTests sharethunk1: minimalTest 3/75, CAFlessTest 4/672, SAME failing sets as GD. Thunk variant fully
  validated on guard (ts, perf, nofib, horde-ad G2 alloc, tests). Draft: importer-specialised (D) horde-ad build
  was measured only with values-only prototype (sharesimp) -> wording narrowed; amended (local only).
- Mikolaj: "assume -fexpose-overloaded-unfoldings is always on, because HEAD will soon set it". Verified: S, M, N,
  R and all 41 sharing programs give IDENTICAL allocation with the flag for headpure/headmr/headthunk1/headthunkall1
  (sizerunX.sh, mrunX.sh, nestrunX.sh, smallAllX.sh; *-mrX.out, smallX.out). horde-ad.cabal already sets the flag
  (some modules opt out). Draft: flag stated in body intro; cross-module "-O" row dropped; guard-only columns
  marked "without the flag"; nofib marked "so far without". Amended locally. nofibX.sh NAME -> _make/NAME-X.
  chain16.sh -> job-chain16.out (after chain15): nofibX x4 + cmps; hbG2 sharethunk1 D.
- chain15: headpure perf = guard perf exactly (geomean 1.0000; the three fixes don't change compile allocation).
  headthunk1 on pure HEAD: testsuite 11800 + the same 2 expected-output changes (inline-check, rule2); perf vs
  headpure geomean +0.59%, 25/101 above 1%, max +4.92% T9961 = guard-based figures exactly.
- headthunkall1 (relaxation, pure HEAD): testsuite = headthunk1 (same 2 expected-output changes). perf vs headpure
  geomean +0.75% (headthunk1 +0.59%), 28/101 > 1%, max +11.1% T19695 (-O2); vs headthunk1: T19695 +11.1%,
  T21839c +2.9%, T13253 +1.7%, T17516 +0.9%, T13056 +0.8%, LargeRecord -0.4%. Cost of pushing bindings used by
  every alternative (copies into all of them). MR does the same -> compare when its perf lands.
- headmr (MR on pure HEAD) testsuite: 11798, 4 unexpected: ElemNoFusion_O1/_O2 (binder names only, x1 -> eta),
  T8331 (coercion form only), T18903 (REAL: duplicates the NOINLINE $wg into two alternatives -- the failure our
  first policy had; dup_ok excludes NOINLINE + join points). MR perf + nofib next in chain15.
- headmr perf vs headpure: geomean +0.28%, 11/101 > 1%, max +3.81% T21839c, T13253-spj -4.82%; T19695 +1.65%
  (relaxation +11.1%: shared budget lets threshold-size copies go into every alternative). Draft amended locally:
  in-short bullet on cost + NOINLINE, NOINLINE/join-point bullet, relaxation's compile cost, testsuite/perf
  paragraph on HEAD. Pending: nofib (4 compilers, then with -X), horde-ad mr12121 2, sharethunkall1 2, sharethunk1 D.
- nofib on pure HEAD vs headpure: headthunk1 geomean 1.0001 (mate +0.68%); headthunkall1 0.9993 (cichelli -10.0%,
  fulsom +6.0%); headmr 0.9999 (puzzle -6.3%, fulsom -2.9%, lift +4.5%, dom-lt +2.7%, fluid +2.2%). Draft amended.
  NEXT: decompose MR's nofib losses: build headmrFI (MR FloatIn+Pipeline, orig SimplUtils) in an untimed window,
  run nofib on puzzle, fulsom, lift, dom-lt, fluid (+ cichelli). Investigate relaxation's fulsom +6%.
- 2mr12121 build 2135 s. headmrFI (MR FloatIn+Pipeline, orig SimplUtils; buildHeadMR.sh mrFI headmrFI) and
  nofibSome.sh sub on 6 benchmarks (MB): fulsom HEAD 246.0 / MR 239.0 / MR-FI 239.0 / thunkall 260.8; fluid 212.6
  / 217.4 / 212.4 / 212.3; lift 249.6 / 260.9 / 260.9 / 249.6; cichelli 194.2 / 194.2 / 194.2 / 174.8; dom-lt
  524.8 / 539.0 / 525.7 / 524.8; puzzle 191.3 / 179.3 / 179.3 / 191.3. => MR's fluid/dom-lt losses from its
  postInlineUnconditionally rewrite; lift/puzzle/fulsom from its FloatIn. Not decomposing further (no bisecting).
  Draft amended.
- horde-ad G2 with guard-based mr12121 vs GD: prod 1.0017 [0.9980,1.0078], MNIST 1.0049 [0.9995,1.0111], conv
  1.0005 [0.9996,1.0087]. VTO rank 1 residual: 1500|500 G2G(no fix) +10.48% -> MR +0.35% (proto 0.00%);
  500|150 +4.90 -> +0.48; 300|100 +3.28 -> +0.52; 30|10 +0.76 -> +0.64. Others up to +1.11% (VTA test sets,
  cgrad s +0.78%). Draft amended.
- chain15 DONE 14:08. 2sharethunkall1 (relaxation, guard base) build 2164 s; alloc vs GD: prod 0.9997 [0.9971
  (grad k list), 1.0000], MNIST 1.0010 [0.9990, 1.0042] (nine test-set VTA/VTO +0.25..+0.42%, the ones MR has at
  +0.8..+1.1%), conv 1.0000 [0.9995,1.0006]. Draft amended. chain16 started 14:08 (nofibX x4, then hbG2 sharethunk1 D).
- nofib with -fexpose-overloaded-unfoldings (nofibX): headpure-X = headpure exactly (all 114); headthunk1-X,
  headmr-X, headthunkall1-X vs headpure-X = the no-flag comparisons. Draft amended. chain16 now: hbG2 sharethunk1 D.
- chain16 DONE 15:17. Dsharethunk1 build 2365 s, alloc = GD (prod 0.9998 [0.9984,1.0000], MNIST 1.0000, conv 1.0000
  [0.9984,1.0006]). ALL MEASUREMENTS COMPLETE; draft has no pending items. Amended locally (no push).
```
