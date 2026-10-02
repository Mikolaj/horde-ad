# Appendix C to the GHC !12121 comment: the scripts and raw results

Appendix to the comment drafted in [`docs/ghc-issue-floatin-duplicate-values-comment.md`](ghc-issue-floatin-duplicate-values-comment.md) for GHC [!12121](https://gitlab.haskell.org/ghc/ghc/-/merge_requests/12121); it is not posted with the comment, which links here. The scripts that built the compilers and ran the GHC testsuite, nofib and horde-ad, verbatim, and a summary of the results they produced. The programs and the scripts that ran them are in [appendix A](ghc-issue-floatin-duplicate-values-appendix-a-programs.md), the compiler changes in [appendix B](ghc-issue-floatin-duplicate-values-appendix-b-prototypes.md). The scripts name a machine-specific layout (`/opt/ghcsrc` the GHC tree at `9f48a5b908`, `/home/user/variants` the scratch tree, `/home/user/hb` a horde-ad checkout) and are recorded as run, not as portable tools.

Contents: [the compilers' names](#the-compilers-names), [scripts](#scripts), [results](#results).

## The compilers' names

Each compiler is a stage-1 GHC named `ghc-NAME` after the change it carries (the diffs in appendix B). On HEAD (`9f48a5b908`, without the fixes of guard): `headpure` HEAD itself; `headthunk1` the prototype; `headthunkall1` the prototype also pushing bindings that every alternative uses; `headshare1` the values-only prototype; `headmr` !12121; `headmrFI` !12121 without its `GHC.Core.Opt.Simplify.Utils` part. On guard (HEAD with the fixes of GHC [#27873](https://gitlab.haskell.org/ghc/ghc/-/work_items/27873), GHC [#27874](https://gitlab.haskell.org/ghc/ghc/-/work_items/27874) and GHC [#27880](https://gitlab.haskell.org/ghc/ghc/-/work_items/27880)): `guard` itself; `dupvalue`, `dupbudget`, `dupcreate` the size policies (inline threshold, budget per case, creation threshold); `dupshare` the values-only shared budget without the simplifier pass; `sharesimp` and `sharesimp1` with the full pass and with one iteration; `guardsimp` and `budgetsimp` the full pass alone and with the budget per case; `sharethunk1` and `sharethunkall1` the prototype and its relaxation; `sharelate` and `guardlate` float-in moved after the final simplifier, with and without the values-only shared budget; `mr12121` !12121; `spine`, `spineall`, `spine2`, `spine3`, `coldalt`, `funtop1` the float-out restrictions; `cselam`, `fibcse` the CSE and pipeline alternatives. A suffix `-X` (nofib) or `X` (small programs) marks a run with `-fexpose-overloaded-unfoldings`; everything else here ran without it.

horde-ad builds are named by source and compiler: a first part `2` or `G2` for the defining-module `SPECIALISE` source (the five `SPECIALISE interpretAst` pragmas hbG2.sh inserts) and `D` or `GD` for the importer-specialised one, then the compiler (`G2S` and `GDS` spine, `G2S2`/`GDS2` spine2, `G2F`/`GDF` funtop1, `G2DV`/`GDDV` dupvalue, `G2G` and `GD` guard). `GD` is the baseline everything is compared with, and `G2G` the defining-module build without a fix, the one with the 10.5% residual.

## Scripts

### Building the compilers

Each script swaps the changed files into the GHC tree, runs hadrian's stage-1 build, copies the binary to `ghc-NAME` and restores the tree, refusing to start when the tree is not in the state it restores to; buildGuard.sh built guard from the patched tree, and buildCselam.sh and buildFibcse.sh built from sources edited in place and not kept.

#### buildGuard.sh

```bash
#!/bin/bash
# Stage-2 GHC with alreadyCovered fix + CBV dict fix + relaxed specImport recursion guard.
cd /opt/ghcsrc || exit 1
export PATH=/opt/boottools:/opt/ghc912/bin:/opt/ghchead:$PATH
git diff --stat compiler/
s=$(date +%s)
hadrian/build --freeze1 -j4 --flavour=default+no_profiled_libs+no_dynamic_libs --docs=none > /home/user/variants/ghc-build-guard.log 2>&1
rc=$?; echo "ghc build exit=$rc seconds=$(( $(date +%s) - s ))"
[ $rc = 0 ] && cp -p _build/stage1/bin/ghc _build/stage1/bin/ghc-guard
echo DONE
```

#### buildFI.sh

```bash
#!/bin/bash
# Stage-1 GHC = ghc-guard + FloatIn dupvalue (SetLevels = HEAD). Restores spine SetLevels, orig FloatIn, ghc-spine binary.
cd /opt/ghcsrc || exit 1
export PATH=/opt/boottools:/opt/ghc912/bin:/opt/ghchead:$PATH
SL=compiler/GHC/Core/Opt/SetLevels.hs; FI=compiler/GHC/Core/Opt/FloatIn.hs; P=/home/user/variants/perf
cmp -s $SL $P/SetLevels.hs.spine-src || { echo "SetLevels is not the spine source"; exit 1; }
cmp -s $FI $P/FloatIn.hs.orig || { echo "FloatIn is not orig"; exit 1; }
cp $P/SetLevels.hs.orig $SL; cp $P/FloatIn.hs.$1 $FI
s=$(date +%s)
hadrian/build --freeze1 -j4 --flavour=default+no_profiled_libs+no_dynamic_libs --docs=none > /home/user/variants/ghc-build-$1.log 2>&1
rc=$?; echo "ghc build exit=$rc seconds=$(( $(date +%s) - s ))"
[ $rc = 0 ] && cp -p _build/stage1/bin/ghc _build/stage1/bin/ghc-$1
cp -p $P/SetLevels.hs.spine-src $SL; cp -p $P/FloatIn.hs.orig $FI; cp -p _build/stage1/bin/ghc-spine _build/stage1/bin/ghc
[ $rc = 0 ] || exit 1
echo BUILT
```

#### buildPL.sh

```bash
#!/bin/bash
# buildPL.sh FI NAME [PL]: stage-1 GHC = FloatIn.hs.FI + Pipeline.hs.PL (default postcse; SetLevels HEAD) -> ghc-NAME.
# Restores spine SetLevels, orig FloatIn, orig Pipeline, ghc-spine binary.
cd /opt/ghcsrc || exit 1
export PATH=/opt/boottools:/opt/ghc912/bin:/opt/ghchead:$PATH
SL=compiler/GHC/Core/Opt/SetLevels.hs; FI=compiler/GHC/Core/Opt/FloatIn.hs; PL=compiler/GHC/Core/Opt/Pipeline.hs
P=/home/user/variants/perf
cmp -s $SL $P/SetLevels.hs.spine-src || { echo "SetLevels is not the spine source"; exit 1; }
cmp -s $FI $P/FloatIn.hs.orig || { echo "FloatIn is not orig"; exit 1; }
cmp -s $PL $P/Pipeline.hs.orig || { echo "Pipeline is not orig"; exit 1; }
cp $P/SetLevels.hs.orig $SL; cp $P/FloatIn.hs.$1 $FI; cp $P/Pipeline.hs.${3:-postcse} $PL
s=$(date +%s)
hadrian/build --freeze1 -j4 --flavour=default+no_profiled_libs+no_dynamic_libs --docs=none > /home/user/variants/ghc-build-$2.log 2>&1
rc=$?; echo "ghc build $2 exit=$rc seconds=$(( $(date +%s) - s ))"
[ $rc = 0 ] && cp -p _build/stage1/bin/ghc _build/stage1/bin/ghc-$2
cp -p $P/SetLevels.hs.spine-src $SL; cp -p $P/FloatIn.hs.orig $FI; cp -p $P/Pipeline.hs.orig $PL
cp -p _build/stage1/bin/ghc-spine _build/stage1/bin/ghc
exit $rc
```

#### buildHead.sh

```bash
#!/bin/bash
# buildHead.sh FI PL NAME: stage-1 GHC = pure HEAD (no #27873/#27874/#27880 fixes) + FloatIn.hs.FI + Pipeline.hs.PL
# -> ghc-NAME.  Restores guard Specialise/Utils, spine SetLevels, orig FloatIn/Pipeline, ghc-spine binary.
cd /opt/ghcsrc || exit 1
export PATH=/opt/boottools:/opt/ghc912/bin:/opt/ghchead:$PATH
O=compiler/GHC/Core; P=/home/user/variants/perf
SL=$O/Opt/SetLevels.hs; FI=$O/Opt/FloatIn.hs; PL=$O/Opt/Pipeline.hs; SP=$O/Opt/Specialise.hs; UT=$O/Utils.hs
cmp -s $SL $P/SetLevels.hs.spine-src || { echo "SetLevels is not the spine source"; exit 1; }
cmp -s $FI $P/FloatIn.hs.orig || { echo "FloatIn is not orig"; exit 1; }
cmp -s $PL $P/Pipeline.hs.orig || { echo "Pipeline is not orig"; exit 1; }
cmp -s $SP $P/Specialise.hs.guard || { echo "Specialise is not guard"; exit 1; }
cmp -s $UT $P/Utils.hs.guard || { echo "Utils is not guard"; exit 1; }
cp $P/SetLevels.hs.orig $SL; cp $P/FloatIn.hs.$1 $FI; cp $P/Pipeline.hs.$2 $PL
cp $P/Specialise.hs.head $SP; cp $P/Utils.hs.head $UT
s=$(date +%s)
hadrian/build --freeze1 -j4 --flavour=default+no_profiled_libs+no_dynamic_libs --docs=none > /home/user/variants/ghc-build-$3.log 2>&1
rc=$?; echo "ghc build $3 exit=$rc seconds=$(( $(date +%s) - s ))"
[ $rc = 0 ] && cp -p _build/stage1/bin/ghc _build/stage1/bin/ghc-$3
cp -p $P/SetLevels.hs.spine-src $SL; cp -p $P/FloatIn.hs.orig $FI; cp -p $P/Pipeline.hs.orig $PL
cp -p $P/Specialise.hs.guard $SP; cp -p $P/Utils.hs.guard $UT
cp -p _build/stage1/bin/ghc-spine _build/stage1/bin/ghc
exit $rc
```

#### buildHeadMR.sh

```bash
#!/bin/bash
# buildHeadMR.sh NAME OUT: stage-1 GHC = pure HEAD (no #27873/#27874/#27880 fixes) + FloatIn.hs.NAME, Pipeline.hs.NAME, SimplUtils.hs.NAME (SetLevels HEAD)
# -> ghc-OUT.  Restores guard Specialise/Utils, spine SetLevels, orig FloatIn/Pipeline/Simplify.Utils, ghc-spine binary.
cd /opt/ghcsrc || exit 1
export PATH=/opt/boottools:/opt/ghc912/bin:/opt/ghchead:$PATH
O=compiler/GHC/Core/Opt; P=/home/user/variants/perf
SL=$O/SetLevels.hs; FI=$O/FloatIn.hs; PL=$O/Pipeline.hs; SU=$O/Simplify/Utils.hs
SP=$O/Specialise.hs; UT=compiler/GHC/Core/Utils.hs
cmp -s $SL $P/SetLevels.hs.spine-src || { echo "SetLevels is not the spine source"; exit 1; }
cmp -s $FI $P/FloatIn.hs.orig || { echo "FloatIn is not orig"; exit 1; }
cmp -s $PL $P/Pipeline.hs.orig || { echo "Pipeline is not orig"; exit 1; }
cmp -s $SU $P/SimplUtils.hs.orig || { echo "Simplify.Utils is not orig"; exit 1; }
cmp -s $SP $P/Specialise.hs.guard || { echo "Specialise is not guard"; exit 1; }
cmp -s $UT $P/Utils.hs.guard || { echo "Utils is not guard"; exit 1; }
cp $P/SetLevels.hs.orig $SL; cp $P/FloatIn.hs.$1 $FI; cp $P/Pipeline.hs.$1 $PL; cp $P/SimplUtils.hs.$1 $SU
cp $P/Specialise.hs.head $SP; cp $P/Utils.hs.head $UT
s=$(date +%s)
hadrian/build --freeze1 -j4 --flavour=default+no_profiled_libs+no_dynamic_libs --docs=none > /home/user/variants/ghc-build-$2.log 2>&1
rc=$?; echo "ghc build $2 exit=$rc seconds=$(( $(date +%s) - s ))"
[ $rc = 0 ] && cp -p _build/stage1/bin/ghc _build/stage1/bin/ghc-$2
cp -p $P/Specialise.hs.guard $SP; cp -p $P/Utils.hs.guard $UT; cp -p $P/SetLevels.hs.spine-src $SL; cp -p $P/FloatIn.hs.orig $FI; cp -p $P/Pipeline.hs.orig $PL; cp -p $P/SimplUtils.hs.orig $SU
cp -p _build/stage1/bin/ghc-spine _build/stage1/bin/ghc
exit $rc
```

#### buildMR.sh

```bash
#!/bin/bash
# buildMR.sh NAME: stage-1 GHC = guard + FloatIn.hs.NAME, Pipeline.hs.NAME, SimplUtils.hs.NAME (SetLevels HEAD)
# -> ghc-NAME.  Restores spine SetLevels, orig FloatIn/Pipeline/Simplify.Utils, ghc-spine binary.
cd /opt/ghcsrc || exit 1
export PATH=/opt/boottools:/opt/ghc912/bin:/opt/ghchead:$PATH
O=compiler/GHC/Core/Opt; P=/home/user/variants/perf
SL=$O/SetLevels.hs; FI=$O/FloatIn.hs; PL=$O/Pipeline.hs; SU=$O/Simplify/Utils.hs
cmp -s $SL $P/SetLevels.hs.spine-src || { echo "SetLevels is not the spine source"; exit 1; }
cmp -s $FI $P/FloatIn.hs.orig || { echo "FloatIn is not orig"; exit 1; }
cmp -s $PL $P/Pipeline.hs.orig || { echo "Pipeline is not orig"; exit 1; }
cmp -s $SU $P/SimplUtils.hs.orig || { echo "Simplify.Utils is not orig"; exit 1; }
cp $P/SetLevels.hs.orig $SL; cp $P/FloatIn.hs.$1 $FI; cp $P/Pipeline.hs.$1 $PL; cp $P/SimplUtils.hs.$1 $SU
s=$(date +%s)
hadrian/build --freeze1 -j4 --flavour=default+no_profiled_libs+no_dynamic_libs --docs=none > /home/user/variants/ghc-build-$1.log 2>&1
rc=$?; echo "ghc build $1 exit=$rc seconds=$(( $(date +%s) - s ))"
[ $rc = 0 ] && cp -p _build/stage1/bin/ghc _build/stage1/bin/ghc-$1
cp -p $P/SetLevels.hs.spine-src $SL; cp -p $P/FloatIn.hs.orig $FI; cp -p $P/Pipeline.hs.orig $PL; cp -p $P/SimplUtils.hs.orig $SU
cp -p _build/stage1/bin/ghc-spine _build/stage1/bin/ghc
exit $rc
```

#### buildVariant.sh

```bash
#!/bin/bash
# Stage-1 GHC = ghc-guard + variant $1 (perf/SetLevels.hs.$1)
# still floats). Restores the spine SetLevels.hs and binary afterwards. Exits on any failure.
cd /opt/ghcsrc || exit 1
export PATH=/opt/boottools:/opt/ghc912/bin:/opt/ghchead:$PATH
F=compiler/GHC/Core/Opt/SetLevels.hs
cmp -s _build/stage1/bin/ghc _build/stage1/bin/ghc-spine || { echo "stage1 ghc is not spine"; exit 1; }
cmp -s $F /home/user/variants/perf/SetLevels.hs.spine-src || { echo "SetLevels is not the spine source"; exit 1; }
cp /home/user/variants/perf/SetLevels.hs.$1 $F
s=$(date +%s)
hadrian/build --freeze1 -j4 --flavour=default+no_profiled_libs+no_dynamic_libs --docs=none > /home/user/variants/ghc-build-$1.log 2>&1
rc=$?; echo "ghc build exit=$rc seconds=$(( $(date +%s) - s ))"
[ $rc = 0 ] && cp -p _build/stage1/bin/ghc _build/stage1/bin/ghc-$1
cp -p /home/user/variants/perf/SetLevels.hs.spine-src $F; cp -p _build/stage1/bin/ghc-spine _build/stage1/bin/ghc
[ $rc = 0 ] || exit 1
echo DONE
```

#### buildDupvalue.sh

```bash
#!/bin/bash
# Stage-1 GHC = ghc-guard + FloatIn dupvalue (SetLevels = HEAD). Restores spine SetLevels, orig FloatIn, ghc-spine binary.
cd /opt/ghcsrc || exit 1
export PATH=/opt/boottools:/opt/ghc912/bin:/opt/ghchead:$PATH
SL=compiler/GHC/Core/Opt/SetLevels.hs; FI=compiler/GHC/Core/Opt/FloatIn.hs; P=/home/user/variants/perf
cmp -s $SL $P/SetLevels.hs.spine-src || { echo "SetLevels is not the spine source"; exit 1; }
cmp -s $FI $P/FloatIn.hs.orig || { echo "FloatIn is not orig"; exit 1; }
cp $P/SetLevels.hs.orig $SL; cp $P/FloatIn.hs.dupvalue $FI
s=$(date +%s)
hadrian/build --freeze1 -j4 --flavour=default+no_profiled_libs+no_dynamic_libs --docs=none > /home/user/variants/ghc-build-dupvalue.log 2>&1
rc=$?; echo "ghc build exit=$rc seconds=$(( $(date +%s) - s ))"
[ $rc = 0 ] && cp -p _build/stage1/bin/ghc _build/stage1/bin/ghc-dupvalue
cp -p $P/SetLevels.hs.spine-src $SL; cp -p $P/FloatIn.hs.orig $FI; cp -p _build/stage1/bin/ghc-spine _build/stage1/bin/ghc
[ $rc = 0 ] || exit 1
echo BUILT
```

#### buildSpine.sh

```bash
#!/bin/bash
# Stage-2 GHC = ghc-guard + PROTOTYPE: SetLevels: first float-out does not split spine lambdas.
cd /opt/ghcsrc || exit 1
export PATH=/opt/boottools:/opt/ghc912/bin:/opt/ghchead:$PATH
s=$(date +%s)
hadrian/build --freeze1 -j4 --flavour=default+no_profiled_libs+no_dynamic_libs --docs=none > /home/user/variants/ghc-build-spine.log 2>&1
rc=$?; echo "ghc build exit=$rc seconds=$(( $(date +%s) - s ))"
[ $rc = 0 ] && cp -p _build/stage1/bin/ghc _build/stage1/bin/ghc-spine
echo DONE
```

#### buildSpine2.sh

```bash
#!/bin/bash
# Stage-1 GHC = ghc-guard + spine2 (first pass: let-bound VALUES don't float out of spine lambdas unless to top; work
# still floats). Restores the spine SetLevels.hs and binary afterwards. Exits on any failure.
cd /opt/ghcsrc || exit 1
export PATH=/opt/boottools:/opt/ghc912/bin:/opt/ghchead:$PATH
F=compiler/GHC/Core/Opt/SetLevels.hs
cmp -s _build/stage1/bin/ghc _build/stage1/bin/ghc-spine || { echo "stage1 ghc is not spine"; exit 1; }
cmp -s $F /home/user/variants/perf/SetLevels.hs.spine-src || { echo "SetLevels is not the spine source"; exit 1; }
cp /home/user/variants/perf/SetLevels.hs.spine2 $F
s=$(date +%s)
hadrian/build --freeze1 -j4 --flavour=default+no_profiled_libs+no_dynamic_libs --docs=none > /home/user/variants/ghc-build-spine2.log 2>&1
rc=$?; echo "ghc build exit=$rc seconds=$(( $(date +%s) - s ))"
[ $rc = 0 ] && cp -p _build/stage1/bin/ghc _build/stage1/bin/ghc-spine2
cp -p /home/user/variants/perf/SetLevels.hs.spine-src $F; cp -p _build/stage1/bin/ghc-spine _build/stage1/bin/ghc
[ $rc = 0 ] || exit 1
echo DONE
```

#### buildSpineall.sh

```bash
#!/bin/bash
# Stage-1 GHC = ghc-spine with the rule in EVERY float-out pass (GHC #15606's proposal): drop `not (floatOverSat env)`.
# Restores the ghc-spine SetLevels.hs and binary afterwards. Exits on any failure.
cd /opt/ghcsrc || exit 1
export PATH=/opt/boottools:/opt/ghc912/bin:/opt/ghchead:$PATH
F=compiler/GHC/Core/Opt/SetLevels.hs
cmp -s _build/stage1/bin/ghc _build/stage1/bin/ghc-spine || { echo "stage1 ghc is not spine"; exit 1; }
cp -p $F /home/user/variants/perf/SetLevels.hs.spine
command grep -q '      | le_spine env, not (floatOverSat env)$' $F || { echo "pattern missing"; exit 1; }
sed -i 's/^      | le_spine env, not (floatOverSat env)$/      | le_spine env/' $F
git diff --stat $F
s=$(date +%s)
hadrian/build --freeze1 -j4 --flavour=default+no_profiled_libs+no_dynamic_libs --docs=none > /home/user/variants/ghc-build-spineall.log 2>&1
rc=$?; echo "ghc build exit=$rc seconds=$(( $(date +%s) - s ))"
[ $rc = 0 ] && cp -p _build/stage1/bin/ghc _build/stage1/bin/ghc-spineall
cp -p /home/user/variants/perf/SetLevels.hs.spine $F; cp -p _build/stage1/bin/ghc-spine _build/stage1/bin/ghc
[ $rc = 0 ] || exit 1
echo DONE
```

#### buildFuntop.sh

```bash
#!/bin/bash
# Stage-2 GHC = ghc-guard + PROTOTYPE: SetLevels floats let-bound functions only to top level.
cd /opt/ghcsrc || exit 1
export PATH=/opt/boottools:/opt/ghc912/bin:/opt/ghchead:$PATH
s=$(date +%s)
hadrian/build --freeze1 -j4 --flavour=default+no_profiled_libs+no_dynamic_libs --docs=none > /home/user/variants/ghc-build-funtop.log 2>&1
rc=$?; echo "ghc build exit=$rc seconds=$(( $(date +%s) - s ))"
[ $rc = 0 ] && cp -p _build/stage1/bin/ghc _build/stage1/bin/ghc-funtop
echo DONE
```

#### buildFuntop1.sh

```bash
#!/bin/bash
# Stage-2 GHC = ghc-guard + PROTOTYPE: SetLevels: early float-out floats let-bound functions only to top level.
cd /opt/ghcsrc || exit 1
export PATH=/opt/boottools:/opt/ghc912/bin:/opt/ghchead:$PATH
s=$(date +%s)
hadrian/build --freeze1 -j4 --flavour=default+no_profiled_libs+no_dynamic_libs --docs=none > /home/user/variants/ghc-build-funtop1.log 2>&1
rc=$?; echo "ghc build exit=$rc seconds=$(( $(date +%s) - s ))"
[ $rc = 0 ] && cp -p _build/stage1/bin/ghc _build/stage1/bin/ghc-funtop1
echo DONE
```

#### buildCselam.sh

```bash
#!/bin/bash
# Stage-2 GHC = ghc-guard + PROTOTYPE: CSE does not common up local let-bound lambdas.
cd /opt/ghcsrc || exit 1
export PATH=/opt/boottools:/opt/ghc912/bin:/opt/ghchead:$PATH
s=$(date +%s)
hadrian/build --freeze1 -j4 --flavour=default+no_profiled_libs+no_dynamic_libs --docs=none > /home/user/variants/ghc-build-cselam.log 2>&1
rc=$?; echo "ghc build exit=$rc seconds=$(( $(date +%s) - s ))"
[ $rc = 0 ] && cp -p _build/stage1/bin/ghc _build/stage1/bin/ghc-cselam
echo DONE
```

#### buildFibcse.sh

```bash
#!/bin/bash
# Stage-2 GHC = ghc-guard + PROTOTYPE: extra float-in before the late CSE.
cd /opt/ghcsrc || exit 1
export PATH=/opt/boottools:/opt/ghc912/bin:/opt/ghchead:$PATH
s=$(date +%s)
hadrian/build --freeze1 -j4 --flavour=default+no_profiled_libs+no_dynamic_libs --docs=none > /home/user/variants/ghc-build-fibcse.log 2>&1
rc=$?; echo "ghc build exit=$rc seconds=$(( $(date +%s) - s ))"
[ $rc = 0 ] && cp -p _build/stage1/bin/ghc _build/stage1/bin/ghc-fibcse
echo DONE
```

### The testsuite and `perf/compiler`

The full testsuite with the compiler's sources installed in the tree, as hadrian builds the stage-2 compiler from them; the `perf/compiler` metrics are written as a tsv by `--summary-metrics`, run on `perf/compiler` alone after the full testsuite.

#### tsFI.sh

```bash
#!/bin/bash
# tsFI.sh NAME: GHC testsuite + perf/compiler with FloatIn.hs.NAME (SetLevels HEAD); restores spine source + binary.
N=$1; V=/home/user/variants; P=$V/perf
cd /opt/ghcsrc || exit 1
export PATH=/opt/boottools:/opt/ghc912/bin:/opt/ghchead:$PATH
SL=compiler/GHC/Core/Opt/SetLevels.hs; FI=compiler/GHC/Core/Opt/FloatIn.hs
cmp -s $SL $P/SetLevels.hs.spine-src || { echo "SetLevels is not the spine source"; exit 1; }
cmp -s $FI $P/FloatIn.hs.orig || { echo "FloatIn is not orig"; exit 1; }
cp $P/SetLevels.hs.orig $SL; cp $P/FloatIn.hs.$N $FI
restore() { cp -p $P/SetLevels.hs.spine-src $SL; cp -p $P/FloatIn.hs.orig $FI; cp -p _build/stage1/bin/ghc-spine _build/stage1/bin/ghc; }
hadrian/build --freeze1 -j4 --flavour=default+no_profiled_libs+no_dynamic_libs --docs=none > $V/ghc-build-$N-ts.log 2>&1 || { restore; echo "$N build failed"; exit 1; }
hadrian/build test --freeze1 -j4 --flavour=default+no_profiled_libs+no_dynamic_libs --docs=none --summary=$P/ts-full-$N-summary.txt > $P/ts-full-$N.log 2>&1; echo "$N testsuite exit=$?"
sed -n '/^SUMMARY/,/fragile/p' $P/ts-full-$N-summary.txt | command grep -E 'expected passes|unexpected (failures|stat)'
sed -n '/^Unexpected results from/,/^$/p' $P/ts-full-$N-summary.txt
hadrian/build test --freeze1 -j2 --flavour=default+no_profiled_libs+no_dynamic_libs --docs=none --test-root-dirs=testsuite/tests/perf/compiler --summary-metrics=$P/perf-$N.tsv --summary=$P/perf-$N-summary.txt > $P/perf-$N.log 2>&1; echo "$N perf exit=$?"
restore
```

#### tsPL.sh

```bash
#!/bin/bash
# PLV=PL tsPL.sh FI NAME [perf]: GHC testsuite (unless "perf") + perf/compiler with FloatIn.hs.FI and Pipeline.hs.PL
# (default postcse)
# (SetLevels HEAD); restores spine SetLevels, orig FloatIn, orig Pipeline, ghc-spine binary.
FIN=$1; N=$2; V=/home/user/variants; P=$V/perf
cd /opt/ghcsrc || exit 1
export PATH=/opt/boottools:/opt/ghc912/bin:/opt/ghchead:$PATH
SL=compiler/GHC/Core/Opt/SetLevels.hs; FI=compiler/GHC/Core/Opt/FloatIn.hs; PL=compiler/GHC/Core/Opt/Pipeline.hs
cmp -s $SL $P/SetLevels.hs.spine-src || { echo "SetLevels is not the spine source"; exit 1; }
cmp -s $FI $P/FloatIn.hs.orig || { echo "FloatIn is not orig"; exit 1; }
cmp -s $PL $P/Pipeline.hs.orig || { echo "Pipeline is not orig"; exit 1; }
cp $P/SetLevels.hs.orig $SL; cp $P/FloatIn.hs.$FIN $FI; cp $P/Pipeline.hs.${PLV:-postcse} $PL
restore() { cp -p $P/SetLevels.hs.spine-src $SL; cp -p $P/FloatIn.hs.orig $FI; cp -p $P/Pipeline.hs.orig $PL; cp -p _build/stage1/bin/ghc-spine _build/stage1/bin/ghc; }
F="--freeze1 --flavour=default+no_profiled_libs+no_dynamic_libs --docs=none"
hadrian/build -j4 $F > $V/ghc-build-$N-ts.log 2>&1 || { restore; echo "$N build failed"; exit 1; }
if [ "$3" != perf ]; then
  hadrian/build test -j4 $F --summary=$P/ts-full-$N-summary.txt > $P/ts-full-$N.log 2>&1; echo "$N testsuite exit=$?"
  sed -n '/^SUMMARY/,/fragile/p' $P/ts-full-$N-summary.txt | command grep -E 'expected passes|unexpected (failures|stat)'
  sed -n '/^Unexpected results from/,/^$/p' $P/ts-full-$N-summary.txt
fi
hadrian/build test -j2 $F --test-root-dirs=testsuite/tests/perf/compiler --summary-metrics=$P/perf-$N.tsv --summary=$P/perf-$N-summary.txt > $P/perf-$N.log 2>&1; echo "$N perf exit=$?"
restore
```

#### tsHead.sh

```bash
#!/bin/bash
# PLV=PL tsHead.sh FI NAME [perf]: as tsPL.sh (Pipeline.hs.PL, default postcse), but on pure HEAD: no
# #27873/#27874/#27880 fixes in Specialise/Utils; SUV=X takes Simplify/Utils.hs from SimplUtils.hs.X (default orig);
# restores guard Specialise/Utils, spine SetLevels, orig FloatIn/Pipeline, ghc-spine binary.
FIN=$1; N=$2; V=/home/user/variants; P=$V/perf
cd /opt/ghcsrc || exit 1
export PATH=/opt/boottools:/opt/ghc912/bin:/opt/ghchead:$PATH
SL=compiler/GHC/Core/Opt/SetLevels.hs; FI=compiler/GHC/Core/Opt/FloatIn.hs; PL=compiler/GHC/Core/Opt/Pipeline.hs
SP=compiler/GHC/Core/Opt/Specialise.hs; UT=compiler/GHC/Core/Utils.hs
SU=compiler/GHC/Core/Opt/Simplify/Utils.hs
cmp -s $SL $P/SetLevels.hs.spine-src || { echo "SetLevels is not the spine source"; exit 1; }
cmp -s $FI $P/FloatIn.hs.orig || { echo "FloatIn is not orig"; exit 1; }
cmp -s $PL $P/Pipeline.hs.orig || { echo "Pipeline is not orig"; exit 1; }
cmp -s $SP $P/Specialise.hs.guard || { echo "Specialise is not guard"; exit 1; }
cmp -s $UT $P/Utils.hs.guard || { echo "Utils is not guard"; exit 1; }
cmp -s $SU $P/SimplUtils.hs.orig || { echo "Simplify.Utils is not orig"; exit 1; }
cp $P/SetLevels.hs.orig $SL; cp $P/FloatIn.hs.$FIN $FI; cp $P/Pipeline.hs.${PLV:-postcse} $PL
cp $P/Specialise.hs.head $SP; cp $P/Utils.hs.head $UT
cp $P/SimplUtils.hs.${SUV:-orig} $SU
restore() { cp -p $P/SimplUtils.hs.orig $SU; cp -p $P/Specialise.hs.guard $SP; cp -p $P/Utils.hs.guard $UT; cp -p $P/SetLevels.hs.spine-src $SL; cp -p $P/FloatIn.hs.orig $FI; cp -p $P/Pipeline.hs.orig $PL; cp -p _build/stage1/bin/ghc-spine _build/stage1/bin/ghc; }
F="--freeze1 --flavour=default+no_profiled_libs+no_dynamic_libs --docs=none"
hadrian/build -j4 $F > $V/ghc-build-$N-ts.log 2>&1 || { restore; echo "$N build failed"; exit 1; }
if [ "$3" != perf ]; then
  hadrian/build test -j4 $F --summary=$P/ts-full-$N-summary.txt > $P/ts-full-$N.log 2>&1; echo "$N testsuite exit=$?"
  sed -n '/^SUMMARY/,/fragile/p' $P/ts-full-$N-summary.txt | command grep -E 'expected passes|unexpected (failures|stat)'
  sed -n '/^Unexpected results from/,/^$/p' $P/ts-full-$N-summary.txt
fi
hadrian/build test -j2 $F --test-root-dirs=testsuite/tests/perf/compiler --summary-metrics=$P/perf-$N.tsv --summary=$P/perf-$N-summary.txt > $P/perf-$N.log 2>&1; echo "$N perf exit=$?"
restore
```

### nofib

`-s Fast` with `--compiler-arg` for the flag; nofibcmp.py compares the `allocated_bytes` of two runs and lists the benchmarks that moved by more than 0.05%.

#### nofibOne.sh

```bash
#!/bin/bash
# nofibOne.sh NAME: nofib (Fast) per benchmark with ghc-NAME into _make/NAME; dep-packages rebuilt once at the start.
# The aggregate run.results.tsv is removed before each invocation (Shake would skip the run otherwise).
G=$1; V=/home/user/variants
cd /opt/ghcsrc/nofib || exit 1
export PATH=/opt/ghchead:$PATH
R=$(find dist-newstyle -type f -name nofib-run -perm -u+x | head -1)
rm -rf _make/$G
L=$V/nofib-$G.log; : > $L
for d in imaginary/* spectral/* real/* shootout/* gc/*; do
  case $d in spectral/hartel) continue;; esac
  [ -f $d/Makefile ] || continue
  rm -f _make/$G/run.results.tsv
  $R -w /opt/ghcsrc/_build/stage1/bin/ghc-$G -o $G -s Fast -j 3 --keep-going $d >> $V/nofib3-$G.log 2>&1
  echo "$d $G exit=$?" >> $L
done
echo "nofib $G: $(command grep -c 'exit=0' $L) ok, $(command grep -vc 'exit=0' $L) failed"
python3 $V/nofibcmp.py guard $G > $V/nofib-guard-$G.cmp 2>&1; head -1 $V/nofib-guard-$G.cmp
find _make/$G -type f \( -name '*.o' -o -name '*.hi' -o -name Main \) -delete
```

#### nofibX.sh

```bash
#!/bin/bash
# nofibX.sh NAME: as nofibOne.sh, but with -fexpose-overloaded-unfoldings (--compiler-arg), into _make/NAME-X.
G=$1; O=$1-X; V=/home/user/variants
cd /opt/ghcsrc/nofib || exit 1
export PATH=/opt/ghchead:$PATH
R=$(find dist-newstyle -type f -name nofib-run -perm -u+x | head -1)
rm -rf _make/$O
L=$V/nofib-$O.log; : > $L
for d in imaginary/* spectral/* real/* shootout/* gc/*; do
  case $d in spectral/hartel) continue;; esac
  [ -f $d/Makefile ] || continue
  rm -f _make/$O/run.results.tsv
  $R -w /opt/ghcsrc/_build/stage1/bin/ghc-$G -o $O -s Fast -j 3 --keep-going --compiler-arg=-fexpose-overloaded-unfoldings $d >> $V/nofib3-$O.log 2>&1
  echo "$d $O exit=$?" >> $L
done
echo "nofib $O: $(command grep -c 'exit=0' $L) ok, $(command grep -vc 'exit=0' $L) failed"
find _make/$O -type f \( -name '*.o' -o -name '*.hi' -o -name Main \) -delete
```

#### nofibSome.sh

```bash
#!/bin/bash
# nofibSome.sh TAG "COMPILERS" "BENCHMARK-DIRS": nofib (Fast) for the given benchmarks only, into _make/C-TAG.
T=$1; CS=$2; BS=$3; V=/home/user/variants
cd /opt/ghcsrc/nofib || exit 1
export PATH=/opt/ghchead:$PATH
R=$(find dist-newstyle -type f -name nofib-run -perm -u+x | head -1)
for G in $CS; do O=$G-$T; rm -rf _make/$O
  for d in $BS; do rm -f _make/$O/run.results.tsv
    $R -w /opt/ghcsrc/_build/stage1/bin/ghc-$G -o $O -s Fast -j 3 --keep-going $d >> $V/nofib3-$O.log 2>&1 || echo "$G $d failed"
  done
done
python3 - "$T" $CS <<'PY'
import glob, os, sys
t, cs = sys.argv[1], sys.argv[2:]
base = '/opt/ghcsrc/nofib/_make'
def load(o):
    r = {}
    for f in glob.glob(f'{base}/{o}/**/Main.run.results.tsv', recursive=True):
        for l in open(f):
            k, v = l.rstrip('\n').split('\t')
            if k.endswith('//allocated_bytes'): r[os.path.relpath(os.path.dirname(f), f'{base}/{o}')] = float(v)
    return r
d = {c: load(f'{c}-{t}') for c in cs}
for b in sorted(d[cs[0]]):
    print(b.ljust(22), '  '.join(f'{c} {d[c].get(b, float("nan"))/1e6:.1f}' for c in cs))
PY
```

#### nofibcmp.py

```python
#!/usr/bin/env python3
"""nofibcmp.py A B: allocated_bytes per benchmark, B/A, from /opt/ghcsrc/nofib/_make/{A,B}."""
import glob, os, sys
base = '/opt/ghcsrc/nofib/_make'
def load(o):
    r = {}
    for f in glob.glob(f'{base}/{o}/**/Main.run.results.tsv', recursive=True):
        for l in open(f):
            k, v = l.rstrip('\n').split('\t')
            if k.endswith('//allocated_bytes'):
                r[os.path.relpath(os.path.dirname(f), f'{base}/{o}')] = float(v)
    return r
a, b = load(sys.argv[1]), load(sys.argv[2])
common = sorted(set(a) & set(b))
import math
rows = [(b[k] / a[k], k, a[k], b[k]) for k in common]
for r, k, x, y in sorted(rows, key=lambda t: -abs(math.log(t[0]))):
    if abs(r - 1) > 0.0005: print(f'{r:8.4f} {x:16.0f} {y:16.0f} {k}')
g = math.exp(sum(math.log(r) for r, *_ in rows) / len(rows)) if rows else float('nan')
print(f'{len(rows)} benchmarks, geomean {g:.4f}, min {min(rows)[0]:.4f}, max {max(rows)[0]:.4f}' if rows else 'none')
```

### horde-ad

hbG2.sh builds the whole package with one compiler, timed, runs the three allocation-checked benchmark suites and compares their allocation with GD's by alloc-cmp.py (whose summary line still says `nocbv/cbv` from an earlier use; the ratio is the build's over GD's); hbTests.sh runs `minimalTest` and `CAFlessTest`.

#### hbG2.sh

```bash
#!/bin/bash
# hbG2.sh NAME SRC(2|D): horde-ad with ghc-NAME, G2 source (SPECIALISE in AstInterpret) or baseline; timed; alloc vs GD.
N=$1; S=$2; V=/home/user/variants; T=$S$N
cd /home/user/hb || exit 1
export PATH=/opt/ghcsrc/_build/stage1/bin:/opt/ghchead:$PATH
B=build/x86_64-linux/ghc-10.1.20260925/horde-ad-0.4.0.0/b
F=src/HordeAd/Core/AstInterpret.hs
git diff --quiet HEAD -- $F && { echo "AstInterpret lacks the aicbv line"; exit 1; }
cp $F $V/AstInterpret-hb-$T.bak
if [ "$S" = 2 ]; then python3 - $F <<'PY'
import sys
p=sys.argv[1]; s=open(p).read()
imp='import HordeAd.Core.Types\n'; assert s.count(imp)==1
s=s.replace(imp, imp+'import HordeAd.Core.CarriersConcrete (Concrete)\nimport HordeAd.Core.OpsConcrete ()\n')
prag='{-# INLINEABLE interpretAst #-}\n'; assert s.count(prag)==1
s=s.replace(prag, '{-# INLINEABLE [1] interpretAst #-}\n{-# SPECIALISE interpretAst @Concrete @FullSpan #-}\n{-# SPECIALISE interpretAst @Concrete @PrimalSpan #-}\n{-# SPECIALISE interpretAst @Concrete @DualSpan #-}\n{-# SPECIALISE interpretAst @Concrete @PlainSpan #-}\n{-# SPECIALISE interpretAst @Concrete #-}\n')
open(p,'w').write(s)
PY
fi
rm -rf dist-$T; s=$(date +%s)
cabal --store-dir=/root/.cabal-store-patched build all --enable-tests --enable-benchmarks --enable-optimization --allow-newer -w /opt/ghcsrc/_build/stage1/bin/ghc-$N --builddir=dist-$T > $V/hb-build-$T.log 2>&1; rc=$?
echo "$T build exit=$rc seconds=$(( $(date +%s) - s )) $(date +%H:%M)"
cp $V/AstInterpret-hb-$T.bak $F
[ $rc = 0 ] || exit 1
for s in shortProdForCI shortMnistForCI convVjpBench; do
  dist-$T/$B/$s/build/$s/$s --regress allocated:iters --json $V/alloc/$T-$s.json +RTS -T -RTS > $V/alloc/$T-$s.log 2>&1 || { echo "$T $s alloc failed"; exit 1; }
  python3 $V/alloc-cmp.py $V/alloc/GD-$s.json $V/alloc/$T-$s.json > $V/alloc/$T-$s.cmp; echo "$T $s: $(head -1 $V/alloc/$T-$s.cmp)"
done
rm -rf dist-$T
```

#### hbTests.sh

```bash
#!/bin/bash
# hbTests.sh NAME: build minimalTest + CAFlessTest of the unmodified horde-ad tree with ghc-NAME into
# dist-tNAME, run them and dist-GD's (guard) binaries, compare the sets of failing tests.
N=$1; V=/home/user/variants; O=$V/hbt
cd /home/user/hb || exit 1
export PATH=/opt/ghcsrc/_build/stage1/bin:/opt/ghchead:$PATH
git diff --quiet HEAD -- src/HordeAd/Core/AstInterpret.hs && { echo "AstInterpret lacks the aicbv line"; exit 1; }
D=build/x86_64-linux/ghc-10.1.20260925/horde-ad-0.4.0.0/t
mkdir -p $O
cabal --store-dir=/root/.cabal-store-patched build minimalTest CAFlessTest --enable-tests --enable-benchmarks --enable-optimization --allow-newer -w /opt/ghcsrc/_build/stage1/bin/ghc-$N --builddir=dist-t$N > $V/hb-tbuild-$N.log 2>&1 || { echo "$N test build failed"; exit 1; }
for s in minimalTest CAFlessTest; do for arm in GD t$N; do
  dist-$arm/$D/$s/build/$s/$s > $O/$arm-$s.log 2>&1
  echo "$arm $s exit=$? $(tail -1 $O/$arm-$s.log)"
  command grep -E ': +FAIL' $O/$arm-$s.log | sed 's/: *FAIL.*//; s/^ *//' | sort > $O/$arm-$s.fails
done
  if cmp -s $O/GD-$s.fails $O/t$N-$s.fails; then echo "$s: same failing set ($(wc -l < $O/GD-$s.fails))"; else echo "$s: FAILING SETS DIFFER"; diff $O/GD-$s.fails $O/t$N-$s.fails | head; fi
done
rm -rf dist-t$N
```

#### alloc-cmp.py

```python
#!/usr/bin/env python3
"""Compare allocated bytes per iteration between two criterion JSON reports."""
import json,sys,math
def load(p):
    d=json.load(open(p)); reps=d[2] if isinstance(d,list) else d
    out={}
    for r in reps:
        name=r['reportName']; a=None
        for reg in r['reportAnalysis']['anRegress']:
            if reg['regResponder']=='allocated':
                a=reg['regCoeffs']['iters']['estPoint']
        out[name]=a
    return out
A=load(sys.argv[1]); B=load(sys.argv[2])
rows=[]
for k in A:
    if k in B and A[k] and B[k]: rows.append((B[k]/A[k],k,A[k],B[k]))
rows.sort()
g=math.exp(sum(math.log(r[0]) for r in rows)/len(rows))
print(f'{len(rows)} benchmarks, geomean nocbv/cbv allocation {g:.4f}, min {rows[0][0]:.4f}, max {rows[-1][0]:.4f}')
for r in rows[:5]+[None]+rows[-5:]:
    if r is None: print('  ...'); continue
    print(f'  {r[0]:.4f}  {r[2]:14.0f} -> {r[3]:14.0f}  {r[1]}')
```

### The small programs

smallAll.sh runs the sharing programs and the reproducers with the compilers given, smallAllX.sh the same with the flag; fmaprepro/run4.sh is the arity experiment of the across-modules interpreter.

#### smallAll.sh

```bash
#!/bin/bash
# All small programs with the given compilers (suffixes of ghc-*), on copies, results to stdout.
# smallAll.sh "guard spine spine2"
V=/home/user/variants; B=/opt/ghcsrc/_build/stage1/bin; CS=$1
W=$V/small-$(echo $CS | tr ' ' '-'); rm -rf $W; mkdir -p $W
for d in adv adv/const adv/heavy adv/spine adv/t15606; do
  echo "### $d (-O)"; mkdir -p $W/$d; cp $V/$d/*.hs $W/$d/; cp $V/adv/t15606/run.sh $W/$d/run.sh
  (cd $W/$d && ./run.sh "$CS" -O)
done
echo "### funtopneg Neg2 (-O)"; mkdir -p $W/neg; cp $V/funtopneg/Neg2.hs $W/neg/Neg2.hs; cp $V/adv/t15606/run.sh $W/neg/
(cd $W/neg && ./run.sh "$CS" -O)
for G in $CS; do
  echo "### fmap2m $G"
  mkdir -p $W/fmap2m-$G; cp $V/fmap2m/Lib.hs $V/fmap2m/LibArg.hs $V/fmap2m/Main.hs $V/fmap2m/run.sh $W/fmap2m-$G/
  (cd $W/fmap2m-$G && ./run.sh $B/ghc-$G $G -O -fexpose-overloaded-unfoldings && ./run.sh $B/ghc-$G $G -O)
  echo "### fmapev $G"
  mkdir -p $W/fmapev-$G; cp $V/fmapev/Lib.hs $V/fmapev/LibArg.hs $V/fmapev/Main.hs $V/fmapev/run.sh $W/fmapev-$G/
  (cd $W/fmapev-$G && ./run.sh $B/ghc-$G $G -O -fexpose-overloaded-unfoldings)
  echo "### fmaprepro $G (importer GD, defining-module G2G)"
  mkdir -p $W/fmaprepro-$G; cp $V/fmaprepro/Lib.hs $V/fmaprepro/Main.hs $V/fmaprepro/Ox.hs $V/fmaprepro/run.sh $W/fmaprepro-$G/
  (cd $W/fmaprepro-$G && GHC=$B/ghc-$G ./run.sh)
  echo "### fmap1s $G"
  for s in Repro ReproArg; do mkdir -p $W/fmap1s-$G-$s; cp $V/fmap1s/$s.hs $W/fmap1s-$G-$s/Repro.hs
    (cd $W/fmap1s-$G-$s && $B/ghc-$G -O Repro.hs -o r > build.log 2>&1 && echo "$s $(./r +RTS -s 2>&1 | command grep 'bytes allocated' | sed 's/^ *//')")
  done
done
echo DONE
```

#### smallAllX.sh

```bash
#!/bin/bash
# All small programs with the given compilers (suffixes of ghc-*), on copies, results to stdout.
# smallAll.sh "guard spine spine2"
V=/home/user/variants; B=/opt/ghcsrc/_build/stage1/bin; CS=$1
W=$V/smallX-$(echo $CS | tr ' ' '-'); rm -rf $W; mkdir -p $W
for d in adv adv/const adv/heavy adv/spine adv/t15606; do
  echo "### $d (-O)"; mkdir -p $W/$d; cp $V/$d/*.hs $W/$d/; cp $V/adv/t15606/run.sh $W/$d/run.sh
  (cd $W/$d && ./run.sh "$CS" -O -fexpose-overloaded-unfoldings)
done
echo "### funtopneg Neg2 (-O)"; mkdir -p $W/neg; cp $V/funtopneg/Neg2.hs $W/neg/Neg2.hs; cp $V/adv/t15606/run.sh $W/neg/
(cd $W/neg && ./run.sh "$CS" -O -fexpose-overloaded-unfoldings)
for G in $CS; do
  echo "### fmap2m $G"
  mkdir -p $W/fmap2m-$G; cp $V/fmap2m/Lib.hs $V/fmap2m/LibArg.hs $V/fmap2m/Main.hs $V/fmap2m/run.sh $W/fmap2m-$G/
  (cd $W/fmap2m-$G && ./run.sh $B/ghc-$G $G -O -fexpose-overloaded-unfoldings && ./run.sh $B/ghc-$G $G -O)
  echo "### fmapev $G"
  mkdir -p $W/fmapev-$G; cp $V/fmapev/Lib.hs $V/fmapev/LibArg.hs $V/fmapev/Main.hs $V/fmapev/run.sh $W/fmapev-$G/
  (cd $W/fmapev-$G && ./run.sh $B/ghc-$G $G -O -fexpose-overloaded-unfoldings)
  echo "### fmaprepro $G (importer GD, defining-module G2G)"
  mkdir -p $W/fmaprepro-$G; cp $V/fmaprepro/Lib.hs $V/fmaprepro/Main.hs $V/fmaprepro/Ox.hs $V/fmaprepro/run.sh $W/fmaprepro-$G/
  (cd $W/fmaprepro-$G && GHC=$B/ghc-$G ./run.sh)
  echo "### fmap1s $G"
  for s in Repro ReproArg; do mkdir -p $W/fmap1s-$G-$s; cp $V/fmap1s/$s.hs $W/fmap1s-$G-$s/Repro.hs
    (cd $W/fmap1s-$G-$s && $B/ghc-$G -O Repro.hs -o r > build.log 2>&1 && echo "$s $(./r +RTS -s 2>&1 | command grep 'bytes allocated' | sed 's/^ *//')")
  done
done
echo DONE
```

#### fmaprepro/run4.sh

```bash
#!/bin/bash
# Item 4: arity worker/wrapper by hand (Lib-ww.hs) against the \case form (Lib.hs), importer (GD-style) and
# defining-module SPECIALISE (G2G-style), with ghc-guard and ghc-spine. MB allocated.
F="-O -fexpose-overloaded-unfoldings -fspecialise-aggressively -fdicts-cheap -fkeep-auto-rules"
v() { d=$1; G=/opt/ghcsrc/_build/stage1/bin/$2; src=$3; rm -rf $d; mkdir -p $d
  sed -e "s/PHASE/$4/" -e "s/^SPEC$/$5/" $src > $d/Lib.hs; cp Main.hs Ox.hs $d/
  (cd $d && $G $F -ddump-stg-final -ddump-to-file -dsuppress-uniques Main.hs -o Main > build.log 2>&1) || { echo "$d build failed"; exit 1; }
  echo "== $d: $(cd $d && ./Main +RTS -s 2>&1 | command grep -E 'bytes allocated' | sed 's/^ *//')"; }
S1="{-# SPECIALISE interp :: KnownS s => Int -> E s -> Int #-}"
S2="{-# SPECIALISE winterp :: KnownS s => Int -> E s -> Int #-}"
v w-guard-lam-imp ghc-guard Lib.hs "" ""
v w-guard-lam-def ghc-guard Lib.hs "[1]" "$S1"
v w-guard-ww-imp ghc-guard Lib-ww.hs "" ""
v w-guard-ww-def ghc-guard Lib-ww.hs "[1]" "$S2"
v w-spine-lam-imp ghc-spine Lib.hs "" ""
v w-spine-lam-def ghc-spine Lib.hs "[1]" "$S1"
v w-spine-ww-imp ghc-spine Lib-ww.hs "" ""
v w-spine-ww-def ghc-spine Lib-ww.hs "[1]" "$S2"
echo DONE
```

### The job chains

The measurements ran as chains of these scripts, one after another, each exiting on the first failure.

#### chainAfterRetime.sh

```bash
#!/bin/bash
# After expRetime.sh: (1) fmap1s with ghc-guard -fno-cse (draft table cell), (2) item 4 run4.sh,
# (3) build ghc-spineall (#15606's rule in every pass) and run fmap1s with it. Exits on any failure.
# DO NOT EDIT WHILE RUNNING.
V=/home/user/variants
cd $V || exit 1
until command grep -q '^DONE' job-retime.out 2>/dev/null; do
  ps -eo args | awk '$0 ~ /expRetim[e]\.sh/ {f=1} END {exit !f}' || { echo "expRetime died"; exit 1; }
  sleep 30
done
echo "retime done $(date +%H:%M)"
r1s() {  # dir compiler flags source
  rm -rf $V/fmap1s/$1; mkdir -p $V/fmap1s/$1; cp $V/fmap1s/$4 $V/fmap1s/$1/Repro.hs
  (cd $V/fmap1s/$1 && /opt/ghcsrc/_build/stage1/bin/$2 -O $3 Repro.hs -o r > build.log 2>&1) || { echo "$1 build failed"; exit 1; }
  echo "fmap1s $1: $(cd $V/fmap1s/$1 && ./r +RTS -s 2>&1 | command grep -E 'bytes allocated' | sed 's/^ *//')"
}
r1s b-guard-nocse ghc-guard -fno-cse Repro.hs
(cd $V/fmaprepro && ./run4.sh) || { echo "run4 failed"; exit 1; }
./buildSpineall.sh || { echo "buildSpineall failed"; exit 1; }
r1s s-spineall-Repro ghc-spineall "" Repro.hs
r1s s-spineall-ReproArg ghc-spineall "" ReproArg.hs
echo DONE
```

#### chain2.sh

```bash
#!/bin/bash
# After chainAfterRetime.sh: the #15606-worry programs (adv/t15606) with ghc-guard, ghc-spine, ghc-spineall at -O.
# DO NOT EDIT WHILE RUNNING.
V=/home/user/variants
cd $V || exit 1
until command grep -q '^DONE' job-chain1.out 2>/dev/null; do
  ps -eo args | awk '$0 ~ /chainAfterRetim[e]\.sh/ {f=1} END {exit !f}' || { echo "chain1 died"; exit 1; }
  sleep 30
done
cd $V/adv/t15606 || exit 1
./run.sh "guard spine spineall" -O || exit 1
echo DONE
```

#### chain3.sh

```bash
#!/bin/bash
# After chain2: spine2 at scale. (1) horde-ad G2 source and baseline source with ghc-spine2, each build timed alone,
# alloc vs GD; (2) nofib (Fast) with ghc-spine2; (3) GHC testsuite + perf/compiler with spine2.
# Exits on any failure. DO NOT EDIT WHILE RUNNING.
V=/home/user/variants
cd $V || exit 1
until command grep -q '^DONE' job-chain2.out 2>/dev/null; do
  ps -eo args | awk '$0 ~ /chain2\.s[h]/ {f=1} END {exit !f}' || { echo "chain2 died"; exit 1; }
  sleep 30
done
echo "chain2 done $(date +%H:%M)"
# (1) horde-ad
cd /home/user/hb || exit 1
export PATH=/opt/ghcsrc/_build/stage1/bin:/opt/ghchead:$PATH
B=build/x86_64-linux/ghc-10.1.20260925/horde-ad-0.4.0.0/b
F=src/HordeAd/Core/AstInterpret.hs
git diff --quiet HEAD -- $F && { echo "AstInterpret lacks the aicbv line"; exit 1; }
cp $F $V/AstInterpret-hb-chain3.bak
C="cabal --store-dir=/root/.cabal-store-patched build all --enable-tests --enable-benchmarks --enable-optimization --allow-newer -w /opt/ghcsrc/_build/stage1/bin/ghc-spine2"
alloc() {
  for s in shortProdForCI shortMnistForCI convVjpBench; do
    dist-$1/$B/$s/build/$s/$s --regress allocated:iters --json $V/alloc/$1-$s.json +RTS -T -RTS > $V/alloc/$1-$s.log 2>&1 || { echo "$1 $s alloc failed"; exit 1; }
    python3 $V/alloc-cmp.py $V/alloc/GD-$s.json $V/alloc/$1-$s.json > $V/alloc/$1-$s.cmp; echo "$1 $s: $(head -1 $V/alloc/$1-$s.cmp)"
  done
}
python3 - $F <<'PY'
import sys
p=sys.argv[1]; s=open(p).read()
imp='import HordeAd.Core.Types\n'; assert s.count(imp)==1
s=s.replace(imp, imp+'import HordeAd.Core.CarriersConcrete (Concrete)\nimport HordeAd.Core.OpsConcrete ()\n')
prag='{-# INLINEABLE interpretAst #-}\n'; assert s.count(prag)==1
s=s.replace(prag, '{-# INLINEABLE [1] interpretAst #-}\n{-# SPECIALISE interpretAst @Concrete @FullSpan #-}\n{-# SPECIALISE interpretAst @Concrete @PrimalSpan #-}\n{-# SPECIALISE interpretAst @Concrete @DualSpan #-}\n{-# SPECIALISE interpretAst @Concrete @PlainSpan #-}\n{-# SPECIALISE interpretAst @Concrete #-}\n')
open(p,'w').write(s)
PY
rm -rf dist-G2S2; s=$(date +%s); $C --builddir=dist-G2S2 > $V/hb-build-G2S2.log 2>&1; rc=$?
echo "G2S2 build exit=$rc seconds=$(( $(date +%s) - s )) $(date +%H:%M)"
cp $V/AstInterpret-hb-chain3.bak $F
[ $rc = 0 ] || exit 1
alloc G2S2; rm -rf dist-G2S2
rm -rf dist-GDS2; s=$(date +%s); $C --builddir=dist-GDS2 > $V/hb-build-GDS2.log 2>&1; rc=$?
echo "GDS2 build exit=$rc seconds=$(( $(date +%s) - s )) $(date +%H:%M)"; [ $rc = 0 ] || exit 1
alloc GDS2
# (2) nofib
cd /opt/ghcsrc/nofib || exit 1
export PATH=/opt/ghchead:$PATH
R=$(find dist-newstyle -type f -name nofib-run -perm -u+x | head -1)
L=$V/nofib-spine2.log; : > $L
for d in imaginary/* spectral/* real/* shootout/* gc/*; do
  case $d in spectral/hartel) continue;; esac
  [ -f $d/Makefile ] || continue
  rm -f _make/spine2/run.results.tsv _make/spine2/dep-packages/*.env-file
  $R -w /opt/ghcsrc/_build/stage1/bin/ghc-spine2 -o spine2 -s Fast -j 3 --keep-going $d >> $V/nofib3-spine2.log 2>&1
  echo "$d spine2 exit=$?" >> $L
done
echo "nofib done $(date +%H:%M): $(command grep -c 'exit=0' $L) ok, $(command grep -vc 'exit=0' $L) failed"
python3 $V/nofibcmp.py guard spine2 > $V/nofib-guard-spine2.cmp 2>&1; tail -3 $V/nofib-guard-spine2.cmp
find _make/spine2 -type f \( -name '*.o' -o -name '*.hi' \) -delete
# (3) testsuite + perf
cd /opt/ghcsrc || exit 1
export PATH=/opt/boottools:/opt/ghc912/bin:/opt/ghchead:$PATH
SL=compiler/GHC/Core/Opt/SetLevels.hs
cmp -s $SL $V/perf/SetLevels.hs.spine-src || { echo "SetLevels is not the spine source"; exit 1; }
cp $V/perf/SetLevels.hs.spine2 $SL
hadrian/build --freeze1 -j4 --flavour=default+no_profiled_libs+no_dynamic_libs --docs=none > $V/ghc-build-spine2-ts.log 2>&1 || { cp $V/perf/SetLevels.hs.spine-src $SL; echo "build failed"; exit 1; }
cmp -s _build/stage1/bin/ghc _build/stage1/bin/ghc-spine2 || echo "note: rebuilt ghc differs from ghc-spine2 binary"
hadrian/build test --freeze1 -j4 --flavour=default+no_profiled_libs+no_dynamic_libs --docs=none --summary=$V/perf/ts-full-spine2-summary.txt > $V/perf/ts-full-spine2.log 2>&1; echo "testsuite exit=$?"
sed -n '/^SUMMARY/,/fragile/p' $V/perf/ts-full-spine2-summary.txt
hadrian/build test --freeze1 -j2 --flavour=default+no_profiled_libs+no_dynamic_libs --docs=none --test-root-dirs=testsuite/tests/perf/compiler --summary-metrics=$V/perf/perf-spine2.tsv --summary=$V/perf/perf-spine2-summary.txt > $V/perf/perf-spine2.log 2>&1; echo "perf exit=$?"
cp $V/perf/SetLevels.hs.spine-src $SL; cp -p _build/stage1/bin/ghc-spine _build/stage1/bin/ghc
echo DONE
```

#### chain4.sh

```bash
#!/bin/bash
# After chain3 (agreed work done): task #20 candidate "coldalt" (SW2 of Note [Saving work] for let-bound values:
# no float out of a multi-alternative case alternative unless to top). Build + all small programs. DO NOT EDIT WHILE RUNNING.
V=/home/user/variants
cd $V || exit 1
until command grep -q '^DONE' job-chain3.out 2>/dev/null; do
  ps -eo args | awk '$0 ~ /chain3\.s[h]/ {f=1} END {exit !f}' || { echo "chain3 died"; exit 1; }
  sleep 60
done
echo "chain3 done $(date +%H:%M)"
./buildVariant.sh coldalt || exit 1
./smallAll.sh "guard spine2 coldalt" > job-small3.out 2>&1 || exit 1
for d in small-guard-spine2-coldalt; do find $d -type f \( -name '*.o' -o -name '*.hi' -o -perm -u+x \) -delete; done
echo DONE
```

#### chain5.sh

```bash
#!/bin/bash
# After chain4: nofib with ghc-spine2 (chain3's run broke: env-file deleted per benchmark), then ghc-coldalt.
# DO NOT EDIT WHILE RUNNING.
V=/home/user/variants
cd $V || exit 1
until command grep -q '^DONE' job-chain4.out 2>/dev/null; do
  ps -eo args | awk '$0 ~ /chain4\.s[h]/ {f=1} END {exit !f}' || { echo "chain4 died"; exit 1; }
  sleep 60
done
echo "chain4 done $(date +%H:%M)"
./nofibOne.sh spine2
[ -x /opt/ghcsrc/_build/stage1/bin/ghc-coldalt ] && ./nofibOne.sh coldalt
echo "chain5 finished $(date +%H:%M)"
echo DONE
```

#### chain6.sh

```bash
#!/bin/bash
# dupvalue at scale: horde-ad G2 + baseline source with ghc-dupvalue (timed, alloc vs GD), then testsuite + perf.
# Exits on any failure. DO NOT EDIT WHILE RUNNING.
V=/home/user/variants
cd $V || exit 1
echo "start $(date +%H:%M)"
# (1) horde-ad
cd /home/user/hb || exit 1
export PATH=/opt/ghcsrc/_build/stage1/bin:/opt/ghchead:$PATH
B=build/x86_64-linux/ghc-10.1.20260925/horde-ad-0.4.0.0/b
F=src/HordeAd/Core/AstInterpret.hs
git diff --quiet HEAD -- $F && { echo "AstInterpret lacks the aicbv line"; exit 1; }
cp $F $V/AstInterpret-hb-chain6.bak
C="cabal --store-dir=/root/.cabal-store-patched build all --enable-tests --enable-benchmarks --enable-optimization --allow-newer -w /opt/ghcsrc/_build/stage1/bin/ghc-dupvalue"
alloc() {
  for s in shortProdForCI shortMnistForCI convVjpBench; do
    dist-$1/$B/$s/build/$s/$s --regress allocated:iters --json $V/alloc/$1-$s.json +RTS -T -RTS > $V/alloc/$1-$s.log 2>&1 || { echo "$1 $s alloc failed"; exit 1; }
    python3 $V/alloc-cmp.py $V/alloc/GD-$s.json $V/alloc/$1-$s.json > $V/alloc/$1-$s.cmp; echo "$1 $s: $(head -1 $V/alloc/$1-$s.cmp)"
  done
}
python3 - $F <<'PY'
import sys
p=sys.argv[1]; s=open(p).read()
imp='import HordeAd.Core.Types\n'; assert s.count(imp)==1
s=s.replace(imp, imp+'import HordeAd.Core.CarriersConcrete (Concrete)\nimport HordeAd.Core.OpsConcrete ()\n')
prag='{-# INLINEABLE interpretAst #-}\n'; assert s.count(prag)==1
s=s.replace(prag, '{-# INLINEABLE [1] interpretAst #-}\n{-# SPECIALISE interpretAst @Concrete @FullSpan #-}\n{-# SPECIALISE interpretAst @Concrete @PrimalSpan #-}\n{-# SPECIALISE interpretAst @Concrete @DualSpan #-}\n{-# SPECIALISE interpretAst @Concrete @PlainSpan #-}\n{-# SPECIALISE interpretAst @Concrete #-}\n')
open(p,'w').write(s)
PY
rm -rf dist-G2DV; s=$(date +%s); $C --builddir=dist-G2DV > $V/hb-build-G2DV.log 2>&1; rc=$?
echo "G2DV build exit=$rc seconds=$(( $(date +%s) - s )) $(date +%H:%M)"
cp $V/AstInterpret-hb-chain6.bak $F
[ $rc = 0 ] || exit 1
alloc G2DV; rm -rf dist-G2DV
rm -rf dist-GDDV; s=$(date +%s); $C --builddir=dist-GDDV > $V/hb-build-GDDV.log 2>&1; rc=$?
echo "GDDV build exit=$rc seconds=$(( $(date +%s) - s )) $(date +%H:%M)"; [ $rc = 0 ] || exit 1
alloc GDDV
# (3) testsuite + perf
cd /opt/ghcsrc || exit 1
export PATH=/opt/boottools:/opt/ghc912/bin:/opt/ghchead:$PATH
SL=compiler/GHC/Core/Opt/SetLevels.hs; FI=compiler/GHC/Core/Opt/FloatIn.hs; P=$V/perf
cmp -s $SL $P/SetLevels.hs.spine-src || { echo "SetLevels is not the spine source"; exit 1; }
cmp -s $FI $P/FloatIn.hs.orig || { echo "FloatIn is not orig"; exit 1; }
cp $P/SetLevels.hs.orig $SL; cp $P/FloatIn.hs.dupvalue $FI
restore() { cp -p $P/SetLevels.hs.spine-src $SL; cp -p $P/FloatIn.hs.orig $FI; cp -p _build/stage1/bin/ghc-spine _build/stage1/bin/ghc; }
hadrian/build --freeze1 -j4 --flavour=default+no_profiled_libs+no_dynamic_libs --docs=none > $V/ghc-build-dupvalue-ts.log 2>&1 || { restore; echo "build failed"; exit 1; }
cmp -s _build/stage1/bin/ghc _build/stage1/bin/ghc-dupvalue || echo "note: rebuilt ghc differs from ghc-dupvalue binary"
hadrian/build test --freeze1 -j4 --flavour=default+no_profiled_libs+no_dynamic_libs --docs=none --summary=$V/perf/ts-full-dupvalue-summary.txt > $V/perf/ts-full-dupvalue.log 2>&1; echo "testsuite exit=$?"
sed -n '/^SUMMARY/,/fragile/p' $V/perf/ts-full-dupvalue-summary.txt
hadrian/build test --freeze1 -j2 --flavour=default+no_profiled_libs+no_dynamic_libs --docs=none --test-root-dirs=testsuite/tests/perf/compiler --summary-metrics=$V/perf/perf-dupvalue.tsv --summary=$V/perf/perf-dupvalue-summary.txt > $V/perf/perf-dupvalue.log 2>&1; echo "perf exit=$?"
restore
echo DONE
```

#### chain6b.sh

```bash
#!/bin/bash
# chain6b (after container restart): horde-ad baseline source with ghc-dupvalue (timed, alloc vs GD), then testsuite + perf.
# Exits on any failure. DO NOT EDIT WHILE RUNNING.
V=/home/user/variants
cd $V || exit 1
echo "start $(date +%H:%M)"
# (1) horde-ad
cd /home/user/hb || exit 1
export PATH=/opt/ghcsrc/_build/stage1/bin:/opt/ghchead:$PATH
B=build/x86_64-linux/ghc-10.1.20260925/horde-ad-0.4.0.0/b
F=src/HordeAd/Core/AstInterpret.hs
git diff --quiet HEAD -- $F && { echo "AstInterpret lacks the aicbv line"; exit 1; }
cp $F $V/AstInterpret-hb-chain6.bak
C="cabal --store-dir=/root/.cabal-store-patched build all --enable-tests --enable-benchmarks --enable-optimization --allow-newer -w /opt/ghcsrc/_build/stage1/bin/ghc-dupvalue"
alloc() {
  for s in shortProdForCI shortMnistForCI convVjpBench; do
    dist-$1/$B/$s/build/$s/$s --regress allocated:iters --json $V/alloc/$1-$s.json +RTS -T -RTS > $V/alloc/$1-$s.log 2>&1 || { echo "$1 $s alloc failed"; exit 1; }
    python3 $V/alloc-cmp.py $V/alloc/GD-$s.json $V/alloc/$1-$s.json > $V/alloc/$1-$s.cmp; echo "$1 $s: $(head -1 $V/alloc/$1-$s.cmp)"
  done
}
rm -rf dist-GDDV; s=$(date +%s); $C --builddir=dist-GDDV > $V/hb-build-GDDV.log 2>&1; rc=$?
echo "GDDV build exit=$rc seconds=$(( $(date +%s) - s )) $(date +%H:%M)"; [ $rc = 0 ] || exit 1
alloc GDDV
# (3) testsuite + perf
cd /opt/ghcsrc || exit 1
export PATH=/opt/boottools:/opt/ghc912/bin:/opt/ghchead:$PATH
SL=compiler/GHC/Core/Opt/SetLevels.hs; FI=compiler/GHC/Core/Opt/FloatIn.hs; P=$V/perf
cmp -s $SL $P/SetLevels.hs.spine-src || { echo "SetLevels is not the spine source"; exit 1; }
cmp -s $FI $P/FloatIn.hs.orig || { echo "FloatIn is not orig"; exit 1; }
cp $P/SetLevels.hs.orig $SL; cp $P/FloatIn.hs.dupvalue $FI
restore() { cp -p $P/SetLevels.hs.spine-src $SL; cp -p $P/FloatIn.hs.orig $FI; cp -p _build/stage1/bin/ghc-spine _build/stage1/bin/ghc; }
hadrian/build --freeze1 -j4 --flavour=default+no_profiled_libs+no_dynamic_libs --docs=none > $V/ghc-build-dupvalue-ts.log 2>&1 || { restore; echo "build failed"; exit 1; }
cmp -s _build/stage1/bin/ghc _build/stage1/bin/ghc-dupvalue || echo "note: rebuilt ghc differs from ghc-dupvalue binary"
hadrian/build test --freeze1 -j4 --flavour=default+no_profiled_libs+no_dynamic_libs --docs=none --summary=$V/perf/ts-full-dupvalue-summary.txt > $V/perf/ts-full-dupvalue.log 2>&1; echo "testsuite exit=$?"
sed -n '/^SUMMARY/,/fragile/p' $V/perf/ts-full-dupvalue-summary.txt
hadrian/build test --freeze1 -j2 --flavour=default+no_profiled_libs+no_dynamic_libs --docs=none --test-root-dirs=testsuite/tests/perf/compiler --summary-metrics=$V/perf/perf-dupvalue.tsv --summary=$V/perf/perf-dupvalue-summary.txt > $V/perf/perf-dupvalue.log 2>&1; echo "perf exit=$?"
restore
echo DONE
```

#### chain7.sh

```bash
#!/bin/bash
# After chain6b: build dupbudget + dupcreate (FloatIn size variants), then size worst cases, all small programs, nofib.
# DO NOT EDIT WHILE RUNNING.
V=/home/user/variants
cd $V || exit 1
until command grep -q '^DONE' job-chain6b.out 2>/dev/null; do
  ps -eo args | awk '$0 ~ /chain6b\.s[h]/ {f=1} END {exit !f}' || { echo "chain6b died"; exit 1; }
  sleep 60
done
echo "chain6b done $(date +%H:%M)"
./buildFI.sh dupbudget || exit 1
./buildFI.sh dupcreate || exit 1
(cd adv/size && ./sizerun.sh "guard dupvalue dupbudget dupcreate") > job-size2.out 2>&1
echo "sizerun done $(date +%H:%M)"
./smallAll.sh "guard dupbudget dupcreate" > job-small5.out 2>&1
find small-guard-dupbudget-dupcreate -type f \( -name '*.o' -o -name '*.hi' -o -perm -u+x \) -delete
echo "smallAll done $(date +%H:%M)"
./nofibOne.sh dupbudget
./nofibOne.sh dupcreate
echo "chain7 finished $(date +%H:%M)"
echo DONE
```

#### chain8.sh

```bash
#!/bin/bash
# After chain7: testsuite+perf with dupbudget and dupcreate; horde-ad G2 source with both; baseline with dupcreate.
# DO NOT EDIT WHILE RUNNING.
V=/home/user/variants
cd $V || exit 1
until command grep -q '^DONE' job-chain7.out 2>/dev/null; do
  ps -eo args | awk '$0 ~ /chain7\.s[h]/ {f=1} END {exit !f}' || { echo "chain7 died"; exit 1; }
  sleep 60
done
echo "chain7 done $(date +%H:%M)"
./tsFI.sh dupbudget || exit 1
./tsFI.sh dupcreate || exit 1
./hbG2.sh dupbudget 2 || exit 1
./hbG2.sh dupcreate 2 || exit 1
./hbG2.sh dupcreate D || exit 1
echo "chain8 finished $(date +%H:%M)"
echo DONE
```

#### chain9.sh

```bash
#!/bin/bash
# After chain8: testsuite+perf with dupshare (shared duplication budget); horde-ad G2 source with dupshare.
# DO NOT EDIT WHILE RUNNING.
V=/home/user/variants
cd $V || exit 1
until command grep -q '^DONE' job-chain8.out 2>/dev/null; do
  ps -eo args | awk '$0 ~ /chain8\.s[h]/ {f=1} END {exit !f}' || { echo "chain8 died"; exit 1; }
  sleep 60
done
echo "chain8 done $(date +%H:%M)"
./tsFI.sh dupshare || exit 1
./hbG2.sh dupshare 2 || exit 1
echo "chain9 finished $(date +%H:%M)"
echo DONE
```

#### chain10.sh

```bash
#!/bin/bash
# After chain8: sharesimp (FloatIn dupshare + simplifier after late CSE): testsuite + perf; perf of the extra
# simplifier alone (guardsimp); horde-ad G2 source and baseline with sharesimp.  DO NOT EDIT WHILE RUNNING.
V=/home/user/variants
cd $V || exit 1
until command grep -q '^DONE' job-chain8.out 2>/dev/null; do
  ps -eo args | awk '$0 ~ /chain8\.s[h]/ {f=1} END {exit !f}' || { echo "chain8 died"; exit 1; }
  sleep 60
done
echo "chain8 done $(date +%H:%M)"
./tsPL.sh dupshare sharesimp || exit 1
./tsPL.sh orig guardsimp perf || exit 1
./hbG2.sh sharesimp 2 || exit 1
./hbG2.sh sharesimp D || exit 1
echo "chain10 finished $(date +%H:%M)"
echo DONE
```

#### chain11.sh

```bash
#!/bin/bash
# After chain10: nofib with sharesimp; horde-ad minimalTest + CAFlessTest with sharesimp vs guard.
# DO NOT EDIT WHILE RUNNING.
V=/home/user/variants
cd $V || exit 1
until command grep -q '^DONE' job-chain10.out 2>/dev/null; do
  ps -eo args | awk '$0 ~ /chain10\.s[h]/ {f=1} END {exit !f}' || { echo "chain10 died"; exit 1; }
  sleep 60
done
echo "chain10 done $(date +%H:%M)"
./nofibOne.sh sharesimp || exit 1
./hbTests.sh sharesimp || exit 1
echo "chain11 finished $(date +%H:%M)"
echo DONE
```

#### chain12.sh

```bash
#!/bin/bash
# After chain11: sharelate (FloatIn dupshare + late float-in after simplify "final"): testsuite + perf, nofib,
# horde-ad G2 source.  DO NOT EDIT WHILE RUNNING.
V=/home/user/variants
cd $V || exit 1
until command grep -q '^DONE' job-chain11.out 2>/dev/null; do
  ps -eo args | awk '$0 ~ /chain11\.s[h]/ {f=1} END {exit !f}' || { echo "chain11 died"; exit 1; }
  sleep 60
done
echo "chain11 done $(date +%H:%M)"
PLV=latefi ./tsPL.sh dupshare sharelate || exit 1
./nofibOne.sh sharelate || exit 1
./hbG2.sh sharelate 2 || exit 1
echo "chain12 finished $(date +%H:%M)"
echo DONE
```

#### chain13.sh

```bash
#!/bin/bash
# sharesimp1 (FloatIn dupshare + ONE-iteration simplifier after the late CSE): testsuite + perf, nofib,
# horde-ad G2 source.  DO NOT EDIT WHILE RUNNING.
V=/home/user/variants
cd $V || exit 1
PLV=postcse1 ./tsPL.sh dupshare sharesimp1 || exit 1
./nofibOne.sh sharesimp1 || exit 1
./hbG2.sh sharesimp1 2 || exit 1
echo "chain13 finished $(date +%H:%M)"
echo DONE
```

#### chain14.sh

```bash
#!/bin/bash
# sharethunk1 (shared budget for values AND thunks + one-iteration simplifier after late CSE) on guard:
# testsuite + perf, nofib, horde-ad G2, horde-ad tests.  Then pure HEAD: perf of headpure (baseline),
# testsuite + perf of headthunk1, nofib of both, horde-ad D/G2 with headpure and G2 with headthunk1.
# DO NOT EDIT WHILE RUNNING.
V=/home/user/variants
cd $V || exit 1
PLV=postcse1 ./tsPL.sh sharethunk sharethunk1 || exit 1
./nofibOne.sh sharethunk1 || exit 1
./hbG2.sh sharethunk1 2 || exit 1
./hbTests.sh sharethunk1 || exit 1
PLV=orig ./tsHead.sh orig headpure perf || exit 1
PLV=postcse1 ./tsHead.sh sharethunk headthunk1 || exit 1
./nofibOne.sh headpure || exit 1
./nofibOne.sh headthunk1 || exit 1
python3 $V/nofibcmp.py headpure headthunk1 > $V/nofib-headpure-headthunk1.cmp 2>&1; echo "headthunk1 vs headpure: $(tail -1 $V/nofib-headpure-headthunk1.cmp)"
./hbG2.sh headpure D || exit 1
./hbG2.sh headpure 2 || exit 1
./hbG2.sh headthunk1 2 || exit 1
echo "chain14 finished $(date +%H:%M)"
echo DONE
```

#### chain15.sh

```bash
#!/bin/bash
# Pure HEAD (for !12121): perf of headpure; testsuite + perf of headthunk1, headthunkall1, headmr; nofib of all four
# (compared with headpure); horde-ad G2 source with guard-based mr12121 and sharethunkall1.
# DO NOT EDIT WHILE RUNNING.
V=/home/user/variants
cd $V || exit 1
while ps -eo args | awk '$0 ~ /hbTests\.s[h]/ {f=1} END {exit !f}'; do sleep 60; done
echo "hbTests done $(date +%H:%M)"
PLV=orig ./tsHead.sh orig headpure perf || exit 1
PLV=postcse1 ./tsHead.sh sharethunk headthunk1 || exit 1
PLV=postcse1 ./tsHead.sh sharethunkall headthunkall1 || exit 1
PLV=mr12121 SUV=mr12121 ./tsHead.sh mr12121 headmr || exit 1
for G in headpure headthunk1 headthunkall1 headmr; do ./nofibOne.sh $G || exit 1; done
for G in headthunk1 headthunkall1 headmr; do
  python3 $V/nofibcmp.py headpure $G > $V/nofib-headpure-$G.cmp 2>&1; echo "nofib $G vs headpure: $(tail -1 $V/nofib-headpure-$G.cmp)"
done
./hbG2.sh mr12121 2 || exit 1
./hbG2.sh sharethunkall1 2 || exit 1
echo "chain15 finished $(date +%H:%M)"
echo DONE
```

#### chain16.sh

```bash
#!/bin/bash
# After chain15: nofib with -fexpose-overloaded-unfoldings for headpure, headthunk1, headmr, headthunkall1
# (compared with headpure-X, and headpure-X with headpure); horde-ad baseline source with sharethunk1.
# DO NOT EDIT WHILE RUNNING.
V=/home/user/variants
cd $V || exit 1
until command grep -q '^DONE' job-chain15.out 2>/dev/null; do
  ps -eo args | awk '$0 ~ /chain15\.s[h]/ {f=1} END {exit !f}' || { echo "chain15 died"; exit 1; }
  sleep 60
done
echo "chain15 done $(date +%H:%M)"
for G in headpure headthunk1 headmr headthunkall1; do ./nofibX.sh $G || exit 1; done
for G in headthunk1 headmr headthunkall1; do
  python3 $V/nofibcmp.py headpure-X $G-X > $V/nofib-headpure-X-$G-X.cmp 2>&1; echo "nofib -X $G vs headpure: $(tail -1 $V/nofib-headpure-X-$G-X.cmp)"
done
python3 $V/nofibcmp.py headpure headpure-X > $V/nofib-headpure-headpure-X.cmp 2>&1; echo "nofib headpure: -X vs plain: $(tail -1 $V/nofib-headpure-headpure-X.cmp)"
./hbG2.sh sharethunk1 D || exit 1
echo "chain16 finished $(date +%H:%M)"
echo DONE
```

## Results

Each change's ratio to the unchanged compiler, geometric mean and range: bytes allocated by the 101 compile-time tests of `perf/compiler` and by 114 nofib benchmarks, on HEAD; and by the 158 benchmarks of horde-ad's defining-module build against its importer-specialised build GD, on guard.

| change | perf/compiler | nofib | horde-ad | testsuite failures |
|---|---:|---:|---:|---:|
| prototype | 1.0059 (0.999-1.049) | 1.0001 (1.000-1.007) | 1.0000 (0.998-1.001) | rule2, inline-check |
| prototype, also every-alternative bindings | 1.0075 (0.999-1.111) | 0.9993 (0.900-1.060) | 1.0001 (0.997-1.004) | rule2, inline-check |
| !12121 | 1.0028 (0.952-1.038) | 0.9999 (0.937-1.046) | 1.0014 (0.998-1.011) | T18903, ElemNoFusion_O1, _O2, T8331 |
| none | 1 | 1 | 1.0015 (0.998-1.105) |  |

Whole-package horde-ad builds took 1949 to 2365 seconds with the duplicating compilers and !12121; the small programs' figures are the comment's.
