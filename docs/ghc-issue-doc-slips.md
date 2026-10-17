# GHC issue: documentation slips, Notes and user's guide text that the code on master contradicts

Filed as GHC [#27973](https://gitlab.haskell.org/ghc/ghc/-/work_items/27973) on 2026-10-17; the text from "## Summary" down is the filed body, in the tracker's documentation template. Title: **Documentation slips: Notes and user's guide text that the code on master contradicts**. Found while checking the GHC code behind surprises in how GHC HEAD compiles horde-ad and orthotope, and by a scan of the user's guide for other `:shortdesc:` defaults that differ from the `:default:` field; Mikolaj pointed out the two `-funfolding-use-threshold` defaults. Every quotation and line link was checked against master f93d523c (2026-10-15). The examples ran on GHC HEAD 10.1.20260918, a build of `wip/T27737` (6913545fd3) on master e2d5702699 with uncommitted patches; none of these changes the code that the items cite (checked by diff). The prose is ASD-STE100 Simplified Technical English. Two slips of the same kind are already on the tracker and are left out: `-fmax-forced-spec-args` documented with two defaults (GHC [#27332](https://gitlab.haskell.org/ghc/ghc/-/work_items/27332), fixed by the open [!16651](https://gitlab.haskell.org/ghc/ghc/-/merge_requests/16651)), and `-dinline-check` and `-drule-check` documented with `=` (GHC [#22015](https://gitlab.haskell.org/ghc/ghc/-/work_items/22015)).

## Summary

Location of documentation issue: the GHC user's guide (items 1 and 2), and Notes and comments in the compiler source (items 3 to 8).

Some Notes and some user's guide text say things that the code on master does not do. Each item below quotes the text, gives its lines at master f93d523c, and says what the code does. The items are independent. Each item needs a text change only, except item 2, where a fix of #21471 can make the text true instead.

### 1. `-funfolding-use-threshold` has two different defaults in one entry

[`using-optimisation.rst`, lines 1815-1820][rst-use]:

```
    :shortdesc: *default: 90.* Tweak unfolding settings.
    ...
    :default: 80
```

The code has `unfoldingUseThreshold   = 90` ([`GHC.Core.Unfold`, line 103][unfold]). Thus the rendered flag table shows 90, and the entry of the flag shows "Default: 80". #24653 reported the wrong default. Its fix, !12407 (commit [a1c24df0e6][a1c24df0e6]), changed `:shortdesc:` but not `:default:`.

### 2. The `-g` text says that debug information does not change the optimisations

[`debug-info.rst`, lines 72-73][rst-g]: "Note that this debugging information does not affect the optimizations performed by GHC."

On HEAD, `-g1` changes the optimised Core. #21471 tracks this in general. Here are two small examples. In both, `-dannot-lint` finds the change and names the pass, and `-fobject-determinism` does not remove the change.

Exitification stops at a source note:

```haskell
module X (loop) where

loop :: Int -> Int -> Int -> Int
loop t n0 x0 = go n0 x0
  where
    go :: Int -> Int -> Int
    go 0 x = t * (x * x) + t * x + x
    go n x = go (n - 1) (x + t)
```

With `ghc -O -fforce-recomp -ddump-simpl -dsuppress-all -dsuppress-uniques X.hs`, the loop has `0# -> jump exit ww3`. With `-g1` added, the loop has no exit join point. With `-g1 -dannot-lint` added, GHC prints `*** Core Lint warning : in result of Exitification transformation ***`.

CSE does not share a string literal under a source note:

```haskell
module B (f, g) where

f :: Int -> Int
f n = errorWithoutStackTrace ("bad index: " ++ show n)

g :: Int -> String
g n = "bad index: " ++ show n
```

With the same command on module `B`, the module has one literal, and `f` uses it: `errorWithoutStackTrace (unpackAppendCString# g1 (itos ww []))`. With `-g1` added, the module has a second literal, `lvl = "bad index: "#`, and `f` uses it: `errorWithoutStackTrace (unpackAppendCString# lvl (itos ww []))`. With `-g1 -dannot-lint` added, GHC prints `*** Core Lint warning : in result of Common sub-expression ***` and `lvl /= lvl`.

### 3. Note [inl_inline and inl_act] gives the NOINLINE phases the wrong way round

[InlinePragma.hs, lines 127-129][note-inl]:

```
  E.g  If you write INLINE[1]    then inl_act will be set to ActiveAfter 1
       If you write NOINLINE[1]  then inl_act will be set to ActiveBefore 1
       If you write NOINLINE[~1] then inl_act will be set to ActiveAfter 1
```

The parser's `explicit_activation` ([`Parser.y`, lines 2862-2867][parser]) makes `[k]` into `ActiveAfter k` and `[~k]` into `ActiveBefore k`, for every inline pragma. The user's guide ([`pragmas.rst`, lines 566-571][rst-noinline]) agrees with the parser: "`NOINLINE[k] f` means: do not inline `f` until phase `k`, but from phase `k` onwards be willing to inline it". Thus `NOINLINE[1]` sets `ActiveAfter 1`, and `NOINLINE[~1]` sets `ActiveBefore 1`.

### 4. Note [Inlining in gentle mode] is stale

[Simplify/Utils.hs, lines 1324-1327][note-gentle]:

```
Something is inlined if
   (i)   the sm_inline flag is on, AND
   (ii)  the thing has an INLINE pragma, AND
   (iii) the thing is inlinable in the earliest phase.
```

And [lines 1345-1346][note-gentle2]: "However, *sometimes* SimplGently must do no call-site inlining at all (hence sm_inline = False)."

The code does not do this:

1. `activeUnfolding` ([Simplify/Inline.hs, lines 122-133][active]) tests only the activation and `sm_inline`. The test for a stable unfolding is commented out.
2. `initGentleSimplMode` ([Driver/Config/Core/Opt/Simplify.hs, lines 79-85][gentle]) takes `sm_inline = True` from `initSimplMode` ([line 66][initmode]) and changes only `sm_case_case`.
3. Only `updModeForRuleLHS` ([Simplify/Utils.hs, lines 1208-1213][rulelhs]) and the GHCi mode of `initSimplifyExprOpts` ([Driver/Config/Core/Opt/Simplify.hs, lines 27-31][ghci]) set `sm_inline = False`.

Thus, in the gentle run, the simplifier inlines a function without a pragma when the usual size rules accept it. The Note has been stale since commit [2effe18ab5][2effe18ab5] (2017, "The Early Inline Patch"), which "switches on sm_inline even in the InitialPhase (aka "gentle" phase)". Nothing in `compiler/` refers to this Note. Example:

```haskell
module Gentle (inlPlain, usePlain) where

inlPlain :: Int -> Maybe Int
inlPlain x = case x of { 6 -> Nothing; _ -> Just (x + 6) }

usePlain :: Int
usePlain = case inlPlain 5 of { Nothing -> 0; Just v -> v }
```

With `ghc -O -c -dverbose-core2core -dsuppress-all -dsuppress-uniques -dinline-check inlPlain Gentle.hs`, the first decision about `inlPlain` comes after `*** Simplifier [Gentle]:` and says `ANSWER = YES`. The result of that pass, under `SimplMode {Phase = initial [Gentle], ...}`, is `usePlain = I# 11#`.

### 5. Note [Eta-expanding at let bindings]: the `myMap = genMap` example is stale

[Simplify/Utils.hs, lines 2198-2214][note-eta]:

```
One useful consequence of not eta-expanding lambdas is this example:
   genMap :: C a => ...
   {-# INLINE genMap #-}
   genMap f xs = ...

   myMap :: D a => ...
   {-# INLINE myMap #-}
   myMap = genMap

Notice that 'genMap' should only inline if applied to two arguments.
In the stable unfolding for myMap we'll have the unfolding
    (\d -> genMap Int (..d..))
We do not want to eta-expand to
    (\d f xs -> genMap Int (..d..) f xs)
because then 'genMap' will inline, and it really shouldn't: at least
as far as the programmer is concerned, it's not applied to two
arguments!
```

Note [Eta-expand stable unfoldings] ([Simplify/Iteration.hs, lines 4940-4958][note-eta2]) says the opposite: "if we know that 'f' has arity N, it seems sensible to eta-expand the stable unfolding to arity N too". `simplStableUnfolding` does this (`eta_expand`, [lines 4930-4938][eta-expand]). Thus HEAD does what the first Note says it does not want. Example:

```haskell
module M where

class C a where
  op :: a -> Int

class C a => D a where
  op2 :: a -> Int

{-# INLINE genMap #-}
genMap :: C a => (Int -> Int) -> [a] -> [Int]
genMap f xs = map (\x -> f (op x)) xs

{-# INLINE myMap #-}
myMap :: D a => (Int -> Int) -> [a] -> [Int]
myMap = genMap
```

With `ghc -O -c M.hs` and `ghc --show-iface M.hi`, `myMap` has `Arity: 3`, and its stable unfolding takes three value arguments and contains the body of `genMap`:

```
   Unfolding: Core: StableUser <1,FalseFalse>
              \ @a
                ($dD['GHC.Internal.Types.Many] :: D a)
                (eta['GHC.Internal.Types.Many] :: GHC.Internal.Types.Int
                                                  -> GHC.Internal.Types.Int)
                (eta1['GHC.Internal.Types.Many] :: [a]) ->
              let {
                $dC :: C a NotJoinPoint [] = $p1D @a $dD
              } in
              GHC.Internal.Base.map
                @a
                @GHC.Internal.Types.Int
                (\ (x['GHC.Internal.Types.Many] :: a) -> eta (op @a $dC x))
                eta1]
```

### 6. Two comments cite a Note that does not exist

[Simplify/Iteration.hs, lines 4962-4963][cite1] and [OccurAnal.hs, line 2230][cite2] cite `Historical-note [Eta-expansion in stable unfoldings]`. No Note in `compiler/` has this name. Commit [6656f0165a][6656f0165a] renamed Note [Eta-expansion in stable unfoldings] to `Historical-note [No eta expansion in stable unfoldings]` and, in the same commit, changed these citations of the old name to `Historical-note [Eta-expansion in stable unfoldings]`. That text is now the "Old note" in Note [Eta expansion in stable unfoldings and rules] ([Simplify/Utils.hs, line 1297][note-old]), which is probably the target. The Notes linter looks for `Note [` only, so it does not find this. A third copy of the citation, in Simplify/Utils.hs, was pointed out in review of !8598 (2022) and is gone since commit [9a3e1f3165][9a3e1f3165]; these two stayed. Related: #27520, about references that renamings broke; this one never resolved.

### 7. A comment in `wantCbvForId` cites a point that its Note no longer has

[Core/Utils.hs, lines 3474-3476][cbv-comment]:

```
  -- If the var is strict already a seq is redundant.
  -- See Note [Which Ids should be strictified] point 4)
  , not (isAbsDmd dmd)
```

Note [Which Ids should be strictified] ([line 3357][cbv-note]) has the points 1), 2), 3) and 5), and no point 4). Commit [c56567ec6b][c56567ec6b] (#26722) removed "4) The argument is already strict." from the Note and added (WIS1) ([lines 3408-3409][cbv-wis1]), which says the opposite of the comment: "You might have thought that we can omit the eval if the argument is used strictly demanded in the body. But you'd be wrong." The test under the comment is the Note's point 3) ([line 3378][cbv-p3]): "The argument is absent."

### 8. Note [Simplifying inside stable unfoldings] names code that does not exist

The Note starts at [Simplify/Utils.hs, line 1437][swu-note]. It has three names that occur nowhere in `compiler/` except in comments.

1. [Lines 1449-1451][swu-occ]: "HENCE we treat any occurrence in a stable unfolding as a multiple occurrence, not a single one; see OccurAnal.addRuleUsage." No function `addRuleUsage` exists. `occAnalUnfolding` does this with `markAllMany` ([OccurAnal.hs, line 2400][occ-unf]), and Note [Occurrences in stable unfoldings and RULES] ([line 2444][occ-note]) explains it. A comment in Specialise.hs ([line 3348][spec-cite]) has the same citation: "C.f. OccAnal.addRuleUsage".
2. [Lines 1481-1490][swu-wrap], "A note about wrappers":

```
It's also important not to inline a worker back into a wrapper.
A wrapper looks like
        wraper = inline_me (\x -> ...worker... )
Normally, the inline_me prevents the worker getting inlined into
the wrapper (initially, the worker's only call site!).  But,
if the wrapper is sure to be called, the strictness analyser will
mark it 'demanded', so when the RHS is simplified, it'll get an ArgOf
continuation.
```

No function `inline_me` exists, and `SimplCont` has no constructor `ArgOf`. The constructor for a strict argument is `StrictArg` ([line 210][strictarg]).

## Proposed improvements or changes

1. `-funfolding-use-threshold`: `:default: 90`.
2. `-g`: until #21471 is fixed, say that `-g` can change the optimised code, and link #21471. #27687 asks for the same kind of statement about the machine code that `-g1` changes.
3. Note [inl_inline and inl_act]: swap `ActiveBefore` and `ActiveAfter` in the two NOINLINE lines.
4. Note [Inlining in gentle mode]: remove (ii) and the sentence about `sm_inline = False`, or delete the Note.
5. Note [Eta-expanding at let bindings]: delete the example, or replace it with a pointer to Note [Eta-expand stable unfoldings].
6. The two citations of `Historical-note [Eta-expansion in stable unfoldings]`: cite Note [Eta expansion in stable unfoldings and rules].
7. `wantCbvForId`: replace the two comment lines with a citation of point 3).
8. Note [Simplifying inside stable unfoldings]: cite `occAnalUnfolding` and Note [Occurrences in stable unfoldings and RULES] in place of `addRuleUsage`, in the Note and in Specialise.hs. Delete the paragraph about wrappers, or write it again for the current worker/wrapper code.

## Environment

* GHC version used (if appropriate): GHC HEAD 10.1.20260918 on x86_64 Linux, for the examples. The text and code are those of master f93d523c (2026-10-15).

[rst-use]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/docs/users_guide/using-optimisation.rst#L1815-1820
[unfold]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Unfold.hs#L103
[a1c24df0e6]: https://gitlab.haskell.org/ghc/ghc/-/commit/a1c24df0e6af4a545921ea783dc54d4ea07f1f03
[rst-g]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/docs/users_guide/debug-info.rst#L72-73
[note-inl]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/Language/Haskell/Syntax/Binds/InlinePragma.hs#L127-129
[parser]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Parser.y#L2862-2867
[rst-noinline]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/docs/users_guide/exts/pragmas.rst#L566-571
[note-gentle]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1324-1327
[note-gentle2]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1345-1346
[active]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Simplify/Inline.hs#L122-133
[gentle]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Driver/Config/Core/Opt/Simplify.hs#L79-85
[initmode]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Driver/Config/Core/Opt/Simplify.hs#L66
[rulelhs]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1208-1213
[ghci]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Driver/Config/Core/Opt/Simplify.hs#L27-31
[note-eta]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Simplify/Utils.hs#L2198-2214
[note-eta2]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4940-4958
[eta-expand]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4930-4938
[cite1]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Simplify/Iteration.hs#L4962-4963
[cite2]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/OccurAnal.hs#L2230
[6656f0165a]: https://gitlab.haskell.org/ghc/ghc/-/commit/6656f0165a30fc2a22208532ba384fc8e2f11b46
[2effe18ab5]: https://gitlab.haskell.org/ghc/ghc/-/commit/2effe18ab51d66474724d38b20e49cc1b8738f60
[9a3e1f3165]: https://gitlab.haskell.org/ghc/ghc/-/commit/9a3e1f316598f7d5072ed4f94437f759352580a5
[cbv-comment]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Utils.hs#L3474-3476
[cbv-note]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Utils.hs#L3357
[cbv-wis1]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Utils.hs#L3408-3409
[cbv-p3]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Utils.hs#L3378
[c56567ec6b]: https://gitlab.haskell.org/ghc/ghc/-/commit/c56567ec6b38ae1021960315bb7efa1c4c347420
[note-old]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1297
[swu-note]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1437
[swu-occ]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1449-1451
[occ-unf]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/OccurAnal.hs#L2400
[occ-note]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/OccurAnal.hs#L2444
[spec-cite]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Specialise.hs#L3348
[swu-wrap]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Simplify/Utils.hs#L1481-1490
[strictarg]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Core/Opt/Simplify/Utils.hs#L210

/label ~bug
/label ~documentation
/label ~"needs triage"
