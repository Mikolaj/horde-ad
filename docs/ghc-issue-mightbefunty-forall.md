# GHC issue: since ce01ccb625, `mightBeFunTy` does not look through foralls and newtypes, so a polymorphic constant is evaluated with `stg_ap_0_fast`

Filed as GHC [#27979](https://gitlab.haskell.org/ghc/ghc/-/work_items/27979) on 2026-10-17; the text from "## Summary" down is the filed body, in the tracker's bug template. Title: **Regression: `mightBeFunTy` no longer looks through foralls and newtypes, so a polymorphic thunk is evaluated with `stg_ap_0_fast`**. Verified with GHC HEAD 10.1.20260918 and 9.14.1, the cost program run from the files as shown here. The 9.14.2-rc2 and 10.0.1-alpha1 copies of `mightBeFunTy` were read at those tags; no 9.14.2 final tag exists on 2026-10-17. A tracker search of 2026-10-16 found no report and no open MR that changes the line; a search on 2026-10-17 of the issues filed since then found none. The cited lines were checked at master f93d523c. The prose is ASD-STE100 Simplified Technical English. Open: the suggested fix is checked only on the predicate (a copy of `mightBeFunTy` linked against HEAD's `ghc` library), not in a GHC build or the testsuite; the effects on the other callers of `mightBeFunTy` are read, not measured.

## Summary

On HEAD, `mightBeFunTy` returns True for a type `forall a. T a`, where `T` is a data type, and for a newtype over a data type. GHC 9.14.1 returns False for these types. So a thunk of such a type gets `might_be_function= True` in its `LambdaFormInfo` ([`mkLFThunk`][lfthunk]), also in the interface file, and a binder of such a type gets `LFUnknown True` ([`mkLFArgument`][lfarg]). Code that evaluates such a value, unless tag inference knows that it is tagged, takes a `SlowCall` branch of `getCallMethod` (for a thunk [lines 561-563][slowcall], for a binder [line 605][slowcall2]) and calls `stg_ap_0_fast`. 9.14.1 tests the pointer tag and enters the closure. In the second example below, this costs 8 instructions a use.

The change came with commit ce01ccb625, "Don't drop ticks around variables of type `IO ()`" (!16123, for #27225). Before it, `mightBeFunTy` tested `tyConAppTyCon_maybe (unwrapType ty)`. Now it tests `tyConAppTyCon_maybe (unwrap_type ty)` ([`GHC.Types.RepType`, line 737][mbft]). The comment on the helper says "Use 'unwrapType' to look through casts, newtypes and foralls." But `unwrap_type` calls `unwrapType` only in its guard for unary classes, and its last equation returns the type unchanged ([lines 749-759][unwrap]):

```
          | otherwise
          = ty
```

Thus, for `forall a. Box a`, `tyConAppTyCon_maybe` gets the type with its forall and returns `Nothing`. For a newtype `Age`, it gets `Age`, which is not a boxed data type constructor. In both cases `mightBeFunTy` returns True. 9.14.2-rc2 and 10.0.1-alpha1 have the same code.

Suggested fix, not tested in a GHC build: `| otherwise = unwrapType ty`. A copy of `mightBeFunTy` with this change, linked against HEAD's `ghc` library, returns False for `forall a. Maybe a` (HEAD: True), and True for `forall a. a` and `Int -> Int`. The other callers of `mightBeFunTy` get the same changed answers: `mkSelectorLFInfo` and `mkApLFInfo` in `GHC.StgToCmm.Closure`, `mkTick` in `GHC.Core.Utils`, `GHC.Core.LateCC`, `GHC.StgToJS.Apply` and `GHC.StgToCmm.Expr`.

## Steps to reproduce

1. Save the module below as `Repro.hs`.
2. `ghc -O -no-link -ddump-cmm -ddump-to-file Repro.hs`
3. `grep -n stg_ap_0_fast Repro.dump-cmm`
4. `ghc --show-iface Repro.hi`, and look at the `LambdaFormInfo` of `cafP` and `cafM`.

```haskell
module Repro (poly, mono, elemAge, elemInt) where

data Box a = Box Int [a]

newtype Age = Age Int

mkBox :: Int -> Box a
mkBox n = Box n []
{-# NOINLINE mkBox #-}

cafP :: Box a  -- a polymorphic constant, a thunk
cafP = mkBox 1

cafM :: Box ()  -- the same, monomorphic
cafM = mkBox 2

poly, mono :: Int -> Int
poly i = case (cafP :: Box ()) of Box n _ -> n + i
mono i = case cafM of Box n _ -> n + i

elemAge :: [Age] -> Int  -- the element's type a newtype over a data type
elemAge (Age n : _) = n
elemAge [] = 0

elemInt :: [Int] -> Int
elemInt (n : _) = n
elemInt [] = 0
```

### Results

On HEAD, step 3 finds two calls. The first is in `elemAge`, the second in `poly`:

```
284:           call stg_ap_0_fast(R1) args: 8, res: 0, upd: 8;
609:           call stg_ap_0_fast(R1) returns to cHa, args: 8, res: 8, upd: 8;
```

`mono` evaluates `cafM` with `if (R1 & 7 != 0) goto cHm; else goto cHn;`, and `elemInt` enters its element with `call (I64![R1])(R1) args: 8, res: 0, upd: 8;`. On 9.14.1, step 3 finds nothing: `poly` tests the tag of `cafP`, and `elemAge` enters its element directly, as `mono` and `elemInt` do.

Step 4, with the white space shortened:

```
HEAD:   cafP :: Box a [LambdaFormInfo: LFThunk (updatable=True might_be_function= True)
HEAD:   cafM :: Box () [LambdaFormInfo: LFThunk (updatable=True might_be_function= False)
9.14.1: cafP :: Box a [LambdaFormInfo: LFThunk (updatable=True might_be_function= False)
```

The cost, for a constant in another module. `Lib.hs`:

```haskell
module Lib (V (..), emptyC, emptyM) where

import Data.Word (Word8)
import Unsafe.Coerce (unsafeCoerce)

data V a = V !Int [a]

{-# NOINLINE emptyC #-}
emptyC :: V a
emptyC = unsafeCoerce (V 0 [] :: V Word8)

{-# NOINLINE emptyM #-}
emptyM :: V Double
emptyM = unsafeCoerce (V 0 [] :: V Word8)
```

`Main.hs`:

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import Lib
import System.Environment (getArgs)

{-# NOINLINE lenC #-}
lenC :: Int -> Int
lenC k = case (emptyC :: V Double) of V n _ -> n + k

{-# NOINLINE lenM #-}
lenM :: Int -> Int
lenM k = case emptyM of V n _ -> n + k

main :: IO ()
main = do
  [which, rs] <- getArgs
  let len = if which == "cast" then lenC else lenM
      go :: Int -> Int -> Int
      go 0 !acc = acc
      go r !acc = go (r - 1) (acc + len r)
  print (go (read rs) 0)
```

With `ghc -O Lib.hs Main.hs -o Main`, `perf stat -e instructions:u ./Main cast N` and `./Main mono N`, at N = 10^7 and 2 * 10^7, differenced:

```
instructions a call of len     HEAD    9.14.1
cast (emptyC :: V a)           74.65   66.65
mono (emptyM :: V Double)      66.65   66.65
```

On HEAD, `Lib.hi` gives `emptyC` `might_be_function= True`, and, with `-fforce-recomp -ddump-asm` added, `$wlenC` does `leaq Lib.emptyC_closure(%rip),%rbx` and then `jmp stg_ap_0_fast`.

## Expected behavior

As in 9.14.1: `mightBeFunTy` returns False for `forall a. T a` and for a newtype over a data type, and GHC evaluates such a thunk with a tag test and a direct entry.

## Environment

* GHC version used: HEAD 10.1.20260918 (`wip/T27737` at 6913545fd3, on master e2d5702699, with local simplifier patches; Types/RepType.hs, StgToCmm/Closure.hs and StgToCmm/Expr.hs are the same as at master f93d523c) shows the problem; 9.14.1 does not.

Optional:

* Operating System: Linux
* System Architecture: x86_64

[lfthunk]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/StgToCmm/Closure.hs#L225-231
[lfarg]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/StgToCmm/Closure.hs#L200-204
[slowcall]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/StgToCmm/Closure.hs#L561-563
[slowcall2]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/StgToCmm/Closure.hs#L605
[mbft]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Types/RepType.hs#L737
[unwrap]: https://gitlab.haskell.org/ghc/ghc/-/blob/f93d523cf3f28e8a7fe8b8bfef8037f42d47aefc/compiler/GHC/Types/RepType.hs#L749-759

/label ~"T::bug"
/label ~"regression"
/label ~"code generation"
/label ~"runtime perf"
/label ~"needs triage"
