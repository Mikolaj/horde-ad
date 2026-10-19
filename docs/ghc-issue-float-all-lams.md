# GHC issue: `-ffloat-all-lams` floats no function with free variables to top level, because `destLevel` has no case for `floatOutLambdas = Nothing`

Filed as GHC [#27990](https://gitlab.haskell.org/ghc/ghc/-/work_items/27990); the text from "## Summary" down is the body as drafted, in the tracker's bug template. Title: **`-ffloat-all-lams` does the same as no flag: `destLevel` treats `floatOutLambdas = Nothing` as `Just 0`**. Verified on 2026-10-19 with GHC HEAD 10.1.20260918, 9.14.1, 9.12.4, 9.10.3 and 9.8.4, all with the same effect, from the file as shown here. Found in a probe of a loop of orthotope: `-ffloat-lam-args=8` floated the loop out of each of its three call sites, and `-ffloat-all-lams` floated none. A tracker search of 2026-10-19 for the two flag names and for `floatOutLambdas` and `floatLamArgs` found no report. The nearest items are GHC [#14985](https://gitlab.haskell.org/ghc/ghc/-/work_items/14985) and GHC [#9358](https://gitlab.haskell.org/ghc/ghc/-/work_items/9358), about flags that the users' guide does not describe; GHC [#5945](https://gitlab.haskell.org/ghc/ghc/-/work_items/5945), closed, about lambda lifting; and GHC [#23449](https://gitlab.haskell.org/ghc/ghc/-/work_items/23449), open and with no comments, which asks how `floatOutLambdas = Just 0` differs from `floatToTopLevelOnly`. The cited lines were checked at master 3d326d7d28; in the HEAD build, SetLevels.hs, Session.hs and Pipeline.hs differ from master, but not in the cited lines. Open: the possible fix is not tested.

## Summary

`-ffloat-all-lams` has the same effect as no flag. It sets `floatOutLambdas` to `Nothing` for the second float-out pass, and `-ffloat-lam-args=N` sets it to `Just N` ([Session.hs, lines 1863-1866][flags], [Pipeline.hs, lines 272-277][pipeline]). `FloatOutSwitches` documents the field ([Monad.hs, lines 78-84][switches]):

```
  { floatOutLambdas   :: Maybe Int  -- ^ Just n <=> float lambdas to top level, if
                                    -- doing so will abstract over n or fewer
                                    -- value variables
                                    -- Nothing <=> float all lambdas to top level,
                                    --             regardless of how many free variables
                                    -- Just 0 is the vanilla case: float a lambda
                                    --    iff it has no free vars
```

Apart from the pretty printer, the only reader of the field is `destLevel` ([SetLevels.hs, lines 1618-1622][destlevel]), through `floatLams`:

```haskell
  | Just n_args <- floatLams env
  , n_args > 0  -- n=0 case handled uniformly by the 'otherwise' case
  , is_function
  , countFreeIds fvs <= n_args
  = as_far_as_poss  -- Send functions to top level; see
```

This guard has no case for `Nothing`, so `Nothing` falls through to the `otherwise` case, like `Just 0`, and `-ffloat-all-lams` can float less than `-ffloat-lam-args=N`, as the example below shows for N = 2. Only the flag sets `Nothing`.

Before a0f0420865 ("Some infrastruture for lambda-lifting", 2010), `floatLams` was a `Bool`, and the guard `floatLams env && is_function` sent all functions to top level. That commit changed the type to `Maybe Int` and wrote the guard above, with no case for `Nothing`. The comment on `Nothing` was added the same day, in c177e43f99.

A possible fix, not tested: give `Nothing` its documented meaning.

```haskell
  | is_function
  , case floatLams env of
      Nothing     -> True
      Just n_args -> n_args > 0 && countFreeIds fvs <= n_args
  = as_far_as_poss
```

Neither flag is in the users' guide ([expected-undocumented-flags.txt, lines 45-46][undoc]). If no user needs `-ffloat-all-lams`, another fix is to remove the flag and make `floatOutLambdas` and `floatLamArgs` (in `DynFlags`) plain `Int`s.

## Steps to reproduce

`Repro.hs`:

```haskell
module Repro (f) where

-- g is a function with two free variables, a and b.
f :: Int -> Int -> [Int] -> [Int]
f a b xs = map g xs
  where
    {-# NOINLINE g #-}
    g x = x * a + b
```

Compile it three times, into three output directories:

```
ghc -O -ffloat-lam-args=2 -ddump-float-out -ddump-simpl -ddump-to-file -dsuppress-uniques -dsuppress-idinfo -outputdir lam2 -c Repro.hs
ghc -O -ffloat-all-lams -ddump-float-out -ddump-simpl -ddump-to-file -dsuppress-uniques -dsuppress-idinfo -outputdir all -c Repro.hs
ghc -O -ddump-float-out -ddump-simpl -ddump-to-file -dsuppress-uniques -dsuppress-idinfo -outputdir none -c Repro.hs
```

### Results

The listings are from 9.14.1. In `lam2/Repro.dump-float-out`, the second float-out pass floats `$wg`, the worker of `g`, to top level as `poly_$wg`, abstracted over `a` and `b`:

```
==================== Float out(FOS {Lam = Just 2,
               Consts = True,
               JoinsToTop = True,
               OverSatApps = True}) ====================
...
poly_$wg
  :: Int -> Int -> GHC.Internal.Prim.Int# -> GHC.Internal.Prim.Int#
poly_$wg
  = \ (a :: Int) (b :: Int) (ww :: GHC.Internal.Prim.Int#) ->
      case a of { GHC.Internal.Types.I# y ->
      case b of { GHC.Internal.Types.I# y ->
      GHC.Internal.Prim.+# (GHC.Internal.Prim.*# ww y) y
      }
      }
```

In `lam2/Repro.dump-simpl` the worker is still at top level, as `Repro.f1`, and `f` passes it `a` and `b`:

```
f = \ (a :: Int) (b :: Int) (xs :: [Int]) ->
      map
        @Int
        @Int
        (\ (x :: Int) ->
           case x of { GHC.Internal.Types.I# ww ->
           case Repro.f1 a b ww of ww1 { __DEFAULT ->
           GHC.Internal.Types.I# ww1
           }
           })
        xs
```

In `all/Repro.dump-float-out`, the header of the second pass has `Lam = Nothing`, and the pass floats nothing. In `all/Repro.dump-simpl`, the worker stays local:

```
f = \ (a :: Int) (b :: Int) (xs :: [Int]) ->
      let {
        $wg :: GHC.Internal.Prim.Int# -> GHC.Internal.Prim.Int#
        $wg
          = \ (ww :: GHC.Internal.Prim.Int#) ->
              case a of { GHC.Internal.Types.I# y ->
              case b of { GHC.Internal.Types.I# y1 ->
              GHC.Internal.Prim.+# (GHC.Internal.Prim.*# ww y) y1
              }
              } } in
      map
```

Each dump file in `all` is the same as its counterpart in `none`, except for the time stamps and for `Lam = Nothing` where `none` has `Lam = Just 0`, in the two lines that name the second pass.

## Expected behavior

With `-ffloat-all-lams`, the second float-out pass floats the worker of `g` to top level, as it does with `-ffloat-lam-args=2`.

## Environment

* GHC version used: HEAD 10.1.20260918 (`wip/T27737` at 6913545fd3, on master e2d5702699, with local simplifier patches; the cited lines are the same as at master 3d326d7d28), 9.14.1, 9.12.4, 9.10.3 and 9.8.4, all with the same effect.

Optional:

* Operating System: Linux
* System Architecture: x86_64

[switches]: https://gitlab.haskell.org/ghc/ghc/-/blob/3d326d7d28ee5d51c9ae42ae1baf1c5a4500d185/compiler/GHC/Core/Opt/Monad.hs#L78-84
[flags]: https://gitlab.haskell.org/ghc/ghc/-/blob/3d326d7d28ee5d51c9ae42ae1baf1c5a4500d185/compiler/GHC/Driver/Session.hs#L1863-1866
[pipeline]: https://gitlab.haskell.org/ghc/ghc/-/blob/3d326d7d28ee5d51c9ae42ae1baf1c5a4500d185/compiler/GHC/Core/Opt/Pipeline.hs#L272-277
[destlevel]: https://gitlab.haskell.org/ghc/ghc/-/blob/3d326d7d28ee5d51c9ae42ae1baf1c5a4500d185/compiler/GHC/Core/Opt/SetLevels.hs#L1618-1622
[undoc]: https://gitlab.haskell.org/ghc/ghc/-/blob/3d326d7d28ee5d51c9ae42ae1baf1c5a4500d185/docs/users_guide/expected-undocumented-flags.txt#L45-46

/label ~"T::bug"
/label ~"float-out"
/label ~"needs triage"
