# GHC issue: with `-fno-full-laziness -fno-cse`, Float inwards moves a jump to an exit join point under a case binder of the same unique, and the program prints an empty line or crashes

Filed as GHC [#27886](https://gitlab.haskell.org/ghc/ghc/-/work_items/27886) on 2026-10-02; the text from "## Summary" down is the filed body, in the tracker's bug template. Title: **With `-fno-full-laziness -fno-cse`, Float inwards moves a jump to an exit join point into the scope of a case binder that Exitification gave the same unique: wrong output on 9.6 to 9.12, `internal error: stg_ap_p_ret` on 9.14 and HEAD**. Verified on 2026-10-02 on HEAD 10.1.20260918 (checkout `6913545fd3`), 9.14.1, 9.12.4, 9.10.3, 9.8.4 and 9.6.7. Found in orthotope's unreleased branch `pr-mikolaj-toVectorListT` as pushed, at `1c0dcac`: in a client module with both flags, the branch's ordered conversions of a dense array returned nothing on 9.6.7 to 9.12.4 and stopped with `internal error: stg_ap_n_ret` on 9.14.1 and HEAD, where the 0.1.8.0 release was correct under both flags on 9.12.4; the reproducer is the loop of that branch's `INLINE` `routeT`, cut down. The tracker was searched on 2026-10-02 for `Exitification`, `exit join point`, `Float inwards`, `FloatIn`, `shadowing`, `name capture`, `case binder shadow`, `duplicate unique`, `Mismatch in type between binder and occurrence`, `stg_ap_n_ret`, `stg_ap_p_ret`, `fno-cse` and `fno-full-laziness`, and the open issues labelled float-in, join points and incorrect runtime result were read through, with no duplicate found; GHC [#22662](https://gitlab.haskell.org/ghc/ghc/-/work_items/22662) is the nearest.

## Summary

With `-O -fno-full-laziness -fno-cse`, the program below prints an empty line on GHC 9.6.7, 9.8.4, 9.10.3 and 9.12.4, and stops with `internal error: stg_ap_p_ret` on 9.14.1 and HEAD. It should print `1`. With `-dcore-lint`, all six report `*** Core Lint errors : in result of Float inwards ***`, and 9.12.4 names the binder:

```
    Mismatch in type between binder and occurrence
    Binder: wild_X1F :: Int
    Occurrence: exit_X1F :: Int# -> [Box] -> String
      Before subst: Int# -> [Box] -> String
```

The documentation of `unsafePerformIO` names both flags among the precautions for code that uses it. The reproducer is cut down from an array library's `INLINE` conversion of an array to a list, which went wrong the same way in a client module with both flags.

The dumps below are from HEAD, with `-O -dverbose-core2core -dsuppress-idinfo -dsuppress-module-prefixes -dsuppress-type-applications -dsuppress-coercions -dsuppress-type-signatures`. After Exitification, `main` is:

```
main_s15m
  = \ eta_aNV ->
      hPutStr2
        stdout
        (join { $j_s1Gq n_aUF = itos n_aUF [] } in
         case xs1 of {
           [] -> jump $j_s1Gq 7#;
           : x_avV xs_avW ->
             join {
               exit_X1F ww_s1GG acc_s1GI
                 = case acc_s1GI of {
                     [] -> jump $j_s1Gq ww_s1GG;
                     : ds1_a159 ds2_a15a -> jump $j_s1Gq 7#
                   } } in
             joinrec {
               $wgo_s1GL ww_s1GG acc_s1GI ds_s1GJ ds_s1GK
                 = join { fail_s1Gp ds_DNE = jump exit_X1F ww_s1GG acc_s1GI } in
                   case ds_s1GJ of {
                     [] -> jump fail_s1Gp (##);
                     : y'_aw1 xs'_aw2 ->
                       case ds_s1GK of {
                         [] -> jump fail_s1Gp (##);
                         : ds_DNA ys'_aw3 ->
                           case y'_aw1 of { I# ww_XNC ->
                           jump $wgo_s1GL ww_XNC (: (Box ww_s1GG) acc_s1GI) xs'_aw2 ys'_aw3
                           }
                       }
                   }; } in
             case x_avV of { I# ww_s1GG ->
             jump $wgo_s1GL ww_s1GG [] xs_avW ys1
             }
         })
        True
        eta_aNV
```

The dead case binder of `case x_avV` at the bottom, which `-dppr-debug` shows, is `wild_X1F`, and so is that of `case y'_aw1` inside `$wgo_s1GL`; both had that name before Exitification ran. Exitification gave the new exit join point the same unique: [`mkExitJoinId`](https://gitlab.haskell.org/ghc/ghc/-/blob/c35096f55daffde5d17ca878a965345db410abf5/compiler/GHC/Core/Opt/Exitify.hs#L261-273) picks it with `uniqAway`, avoiding the variables in scope at the `joinrec`, those bound on the way to the exit and the earlier exit join points, and neither `wild_X1F` is among them: one is in the body of the `joinrec`, the other off the way to the exit. The program is still correct here, as no occurrence of `exit_X1F` is in the scope of a `wild_X1F`.

With both flags, Float inwards is the next pass; by default, full laziness (`Float out`) and CSE (`Common sub-expression`) run between the two. It moves the `joinrec` into the alternative of `case x_avV` (excerpt):

```
             case x_avV of { I# ww_s1GG ->
             joinrec {
               $wgo_s1GL ww_s1GG acc_s1GI ds_s1GJ ds_s1GK
                 = join { fail_s1Gp ds_DNE = jump exit_X1F ww_s1GG acc_s1GI } in
```

Now the jump to `exit_X1F` in `fail_s1Gp` is in the scope of `wild_X1F :: Int`, which is the Lint error. The simplifier that runs next replaces the jump with `I# ww_s1GG`, the case binder's value, applied to the two arguments, and drops `exit_X1F`; in Tidy Core:

```
                 = join { fail_s1Gp ds2_DNE = I# ww_s1GG ww1_X1G acc_s1GI } in
```

[Note [Shadowing and name capture]](https://gitlab.haskell.org/ghc/ghc/-/blob/c35096f55daffde5d17ca878a965345db410abf5/compiler/GHC/Core/Opt/FloatIn.hs#L320-350) in FloatIn, added for #22662, says that a binding site abandons float-in for the floating bindings that mention its binders, the case binder included. Reading the code, the guard does not do that for this float: `sepBindsByDropPoint` seeds the used-here set with the binders, and [`used_here`](https://gitlab.haskell.org/ghc/ghc/-/blob/c35096f55daffde5d17ca878a965345db410abf5/compiler/GHC/Core/Opt/FloatIn.hs#L803) intersects that set with each floater's own binders, not with its free variables. So a floater that binds a name the case also binds is held back, but `$wgo_s1GL`, which only mentions `exit_X1F`, is not. We have not built a compiler with a change.

A possible fix, not tested: Exitification could also avoid the binders in the right-hand sides and body of the `joinrec`, or FloatIn could hold back a floater whose free variables meet the binders of the site.

### Related

- #22662: a FloatIn capture under shadowing, closed in 2023 by the change that added Note [Shadowing and name capture].
- #15110: Exitification abstracting over shadowed variables, closed in 2018.
- #21685: CSE mishandling an exit join point and a `$j` of the same unique, closed in 2022.

## Steps to reproduce

```haskell
{-# OPTIONS_GHC -fno-full-laziness -fno-cse #-}
module Main (main) where

data Box = Box !Int

f :: [Int] -> [Int] -> Int
f (x : xs) ys = go x [] xs ys
  where
    go :: Int -> [Box] -> [Int] -> [Int] -> Int
    go !y acc (y' : xs') (_ : ys') = go y' (Box y : acc) xs' ys'
    go !y acc _ _ = if null acc then y else 7
f _ _ = 7

xs1, ys1 :: [Int]
xs1 = [1]
{-# NOINLINE xs1 #-}
ys1 = [10]
{-# NOINLINE ys1 #-}

main :: IO ()
main = print (f xs1 ys1)
```

Save it as `Repro.hs`:

```
ghc -O Repro.hs -o Repro && ./Repro
ghc -O -dcore-lint -fforce-recomp Repro.hs -o Repro
```

| compiler | `./Repro` | `-dcore-lint` |
|---|---|---|
| HEAD 10.1.20260918 | `Repro: internal error: stg_ap_p_ret`, exit 134 | error in result of Float inwards |
| 9.14.1 | `Repro: internal error: stg_ap_p_ret`, exit 134 | error in result of Float inwards |
| 9.12.4 | an empty line, exit 0 | error in result of Float inwards |
| 9.10.3 | an empty line, exit 0 | error in result of Float inwards |
| 9.8.4 | an empty line, exit 0 | error in result of Float inwards |
| 9.6.7 | an empty line, exit 0 | error in result of Float inwards |

Without the `OPTIONS_GHC` line, or with either flag alone, the program prints `1` (checked on HEAD, 9.12.4 and 9.6.7). With both flags, `-fno-exitification` or `-fno-float-in` also gives `1`, and `-O2` gives the same results as `-O` (checked on HEAD and 9.12.4).

## Expected behavior

The program prints `1`, and Core Lint reports no error.

## Environment

* GHC version used: HEAD 10.1.20260918 (commit 6913545fd3), 9.14.1, 9.12.4, 9.10.3, 9.8.4, 9.6.7

Optional:

* Operating System: Linux
* System Architecture: x86_64

/label ~"T::bug"
/label ~"needs triage"
