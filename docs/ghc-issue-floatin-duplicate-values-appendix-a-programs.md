# Appendix A to the GHC !12121 comment: the programs

Appendix to the comment drafted in [`docs/ghc-issue-floatin-duplicate-values-comment.md`](ghc-issue-floatin-duplicate-values-comment.md) for GHC [!12121](https://gitlab.haskell.org/ghc/ghc/-/merge_requests/12121); it is not posted with the comment, which links here. Every program measured in the comment, verbatim, grouped as the comment groups them; the generators that wrote the generated ones; and the scripts that ran them (the build, testsuite, nofib and horde-ad scripts are in [appendix C](ghc-issue-floatin-duplicate-values-appendix-c-scripts-and-results.md)). Unless a script says otherwise, each program is a `Main` module compiled with `ghc -O -fexpose-overloaded-unfoldings Main.hs` and run with `+RTS -s`; the comment's figures are its `bytes allocated`, its `MUT time` and the `.text` size of `Main.o`. The single-module programs allocate the same without `-fexpose-overloaded-unfoldings`.

Contents: [the case](#the-case), [the size family](#the-size-family), [the nested families](#the-nested-families), [the examples of the related tickets](#the-examples-of-the-related-tickets), [the sharing programs](#the-sharing-programs), [across modules](#across-modules).

## The case

The case of the comment ("The case"), as a program, and its argument form `eval k t | check k = case t of ...`; ReproWW.hs is the case with the worker/wrapper split for arity (GHC #19230) written by hand, 291 MB. ReproDiff.hs is a variant whose three alternatives call three different functions (`ev`, `ev2`, `ev3`), so there is nothing for CSE to merge.

#### fmap1s/Repro.hs

```haskell
{-# LANGUAGE LambdaCase #-}
module Main (main) where

data E = Lit Int | Add E E | I1 E [Int] | I2 E [Int] | I3 E [Int]

check :: Int -> Bool
{-# NOINLINE check #-}
check k = k > 0

ev :: Int -> Int -> Int
{-# NOINLINE ev #-}
ev k i = k + i

mapS :: (a -> b) -> [a] -> [b]
{-# INLINE mapS #-}
mapS f l =
  let go [] = []
      go (x : xs) = let y = f x; rest = go xs in y `seq` rest `seq` (y : rest)
  in go l

eval :: Int -> E -> Int
eval k | check k = \case
  Lit n -> n
  Add a b -> eval k a + eval k b
  I1 a ix -> eval k a + sum (mapS (ev k) ix)
  I2 a ix -> eval k a * sum (mapS (ev k) ix)
  I3 a ix -> eval k a - sum (mapS (ev k) ix)
eval _ = const 0

mk :: Int -> E
mk 0 = Lit 0
mk n = Add (mk (n - 1)) (if even n then Lit n else I1 (Lit 1) [1, 2])

main :: IO ()
main = print (sum [eval k (mk 20) | k <- [1 .. 200000]])
```

#### fmap1s/ReproArg.hs

```haskell
{-# LANGUAGE LambdaCase #-}
module Main (main) where

data E = Lit Int | Add E E | I1 E [Int] | I2 E [Int] | I3 E [Int]

check :: Int -> Bool
{-# NOINLINE check #-}
check k = k > 0

ev :: Int -> Int -> Int
{-# NOINLINE ev #-}
ev k i = k + i

mapS :: (a -> b) -> [a] -> [b]
{-# INLINE mapS #-}
mapS f l =
  let go [] = []
      go (x : xs) = let y = f x; rest = go xs in y `seq` rest `seq` (y : rest)
  in go l

eval :: Int -> E -> Int
eval k t | check k = case t of
  Lit n -> n
  Add a b -> eval k a + eval k b
  I1 a ix -> eval k a + sum (mapS (ev k) ix)
  I2 a ix -> eval k a * sum (mapS (ev k) ix)
  I3 a ix -> eval k a - sum (mapS (ev k) ix)
eval _ _ = 0

mk :: Int -> E
mk 0 = Lit 0
mk n = Add (mk (n - 1)) (if even n then Lit n else I1 (Lit 1) [1, 2])

main :: IO ()
main = print (sum [eval k (mk 20) | k <- [1 .. 200000]])
```

#### fill/ReproWW.hs

```haskell
{-# LANGUAGE LambdaCase #-}
module Main (main) where

data E = Lit Int | Add E E | I1 E [Int] | I2 E [Int] | I3 E [Int]

check :: Int -> Bool
{-# NOINLINE check #-}
check k = k > 0

ev :: Int -> Int -> Int
{-# NOINLINE ev #-}
ev k i = k + i

mapS :: (a -> b) -> [a] -> [b]
{-# INLINE mapS #-}
mapS f l =
  let go [] = []
      go (x : xs) = let y = f x; rest = go xs in y `seq` rest `seq` (y : rest)
  in go l

eval :: Int -> E -> Int
{-# INLINE eval #-}
eval k | check k = \t -> weval k t
eval _ = const 0

-- The full-arity worker of a hand-written arity worker/wrapper split.
weval :: Int -> E -> Int
weval k = \case
  Lit n -> n
  Add a b -> eval k a + eval k b
  I1 a ix -> eval k a + sum (mapS (ev k) ix)
  I2 a ix -> eval k a * sum (mapS (ev k) ix)
  I3 a ix -> eval k a - sum (mapS (ev k) ix)

mk :: Int -> E
mk 0 = Lit 0
mk n = Add (mk (n - 1)) (if even n then Lit n else I1 (Lit 1) [1, 2])

main :: IO ()
main = print (sum [eval k (mk 20) | k <- [1 .. 200000]])
```

#### fmap1s/ReproDiff.hs

```haskell
{-# LANGUAGE LambdaCase #-}
module Main (main) where

data E = Lit Int | Add E E | I1 E [Int] | I2 E [Int] | I3 E [Int]

check :: Int -> Bool
{-# NOINLINE check #-}
check k = k > 0

ev, ev2, ev3 :: Int -> Int -> Int
{-# NOINLINE ev #-}
ev k i = k + i
{-# NOINLINE ev2 #-}
ev2 k i = k * i
{-# NOINLINE ev3 #-}
ev3 k i = k - i

mapS :: (a -> b) -> [a] -> [b]
{-# INLINE mapS #-}
mapS f l =
  let go [] = []
      go (x : xs) = let y = f x; rest = go xs in y `seq` rest `seq` (y : rest)
  in go l

eval :: Int -> E -> Int
eval k | check k = \case
  Lit n -> n
  Add a b -> eval k a + eval k b
  I1 a ix -> eval k a + sum (mapS (ev k) ix)
  I2 a ix -> eval k a * sum (mapS (ev2 k) ix)
  I3 a ix -> eval k a - sum (mapS (ev3 k) ix)
eval _ = const 0

mk :: Int -> E
mk 0 = Lit 0
mk n = Add (mk (n - 1)) (if even n then Lit n else I1 (Lit 1) [1, 2])

main :: IO ()
main = print (sum [eval k (mk 20) | k <- [1 .. 200000]])
```

## The size family

Generated by gen5.py (S1 to S5) from a common preamble, run in a directory `adv/size`; `S1_cliff_14` and `S1_cliff_16` come from the same script with its S1 list replaced by `[14, 16]`. The generated programs are not reproduced here. S6 and S7 were written by hand, and S6_user_one_copy_9of10_arg.hs and S7_user_one_copy_2of10_arg.hs are their argument forms. In S1, `S1_cliff_NN` has NN extra levels of `ev k (... + j)`; the sizes in the comment's table are those of the floated `go` as float-in sees it: 100 (NN = 0), 130 (1), 283 (4), 385 (6), 691 (12), 793 (14). sizerun.sh runs the family with the compilers given (suffixes of `ghc-*`).

#### adv/size/gen5.py

```python
# Worst cases for duplicating floated values into case alternatives (dupvalue / dupbudget).
hdr = '''{-# LANGUAGE LambdaCase #-}
module Main (main) where
check :: Int -> Bool
{-# NOINLINE check #-}
check k = k > 0
ev :: Int -> Int -> Int
{-# NOINLINE ev #-}
ev k i = k + i
mapS :: (a -> b) -> [a] -> [b]
{-# INLINE mapS #-}
mapS f l =
  let go [] = []
      go (x : xs) = let y = f x; rest = go xs in y `seq` rest `seq` (y : rest)
  in go l
'''
def calls(n):  # an Int -> Int function of k with n extra NOINLINE calls (grows its size)
    body = "ev k i"
    for j in range(n):
        body = f"ev k ({body} + {j})"
    return body
def prog(name, alts, uses, extra_defs, use_expr, nalts_data):
    cons = " | ".join([f"C{i} E [Int]" for i in range(nalts_data)])
    data = f"data E = Lit Int | Add E E | {cons}\n"
    lines = ["eval :: Int -> E -> Int", "eval k | check k = \\case",
             "  Lit n -> n", "  Add a b -> eval k a + eval k b"]
    for i in range(nalts_data):
        if i in uses:
            lines.append(f"  C{i} a ix -> eval k a + {use_expr(i)}")
        else:
            lines.append(f"  C{i} a ix -> eval k a + length ix")
    lines.append("eval _ = const 0")
    mk = f'''mk :: Int -> E
mk 0 = Lit 0
mk n = Add (mk (n - 1)) (if even n then Lit n else C{min(uses)} (Lit 1) [1, 2])
main :: IO ()
main = print (sum [eval k (mk 20) | k <- [1 .. 200000]])
'''
    open(name + ".hs", "w").write(hdr + extra_defs + data + "\n".join(lines) + "\n" + mk)
# S1: cliff, one local function used in 3 of 6 alternatives, size growing
for n in [0, 1, 2, 3, 4, 6, 8, 12]:
    prog(f"S1_cliff_{n:02d}", None, {0, 1, 2}, "",
         lambda i, n=n: f"sum (mapS (\\i -> {calls(n)}) ix)", 6)
# S2: small and big independent values, both in the same 3 of 6 alternatives
prog("S2_small_and_big", None, {0, 1, 2}, "",
     lambda i: f"sum (mapS (ev k) ix) + sum (mapS (\\i -> {calls(12)}) ix)", 6)
# S3: big captures small (big's body maps the small function)
prog("S3_big_captures_small", None, {0, 1, 2}, "",
     lambda i: f"sum (mapS (\\i -> {calls(12)} + sum (mapS (ev k) [i, i])) ix)", 6)
# S4: wide, small function used in 20 of 21 alternatives (the unused one is the hot one)
prog("S4_wide_20of21", None, set(range(1, 21)), "",
     lambda i: "sum (mapS (ev k) ix)", 21)
# S5: combinatorial, 10 small functions, alternative i uses all but function i
defs5 = "".join(f"ev{j} :: Int -> Int -> Int\n{{-# NOINLINE ev{j} #-}}\nev{j} k i = k + i + {j}\n" for j in range(10))
prog("S5_ten_values_9of10", None, set(range(10)), defs5,
     lambda i: " + ".join(f"sum (mapS (ev{j} k) ix)" for j in range(10) if j != i), 10)
```

#### adv/size/sizerun.sh

```bash
#!/bin/bash
# sizerun.sh "COMPILERS": per program and compiler: bytes allocated, MUT time, Main.o text size, compile seconds.
B=/opt/ghcsrc/_build/stage1/bin
for p in S*.hs; do n=${p%.hs}; line="$n"
  for G in $1; do d=out/$n-$G; rm -rf $d; mkdir -p $d; cp $p $d/Main.hs
    s=$(date +%s.%N)
    (cd $d && $B/ghc-$G -O Main.hs -o m > build.log 2>&1) || { line="$line  $G:BUILD-FAILED"; continue; }
    ct=$(echo "$(date +%s.%N) - $s" | bc)
    (cd $d && ./m +RTS -s > out.txt 2> rts.txt)
    a=$(command grep 'bytes allocated' $d/rts.txt | sed 's/^ *//; s/ bytes.*//')
    txt=$(size -A $d/Main.o | awk '$1==".text"{print $2}')
    line="$line  $G $a text=$txt ct=$(printf %.1f $ct)"
    rm -f $d/m $d/*.o $d/*.hi
  done
  echo "$line"
done
```

#### adv/size/S6_user_one_copy_9of10.hs

```haskell
{-# LANGUAGE LambdaCase #-}
module Main (main) where
check :: Int -> Bool
{-# NOINLINE check #-}
check k = k > 0
ev :: Int -> Int -> Int
{-# NOINLINE ev #-}
ev k i = k + i
mapS :: (a -> b) -> [a] -> [b]
{-# INLINE mapS #-}
mapS f l =
  let go [] = []
      go (x : xs) = let y = f x; rest = go xs in y `seq` rest `seq` (y : rest)
  in go l
data E = Lit Int | Add E E | C0 E [Int] | C1 E [Int] | C2 E [Int] | C3 E [Int] | C4 E [Int] | C5 E [Int] | C6 E [Int] | C7 E [Int] | C8 E [Int] | C9 E [Int]
eval :: Int -> E -> Int
eval k | check k = let bigmap = mapS (\i -> ev k (ev k (ev k (ev k (ev k (ev k (ev k (ev k (ev k (ev k (ev k i + 0) + 1) + 2) + 3) + 4) + 5) + 6) + 7) + 8) + 9)) in \case
  Lit n -> n
  Add a b -> eval k a + eval k b
  C0 a ix -> eval k a + sum (bigmap ix)
  C1 a ix -> eval k a + sum (bigmap ix)
  C2 a ix -> eval k a + sum (bigmap ix)
  C3 a ix -> eval k a + sum (bigmap ix)
  C4 a ix -> eval k a + sum (bigmap ix)
  C5 a ix -> eval k a + sum (bigmap ix)
  C6 a ix -> eval k a + sum (bigmap ix)
  C7 a ix -> eval k a + sum (bigmap ix)
  C8 a ix -> eval k a + sum (bigmap ix)
  C9 a ix -> eval k a + length ix
eval _ = const 0
mk :: Int -> E
mk 0 = Lit 0
mk n = Add (mk (n - 1)) (if even n then Lit n else C0 (Lit 1) [1, 2])
main :: IO ()
main = print (sum [eval k (mk 20) | k <- [1 .. 200000]])
```

#### adv/size/S7_user_one_copy_2of10.hs

```haskell
{-# LANGUAGE LambdaCase #-}
module Main (main) where
check :: Int -> Bool
{-# NOINLINE check #-}
check k = k > 0
ev :: Int -> Int -> Int
{-# NOINLINE ev #-}
ev k i = k + i
mapS :: (a -> b) -> [a] -> [b]
{-# INLINE mapS #-}
mapS f l =
  let go [] = []
      go (x : xs) = let y = f x; rest = go xs in y `seq` rest `seq` (y : rest)
  in go l
data E = Lit Int | Add E E | C0 E [Int] | C1 E [Int] | C2 E [Int] | C3 E [Int] | C4 E [Int] | C5 E [Int] | C6 E [Int] | C7 E [Int] | C8 E [Int] | C9 E [Int]
eval :: Int -> E -> Int
eval k | check k = let bigmap = mapS (\i -> ev k (ev k (ev k (ev k (ev k (ev k (ev k (ev k (ev k (ev k (ev k i + 0) + 1) + 2) + 3) + 4) + 5) + 6) + 7) + 8) + 9)) in \case
  Lit n -> n
  Add a b -> eval k a + eval k b
  C0 a ix -> eval k a + sum (bigmap ix)
  C1 a ix -> eval k a + sum (bigmap ix)
  C2 a ix -> eval k a + length ix
  C3 a ix -> eval k a + length ix
  C4 a ix -> eval k a + length ix
  C5 a ix -> eval k a + length ix
  C6 a ix -> eval k a + length ix
  C7 a ix -> eval k a + length ix
  C8 a ix -> eval k a + length ix
  C9 a ix -> eval k a + length ix
eval _ = const 0
mk :: Int -> E
mk 0 = Lit 0
mk n = Add (mk (n - 1)) (if even n then Lit n else C0 (Lit 1) [1, 2])
main :: IO ()
main = print (sum [eval k (mk 20) | k <- [1 .. 200000]])
```

#### fill/S6_user_one_copy_9of10_arg.hs

```haskell
{-# LANGUAGE LambdaCase #-}
module Main (main) where
check :: Int -> Bool
{-# NOINLINE check #-}
check k = k > 0
ev :: Int -> Int -> Int
{-# NOINLINE ev #-}
ev k i = k + i
mapS :: (a -> b) -> [a] -> [b]
{-# INLINE mapS #-}
mapS f l =
  let go [] = []
      go (x : xs) = let y = f x; rest = go xs in y `seq` rest `seq` (y : rest)
  in go l
data E = Lit Int | Add E E | C0 E [Int] | C1 E [Int] | C2 E [Int] | C3 E [Int] | C4 E [Int] | C5 E [Int] | C6 E [Int] | C7 E [Int] | C8 E [Int] | C9 E [Int]
eval :: Int -> E -> Int
eval k t | check k = let bigmap = mapS (\i -> ev k (ev k (ev k (ev k (ev k (ev k (ev k (ev k (ev k (ev k (ev k i + 0) + 1) + 2) + 3) + 4) + 5) + 6) + 7) + 8) + 9)) in case t of
  Lit n -> n
  Add a b -> eval k a + eval k b
  C0 a ix -> eval k a + sum (bigmap ix)
  C1 a ix -> eval k a + sum (bigmap ix)
  C2 a ix -> eval k a + sum (bigmap ix)
  C3 a ix -> eval k a + sum (bigmap ix)
  C4 a ix -> eval k a + sum (bigmap ix)
  C5 a ix -> eval k a + sum (bigmap ix)
  C6 a ix -> eval k a + sum (bigmap ix)
  C7 a ix -> eval k a + sum (bigmap ix)
  C8 a ix -> eval k a + sum (bigmap ix)
  C9 a ix -> eval k a + length ix
eval _ _ = 0
mk :: Int -> E
mk 0 = Lit 0
mk n = Add (mk (n - 1)) (if even n then Lit n else C0 (Lit 1) [1, 2])
main :: IO ()
main = print (sum [eval k (mk 20) | k <- [1 .. 200000]])
```

#### fill/S7_user_one_copy_2of10_arg.hs

```haskell
{-# LANGUAGE LambdaCase #-}
module Main (main) where
check :: Int -> Bool
{-# NOINLINE check #-}
check k = k > 0
ev :: Int -> Int -> Int
{-# NOINLINE ev #-}
ev k i = k + i
mapS :: (a -> b) -> [a] -> [b]
{-# INLINE mapS #-}
mapS f l =
  let go [] = []
      go (x : xs) = let y = f x; rest = go xs in y `seq` rest `seq` (y : rest)
  in go l
data E = Lit Int | Add E E | C0 E [Int] | C1 E [Int] | C2 E [Int] | C3 E [Int] | C4 E [Int] | C5 E [Int] | C6 E [Int] | C7 E [Int] | C8 E [Int] | C9 E [Int]
eval :: Int -> E -> Int
eval k t | check k = let bigmap = mapS (\i -> ev k (ev k (ev k (ev k (ev k (ev k (ev k (ev k (ev k (ev k (ev k i + 0) + 1) + 2) + 3) + 4) + 5) + 6) + 7) + 8) + 9)) in case t of
  Lit n -> n
  Add a b -> eval k a + eval k b
  C0 a ix -> eval k a + sum (bigmap ix)
  C1 a ix -> eval k a + sum (bigmap ix)
  C2 a ix -> eval k a + length ix
  C3 a ix -> eval k a + length ix
  C4 a ix -> eval k a + length ix
  C5 a ix -> eval k a + length ix
  C6 a ix -> eval k a + length ix
  C7 a ix -> eval k a + length ix
  C8 a ix -> eval k a + length ix
  C9 a ix -> eval k a + length ix
eval _ _ = 0
mk :: Int -> E
mk 0 = Lit 0
mk n = Add (mk (n - 1)) (if even n then Lit n else C0 (Lit 1) [1, 2])
main :: IO ()
main = print (sum [eval k (mk 20) | k <- [1 .. 200000]])
```

## The nested families

N (gen6.py): one local function `g`, of unfolding size 253 (`s04`) or 661 (`s12`), used at every leaf of d levels of three-way cases, two alternatives of each using it. M (gen7.py): a three-way case, two alternatives using `g`, each containing a nested case of three or four alternatives of which two or three use it. The sizes were read off the unfolding guidance of top-level copies of `g`. Both scripts read their preamble from ../size/gen5.py, so they run in a directory `adv/nest` beside `adv/size`; the programs they generate are not reproduced here.

#### adv/nest/gen6.py

```python
# Nested duplication: one local function shared by every leaf of a depth-d if-tree inside one alternative.
# Each case has 3 alternatives, 2 using g (a case all of whose alternatives use g never pushes it),
# so each float-in level sees only 2 using alternatives, so per-level size checks compound to 2^d copies.
import sys
sys.path.insert(0, "../size")
hdr = open("../size/gen5.py").read().split("'''")[1]
def calls(n):
    body = "ev k i"
    for j in range(n):
        body = f"ev k ({body} + {j})"
    return body
def tree(d, lvl=0, idx=0):
    if d == 0:
        return f"sum (mapS g ix) + {idx}"
    return (f"(case sel (k - {lvl}) of {{ 0 -> {tree(d - 1, lvl + 1, 2 * idx)}; "
            f"1 -> {tree(d - 1, lvl + 1, 2 * idx + 1)}; _ -> {idx} }})")
def prog(name, d, n):
    sel = "sel :: Int -> Int\n{-# NOINLINE sel #-}\nsel k = k `mod` 3\n"
    data = sel + "data E = Lit Int | Add E E | C0 E [Int] | C1 E [Int]\n"
    body = f'''eval :: Int -> E -> Int
eval k | check k = \\case
  Lit n -> n
  Add a b -> eval k a + eval k b
  C0 a ix -> eval k a + (let g = \\i -> {calls(n)} in {tree(d)})
  C1 a ix -> eval k a + length ix
eval _ = const 0
mk :: Int -> E
mk 0 = Lit 0
mk n = Add (mk (n - 1)) (if even n then Lit n else C0 (Lit 1) [1, 2])
main :: IO ()
main = print (sum [eval k (mk 20) | k <- [1 .. 200000]])
'''
    open(name + ".hs", "w").write(hdr + data + body)
for n in [4, 12]:
    for d in [1, 2, 4, 6, 8]:
        prog(f"N_s{n:02d}_d{d}", d, n)
```

#### adv/nest/gen7.py

```python
# Mixed fan-out: a shared g, a top case with 3 alternatives (2 use g), each with a nested case of `alts`
# alternatives (`used` use g).  Budget-like policies can pass the top case and stop at the nested one.
hdr = open("../size/gen5.py").read().split("'''")[1]
def calls(n):
    body = "ev k i"
    for j in range(n):
        body = f"ev k ({body} + {j})"
    return body
def inner(lvl, base, alts, used):
    arms = [f"{j} -> sum (mapS g ix) + {base + j}" for j in range(used)]
    arms += [f"{j} -> {base + j}" for j in range(used, alts - 1)]
    arms.append(f"_ -> {base + alts}")
    return f"(case sel{alts} (k - {lvl}) of {{ " + "; ".join(arms) + " })"
def prog(name, n, alts, used):
    sel = "".join(f"sel{a} :: Int -> Int\n{{-# NOINLINE sel{a} #-}}\nsel{a} k = k `mod` {a}\n" for a in sorted({3, alts}))
    top = (f"(case sel3 k of {{ 0 -> {inner(1, 0, alts, used)}; "
           f"1 -> {inner(1, 100, alts, used)}; _ -> 7 }})")
    body = f'''data E = Lit Int | Add E E | C0 E [Int] | C1 E [Int]
eval :: Int -> E -> Int
eval k | check k = \\case
  Lit n -> n
  Add a b -> eval k a + eval k b
  C0 a ix -> eval k a + (let g = \\i -> {calls(n)} in {top})
  C1 a ix -> eval k a + length ix
eval _ = const 0
mk :: Int -> E
mk 0 = Lit 0
mk n = Add (mk (n - 1)) (if even n then Lit n else C0 (Lit 1) [1, 2])
main :: IO ()
main = print (sum [eval k (mk 20) | k <- [1 .. 200000]])
'''
    open(name + ".hs", "w").write(hdr + sel + body)
for n in [4, 12]:
    prog(f"M_s{n:02d}_2of3_3of4", n, 4, 3)
    prog(f"M_s{n:02d}_2of3_2of3", n, 3, 2)
```

#### adv/nest/nestrun.sh

```bash
#!/bin/bash
# sizerun.sh "COMPILERS": per program and compiler: bytes allocated, MUT time, Main.o text size, compile seconds.
B=/opt/ghcsrc/_build/stage1/bin
for p in N*.hs; do n=${p%.hs}; line="$n"
  for G in $1; do d=out/$n-$G; rm -rf $d; mkdir -p $d; cp $p $d/Main.hs
    s=$(date +%s.%N)
    (cd $d && $B/ghc-$G -O Main.hs -o m > build.log 2>&1) || { line="$line  $G:BUILD-FAILED"; continue; }
    ct=$(echo "$(date +%s.%N) - $s" | bc)
    (cd $d && ./m +RTS -s > out.txt 2> rts.txt)
    a=$(command grep 'bytes allocated' $d/rts.txt | sed 's/^ *//; s/ bytes.*//')
    txt=$(size -A $d/Main.o | awk '$1==".text"{print $2}')
    line="$line  $G $a text=$txt ct=$(printf %.1f $ct)"
    rm -f $d/m $d/*.o $d/*.hi
  done
  echo "$line"
done
```

#### adv/nest/mrun.sh

```bash
#!/bin/bash
# sizerun.sh "COMPILERS": per program and compiler: bytes allocated, MUT time, Main.o text size, compile seconds.
B=/opt/ghcsrc/_build/stage1/bin
for p in M*.hs; do n=${p%.hs}; line="$n"
  for G in $1; do d=out/$n-$G; rm -rf $d; mkdir -p $d; cp $p $d/Main.hs
    s=$(date +%s.%N)
    (cd $d && $B/ghc-$G -O Main.hs -o m > build.log 2>&1) || { line="$line  $G:BUILD-FAILED"; continue; }
    ct=$(echo "$(date +%s.%N) - $s" | bc)
    (cd $d && ./m +RTS -s > out.txt 2> rts.txt)
    a=$(command grep 'bytes allocated' $d/rts.txt | sed 's/^ *//; s/ bytes.*//')
    txt=$(size -A $d/Main.o | awk '$1==".text"{print $2}')
    line="$line  $G $a text=$txt ct=$(printf %.1f $ct)"
    rm -f $d/m $d/*.o $d/*.hi
  done
  echo "$line"
done
```

## The examples of the related tickets

R1 to R13: the examples of GHC #24466 (R1, R2, R3, R11, R12), of !12121's own comment (R13), of GHC #2988 (R4, R5, R6), of GHC #24655 (R7; R8 is a construction after the ticket's description), of GHC #19230 (R9) and of GHC #15606 (R10, the same as W3), each with a driver. run.sh prints allocation and mutator time per compiler; the comment's times are medians of 7 interleaved runs of the compiled binaries.

#### adv/related/run.sh

```bash
#!/bin/bash
# run.sh "COMPILERS" FLAGS...: each program with each compiler (suffix of ghc-*); allocation, mutator time, output.
B=/opt/ghcsrc/_build/stage1/bin
CS=$1; shift
for p in *.hs; do n=${p%.hs}; line="$n"; ref=
  for G in $CS; do d=out/$n-$G; rm -rf $d; mkdir -p $d; cp $p $d/Main.hs
    (cd $d && $B/ghc-$G "$@" Main.hs -o m > build.log 2>&1) || { line="$line $G:BUILD-FAILED"; continue; }
    (cd $d && ./m +RTS -s > out.txt 2> rts.txt)
    a=$(command grep 'bytes allocated' $d/rts.txt | sed 's/^ *//; s/ bytes.*//')
    t=$(command grep -E '^ *MUT +time' $d/rts.txt | awk '{print $3}')
    o=$(cat $d/out.txt); [ -z "$ref" ] && ref=$o; [ "$o" = "$ref" ] || line="$line OUTPUT-DIFFERS"
    line="$line  $G $a ${t}s"
  done
  echo "$line"
done
```

#### adv/related/R1_24466_f.hs

```haskell
module Main (main) where
import Data.List (foldl')
-- #24466: a thunk used in two of three alternatives; the default one is hot
f :: Int -> Int -> (Int,Int)
{-# NOINLINE f #-}
f z x = let y = x+1 in
        case z of
          0 -> (y,y)
          1 -> (y,y+1)
          _ -> (99,1)
main :: IO ()
main = print (foldl' (\acc k -> case f (k `mod` 10) k of (a, b) -> acc + a + b) 0 [1 .. 10000000 :: Int])
```

#### adv/related/R2_24466_foo1.hs

```haskell
module Main (main) where
import Data.List (foldl')
-- #24466 foo1: a thunk used by a join point and one alternative (pushing it into both is safe)
data T = A | B | C
expensive :: Int -> Int
{-# NOINLINE expensive #-}
expensive k = sum [1 .. 200 + k `mod` 7]
g :: Int -> Int -> Int
{-# NOINLINE g #-}
g a b = a * 3 + b
foo1 :: Int -> T -> Int
{-# NOINLINE foo1 #-}
foo1 w z = let x = expensive w in
           let j y = g (g x x) (g (g y x) (g x y)) in
           case z of
             A -> j 1
             B -> j 2
             C -> x + 1
tOf :: Int -> T
tOf k = case k `mod` 3 of { 0 -> A; 1 -> B; _ -> C }
main :: IO ()
main = print (foldl' (\acc k -> acc + foo1 k (tOf k)) 0 [1 .. 200000 :: Int])
```

#### adv/related/R3_24466_foo2.hs

```haskell
module Main (main) where
import Data.List (foldl')
-- #24466 foo2: the thunk is also used in the scrutinee, so pushing it into the join point would lose sharing
data T = A | B | C
expensive :: Int -> Int
{-# NOINLINE expensive #-}
expensive k = sum [1 .. 200 + k `mod` 7]
g :: Int -> Int -> Int
{-# NOINLINE g #-}
g a b = a * 3 + b
h :: Int -> Int -> T
{-# NOINLINE h #-}
h x z = case (x + z) `mod` 3 of { 0 -> A; 1 -> B; _ -> C }
foo2 :: Int -> Int -> Int
{-# NOINLINE foo2 #-}
foo2 w z = let x = expensive w in
           let j y = g (g x x) (g (g y x) (g x y)) in
           case h x z of
             A -> j 1
             B -> j 2
             C -> x + 1
main :: IO ()
main = print (foldl' (\acc k -> acc + foo2 k k) 0 [1 .. 200000 :: Int])
```

#### adv/related/R4_2988_cascade.hs

```haskell
module Main (main) where
import Data.List (foldl')
-- #2988: a cascade of bindings used in every alternative
blah :: Int -> Int
{-# NOINLINE blah #-}
blah b = b * 7
f4, g4 :: [Int] -> Int
{-# NOINLINE f4 #-}
f4 = sum
{-# NOINLINE g4 #-}
g4 = length
cascade :: Int -> Bool -> Int
{-# NOINLINE cascade #-}
cascade b c = let x1 = blah b
                  x2 = x1 : []
                  x3 = 1 : x2
                  x4 = 2 : x3
              in case c of
                   True -> f4 x4
                   False -> g4 x4
main :: IO ()
main = print (foldl' (\acc k -> acc + cascade k (even k)) 0 [1 .. 10000000 :: Int])
```

#### adv/related/R5_2988_hotC_fun.hs

```haskell
module Main (main) where
import Data.List (foldl')
-- #2988: x used in two of three alternatives, C hot; x a local function
data T = A | B | C
ev :: Int -> Int -> Int
{-# NOINLINE ev #-}
ev k i = k + i
bar :: Int -> T -> [Int] -> Int
{-# NOINLINE bar #-}
bar w foo l = let x = \i -> ev w (ev w i + 1) in
              case foo of
                A -> sum (map x l)
                B -> sum (map x (reverse l))
                C -> length l
tOf :: Int -> T
tOf k = case k `mod` 10 of { 0 -> A; 1 -> B; _ -> C }
main :: IO ()
main = print (foldl' (\acc k -> acc + bar k (tOf k) [k, k + 1]) 0 [1 .. 2000000 :: Int])
```

#### adv/related/R6_2988_hotC_thunk.hs

```haskell
module Main (main) where
import Data.List (foldl')
-- #2988: x used in two of three alternatives, C hot; x a thunk
data T = A | B | C
blah :: Int -> Int
{-# NOINLINE blah #-}
blah b = b * 7
use :: Int -> Int -> Int
{-# NOINLINE use #-}
use a b = a + b
bar :: Int -> T -> Int
{-# NOINLINE bar #-}
bar w foo = let x = blah w in
            case foo of
              A -> use x 1
              B -> use 2 x
              C -> w
tOf :: Int -> T
tOf k = case k `mod` 10 of { 0 -> A; 1 -> B; _ -> C }
main :: IO ()
main = print (foldl' (\acc k -> acc + bar k (tOf k)) 0 [1 .. 10000000 :: Int])
```

#### adv/related/R7_24655_loop.hs

```haskell
module Main (main) where
-- #24655: (x,x) floated out of the g-loop
f :: Int -> [Int] -> (Int, Int)
{-# NOINLINE f #-}
f x ys = let g [] = (x,x)
             g (_:ys') = g ys'
         in g ys
main :: IO ()
main = print (sum [a + b | k <- [1 .. 1000000 :: Int], let (a, b) = f k (if even k then [] else [1, 2])])
```

#### adv/related/R8_24655_lvl.hs

```haskell
module Main (main) where
import Data.List (foldl')
-- #24655: an inlined function's lambda floats out of \p and is allocated on every call of foo
data T = A | B | C
fI :: Bool -> Int -> Int -> [Int] -> Int
{-# INLINE fI #-}
fI a b c l = sum (zipWith (\x y -> if a then x * y + b else x + y + c) l l)
foo :: Int -> Int -> T -> [Int] -> Int
{-# NOINLINE foo #-}
foo r s t l = case t of
                A -> sum (map (\p -> fI True r s (p : l)) l)
                B -> sum (map (\p -> fI True r s (l ++ [p])) l)
                C -> length l
tOf :: Int -> T
tOf k = case k `mod` 10 of { 0 -> A; 1 -> B; _ -> C }
main :: IO ()
main = print (foldl' (\acc k -> acc + foo k (k + 1) (tOf k) [k, 2]) 0 [1 .. 2000000 :: Int])
```

#### adv/related/R9_19230_e5.hs

```haskell
module Main (main) where
-- #19230: the Call Arity motivator
e5'1 :: (Int -> Bool) -> Int
{-# NOINLINE e5'1 #-}
e5'1 f = sum (filter f [42..2014::Int])
main :: IO ()
main = print (sum [e5'1 (\x -> x `mod` k == 0) | k <- [1 .. 20000]])
```

#### adv/related/R10_15606_W3.hs

```haskell
module Main (main) where
expensive :: Int -> Int
{-# NOINLINE expensive #-}
expensive k = sum [1 .. 2000 + k `mod` 7]
blah :: Int -> Int
{-# NOINLINE blah #-}
blah x = x * 3
h :: Int -> Int -> Int
{-# NOINLINE h #-}
h x y = expensive (x + y)
f :: Int -> Int -> Int
{-# NOINLINE f #-}
f x = let y = blah x in \z -> let v = h x y in v + z
main :: IO ()
main = print (sum [let g = f k in sum (map g [1 .. 1000]) | k <- [1 .. 200]])
```

#### adv/related/R11_24466_strict.hs

```haskell
module Main (main) where
import Data.List (foldl')
-- #24466: "Suppose one RHS was simply `g y y` where `g` is strict"
g :: Int -> Int -> Int
{-# NOINLINE g #-}
g a b = a * b + a
f :: Int -> Int -> (Int,Int)
{-# NOINLINE f #-}
f z x = let y = x+1 in
        case z of
          0 -> (g y y, 0)
          1 -> (y,y+1)
          _ -> (99,1)
main :: IO ()
main = print (foldl' (\acc k -> case f (k `mod` 3) k of (a, b) -> acc + a + b) 0 [1 .. 10000000 :: Int])
```

#### adv/related/R12_24466_foo1_unused.hs

```haskell
module Main (main) where
import Data.List (foldl')
-- #24466 foo1 with a fourth alternative that doesn't use x, so x is a thunk; pushing it into the join point's
-- right-hand side and the C alternative would avoid it on the D path
data T = A | B | C | D
expensive :: Int -> Int
{-# NOINLINE expensive #-}
expensive k = sum [1 .. 200 + k `mod` 7]
g :: Int -> Int -> Int
{-# NOINLINE g #-}
g a b = a * 3 + b
foo1 :: Int -> T -> Int
{-# NOINLINE foo1 #-}
foo1 w z = let x = expensive w in
           let j y = g (g x x) (g (g y x) (g x y)) in
           case z of
             A -> j 1
             B -> j 2
             C -> x + 1
             D -> w
tOf :: Int -> T
tOf k = case k `mod` 10 of { 0 -> A; 1 -> B; 2 -> C; _ -> D }
main :: IO ()
main = print (foldl' (\acc k -> acc + foo1 k (tOf k)) 0 [1 .. 2000000 :: Int])
```

#### adv/related/R13_12121_nested_all.hs

```haskell
module Main (main) where
import Data.List (foldl')
-- !12121's own example: x used in both outer alternatives, but only in one inner alternative of each
f :: Int -> Bool -> Bool -> Maybe Int
{-# NOINLINE f #-}
f y z p = let x = Just y in
          case z of
            True  -> case p of { True  -> x; False -> Nothing }
            False -> case p of { False -> x; True  -> Nothing }
main :: IO ()
main = print (foldl' (\acc k -> case f k (even k) (k `mod` 3 == 0) of { Just v -> acc + v; Nothing -> acc + 1 }) 0 [1 .. 10000000 :: Int])
```

## The sharing programs

The 41 programs written to find a loss of sharing, by any of the fixes: local functions under many-shot lambdas in fused and unfused loops, IO loops and higher-order functions (A to K), called with constants (L1 to L5), heavy inner loops (H2 to H5), partial applications shared across a guard or a cheap case (P1 to P5), and the cases of GHC #15606 and around it (W1 to W16). funtopneg/Neg2.hs, which the runs also include, is a variant of J_neg2.hs. The generators wrote the first four groups (A to K, L, H and P), which are not reproduced here; each writes its programs into the directory it runs in; run.sh (one copy per directory) runs a directory with the compilers given. L5, D, I and P3 are the losses of (SW2) for let-bound values in the comment's table of fixes, W3, W8 and W13 those of the float-out rules, H4 and L4 the programs that pushing bindings every alternative uses improves.

#### run.sh (each directory has a copy)

```bash
#!/bin/bash
# run.sh "COMPILERS" FLAGS...: each program with each compiler (suffix of ghc-*); allocation, mutator time, output.
B=/opt/ghcsrc/_build/stage1/bin
CS=$1; shift
for p in *.hs; do n=${p%.hs}; line="$n"; ref=
  for G in $CS; do d=out/$n-$G; rm -rf $d; mkdir -p $d; cp $p $d/Main.hs
    (cd $d && $B/ghc-$G "$@" Main.hs -o m > build.log 2>&1) || { line="$line $G:BUILD-FAILED"; continue; }
    (cd $d && ./m +RTS -s > out.txt 2> rts.txt)
    a=$(command grep 'bytes allocated' $d/rts.txt | sed 's/^ *//; s/ bytes.*//')
    t=$(command grep -E '^ *MUT +time' $d/rts.txt | awk '{print $3}')
    o=$(cat $d/out.txt); [ -z "$ref" ] && ref=$o; [ "$o" = "$ref" ] || line="$line OUTPUT-DIFFERS"
    line="$line  $G $a ${t}s"
  done
  echo "$line"
done
```

#### adv/gen.py

```python
# Generate adversarial programs: a local recursive function `go` free only in an
# outer variable, used (twice, so it is a real closure) inside a many-shot lambda.
GO = "let { go :: Int -> Int; go 0 = x; go m = go (m - 1) + 1 } in"
progs = {
'A_fusedmap': """f :: Int -> [Int] -> Int
{-# NOINLINE f #-}
f x ys = sum (map (\\y -> %s go (y `mod` 3) * go (y `mod` 5)) ys)
main = print (sum [f k [1 .. 1000] | k <- [1 .. 2000]])""",
'B_comprehension': """f :: Int -> Int -> Int
{-# NOINLINE f #-}
f x n = sum [ %s go (y `mod` 3) * go (y `mod` 5) | y <- [1 .. n] ]
main = print (sum [f k 1000 | k <- [1 .. 2000]])""",
'C_foldl': """import Data.List (foldl')
f :: Int -> [Int] -> Int
{-# NOINLINE f #-}
f x = foldl' (\\acc y -> %s acc + go (y `mod` 3) * go (y `mod` 5)) 0
main = print (sum [f k [1 .. 1000] | k <- [1 .. 2000]])""",
'D_looprec': """f :: Int -> Int -> Int
{-# NOINLINE f #-}
f x n = loop 0 0
  where
    loop :: Int -> Int -> Int
    loop acc i
      | i == n = acc
      | otherwise = %s loop (acc + go (i `mod` 3) * go (i `mod` 5)) (i + 1)
main = print (sum [f k 1000 | k <- [1 .. 2000]])""",
'E_ioloop': """import Control.Monad (forM_)
import Data.IORef
f :: Int -> Int -> IO Int
{-# NOINLINE f #-}
f x n = do
  r <- newIORef 0
  forM_ [1 .. n] $ \\y -> %s modifyIORef' r (+ go (y `mod` 3) * go (y `mod` 5))
  readIORef r
main = do { s <- mapM (\\k -> f k 1000) [1 .. 2000]; print (sum s) }""",
'F_hof': """applyAll :: (Int -> Int) -> [Int] -> Int
{-# NOINLINE applyAll #-}
applyAll g = sum . map g
f :: Int -> [Int] -> Int
{-# NOINLINE f #-}
f x = applyAll (\\y -> %s go (y `mod` 3) * go (y `mod` 5))
main = print (sum [f k [1 .. 1000] | k <- [1 .. 2000]])""",
'G_sharedpap': """expensive :: Int -> Int
{-# NOINLINE expensive #-}
expensive k = sum [1 .. k `mod` 7]
f :: Int -> Int -> Int
{-# NOINLINE f #-}
f x0 = let x = expensive x0 in \\y -> %s go (y `mod` 3) * go (y `mod` 5)
main = print (sum [sum (map (f k) [1 .. 1000]) | k <- [1 .. 2000]])""",
'H_nested': """f :: Int -> [Int] -> Int
{-# NOINLINE f #-}
f x ys = sum (map (\\y -> sum (map (\\z -> %s go (z `mod` 3) * go (y `mod` 5)) [1 .. 10])) ys)
main = print (sum [f k [1 .. 100] | k <- [1 .. 2000]])""",
'I_onebranch': """f :: Int -> [Int] -> [Int]
{-# NOINLINE f #-}
f x = map (\\y -> if even y then (%s go (y `mod` 3) * go (y `mod` 5)) else y)
main = print (sum (concat [f k [1 .. 1000] | k <- [1 .. 2000]]))""",
'J_neg2': """f :: Int -> [Int] -> [Int]
{-# NOINLINE f #-}
f x = map (\\y -> %s go (y `mod` 3) * go (y `mod` 5))
main = print (sum (concat [f k [1 .. 1000] | k <- [1 .. 2000]]))""",
'K_zipwith': """f :: Int -> [Int] -> [Int] -> Int
{-# NOINLINE f #-}
f x as bs = sum (zipWith (\\a b -> %s go (a `mod` 3) * go (b `mod` 5)) as bs)
main = print (sum [f k [1 .. 1000] [2 .. 1001] | k <- [1 .. 2000]])""",
}
for name, body in progs.items():
    open(name + '.hs', 'w').write('module Main (main) where\n' + (body % GO) + '\n')
```

#### adv/const/gen2.py

```python
GO = "let { go :: Int -> Int; go 0 = x; go m = go (m - 1) + 1 } in"
progs = {
'L1_const_single': """f :: Int -> [Int] -> Int
{-# NOINLINE f #-}
f x ys = sum (map (\\y -> %s go 1000 + y) ys)
main = print (sum [f k [1 .. 1000] | k <- [1 .. 200]])""",
'L2_const_nested': """f :: Int -> [Int] -> Int
{-# NOINLINE f #-}
f x ys = sum (map (\\y -> sum (map (\\z -> %s go 1000 + y * z) [1 .. 10])) ys)
main = print (sum [f k [1 .. 100] | k <- [1 .. 200]])""",
'L3_const_twouses': """f :: Int -> [Int] -> Int
{-# NOINLINE f #-}
f x ys = sum (map (\\y -> %s go 1000 + go (y `mod` 7)) ys)
main = print (sum [f k [1 .. 1000] | k <- [1 .. 200]])""",
'L4_const_nested_twouses': """f :: Int -> [Int] -> Int
{-# NOINLINE f #-}
f x ys = sum (map (\\y -> sum (map (\\z -> %s go 1000 + go (z `mod` 7) * y) [1 .. 10])) ys)
main = print (sum [f k [1 .. 100] | k <- [1 .. 200]])""",
'L5_const_loop': """f :: Int -> Int -> Int
{-# NOINLINE f #-}
f x n = loop 0 0
  where
    loop :: Int -> Int -> Int
    loop acc i
      | i == n = acc
      | otherwise = %s loop (acc + go 1000 + go (i `mod` 7)) (i + 1)
main = print (sum [f k 1000 | k <- [1 .. 200]])""",
}
for name, body in progs.items():
    open(name + '.hs', 'w').write('module Main (main) where\n' + (body % GO) + '\n')
```

#### adv/heavy/gen3.py

```python
GO = "let { go :: Int -> Int; go 0 = x; go m = go (m - 1) + 1 } in"
progs = {
'H2_heavy': """f :: Int -> [Int] -> Int
{-# NOINLINE f #-}
f x ys = sum (map (\\y -> sum (map (\\z -> %s go (1000 + z `mod` 3) * go (y `mod` 5)) [1 .. 10])) ys)
main = print (sum [f k [1 .. 100] | k <- [1 .. 200]])""",
'H3_heavy_inner_only': """f :: Int -> [Int] -> Int
{-# NOINLINE f #-}
f x ys = sum (map (\\y -> sum (map (\\z -> %s go (1000 + z `mod` 3) * y) [1 .. 10])) ys)
main = print (sum [f k [1 .. 100] | k <- [1 .. 200]])""",
'H4_depth3': """f :: Int -> [Int] -> Int
{-# NOINLINE f #-}
f x ys = sum (map (\\y -> sum (map (\\w -> sum (map (\\z -> %s go (100 + z `mod` 3) * go (w `mod` 5) + y) [1 .. 5])) [1 .. 5])) ys)
main = print (sum [f k [1 .. 100] | k <- [1 .. 200]])""",
'H5_last_const': """f :: Int -> [Int] -> Int
{-# NOINLINE f #-}
f x ys = sum (map (\\y -> sum (map (\\z -> %s go (2000 * (z `div` 10))) [1 .. 10]) + y) ys)
main = print (sum [f k [1 .. 100] | k <- [1 .. 200]])""",
}
for name, body in progs.items():
    open(name + '.hs', 'w').write('module Main (main) where\n' + (body % GO) + '\n')
```

#### adv/spine/gen4.py

```python
GO = "let { go :: Int -> Int; go 0 = x; go m = go (m - 1) + 1 } in"
EXP = """expensive :: Int -> Int
{-# NOINLINE expensive #-}
expensive k = sum [1 .. k `mod` 7]
"""
progs = {
'P1_pap_heavy': EXP + """f :: Int -> Int -> Int
{-# NOINLINE f #-}
f x0 = let x = expensive x0 in \\y -> %s go (100 + y `mod` 3) * go (y `mod` 5)
main = print (sum [sum (map (f k) [1 .. 1000]) | k <- [1 .. 200]])""",
'P2_pap_innerloop': EXP + """f :: Int -> Int -> Int
{-# NOINLINE f #-}
f x0 = let x = expensive x0 in \\y -> %s sum (map (\\z -> go (1000 + z `mod` 3) * y) [1 .. 10])
main = print (sum [sum (map (f k) [1 .. 100]) | k <- [1 .. 200]])""",
'P3_eval_pap': """data E = Lit Int | Add E E | I1 E [Int] | I2 E [Int] | I3 E [Int]
check :: Int -> Bool
{-# NOINLINE check #-}
check k = k > 0
eval :: Int -> E -> Int
eval x | check x = \\case
  Lit n -> n
  Add a b -> eval x a + eval x b
  I1 a ix -> eval x a + sum (map (\\i -> %s go i) ix)
  I2 a ix -> eval x a * sum (map (\\i -> %s go (i + 1)) ix)
  I3 a ix -> eval x a - sum (map (\\i -> %s go (i + 2)) ix)
eval _ = const 0
mk :: Int -> E
mk 0 = Lit 0
mk n = Add (mk (n - 1)) (if even n then Lit n else I1 (Lit 1) [1, 2])
main = print (sum [sum (map (eval k) [mk 5, mk 6, mk 7, mk 8]) | k <- [1 .. 50000]])""",
'P4_guard_shared': """check :: Int -> Bool
{-# NOINLINE check #-}
check k = k > 0
f :: Int -> Int -> Int
{-# NOINLINE f #-}
f x | check x = \\y -> %s go (y `mod` 3) * go (y `mod` 5)
f _ = const 0
main = print (sum [sum (map (f k) [1 .. 1000]) | k <- [1 .. 2000]])""",
'P5_guard_shared_heavy': """check :: Int -> Bool
{-# NOINLINE check #-}
check k = k > 0
f :: Int -> Int -> Int
{-# NOINLINE f #-}
f x | check x = \\y -> %s sum (map (\\z -> go (1000 + z `mod` 3) * y) [1 .. 10])
f _ = const 0
main = print (sum [sum (map (f k) [1 .. 100]) | k <- [1 .. 200]])""",
}
for name, body in progs.items():
    n = body.count('%s')
    open(name + '.hs', 'w').write('{-# LANGUAGE LambdaCase #-}\nmodule Main (main) where\n' + (body % tuple([GO] * n)) + '\n')
```

#### adv/t15606/W1_cheapcase_pap.hs

```haskell
module Main (main) where
expensive :: Int -> Int
{-# NOINLINE expensive #-}
expensive k = sum [1 .. 2000 + k `mod` 7]
f :: (Int, Int) -> Int -> Int
{-# NOINLINE f #-}
f p = case p of (a, b) -> \y -> expensive a + b + y
main :: IO ()
main = print (sum [let g = f (k, 1) in sum (map g [1 .. 1000]) | k <- [1 .. 200]])
```

#### adv/t15606/W2_cheapcase_sat.hs

```haskell
module Main (main) where
expensive :: Int -> Int
{-# NOINLINE expensive #-}
expensive k = sum [1 .. 2000 + k `mod` 7]
f :: (Int, Int) -> Int -> Int
{-# NOINLINE f #-}
f p = case p of (a, b) -> \y -> expensive a + b + y
main :: IO ()
main = print (sum [sum [f (k, 1) y | y <- [1 .. 1000]] | k <- [1 .. 200]])
```

#### adv/t15606/W3_spj_blahcall_pap.hs

```haskell
module Main (main) where
expensive :: Int -> Int
{-# NOINLINE expensive #-}
expensive k = sum [1 .. 2000 + k `mod` 7]
blah :: Int -> Int
{-# NOINLINE blah #-}
blah x = x * 3
h :: Int -> Int -> Int
{-# NOINLINE h #-}
h x y = expensive (x + y)
f :: Int -> Int -> Int
{-# NOINLINE f #-}
f x = let y = blah x in \z -> let v = h x y in v + z
main :: IO ()
main = print (sum [let g = f k in sum (map g [1 .. 1000]) | k <- [1 .. 200]])
```

#### adv/t15606/W4_spj_blahjust_pap.hs

```haskell
module Main (main) where
expensive :: Int -> Int
{-# NOINLINE expensive #-}
expensive k = sum [1 .. 2000 + k `mod` 7]
h :: Int -> Maybe Int -> Int
{-# NOINLINE h #-}
h x y = expensive (x + maybe 0 id y)
f :: Int -> Int -> Int
{-# NOINLINE f #-}
f x = let y = Just x in \z -> let v = h x y in v + z
main :: IO ()
main = print (sum [let g = f k in sum (map g [1 .. 1000]) | k <- [1 .. 200]])
```

#### adv/t15606/W5_newlevel_letlam.hs

```haskell
module Main (main) where
expensive :: Int -> Int
{-# NOINLINE expensive #-}
expensive k = sum [1 .. 2000 + k `mod` 7]
f :: Int -> Int
{-# NOINLINE f #-}
f x = let v = \y -> expensive x + y in sum (map v [1 .. 1000])
main :: IO ()
main = print (sum [f k | k <- [1 .. 200]])
```

#### adv/t15606/W6_newlevel_arg.hs

```haskell
module Main (main) where
expensive :: Int -> Int
{-# NOINLINE expensive #-}
expensive k = sum [1 .. 2000 + k `mod` 7]
f :: Int -> Int
{-# NOINLINE f #-}
f x = sum (map (\y -> expensive x + y) [1 .. 1000])
main :: IO ()
main = print (sum [f k | k <- [1 .. 200]])
```

#### adv/t15606/W7_userlet_pap.hs

```haskell
module Main (main) where
expensive :: Int -> Int
{-# NOINLINE expensive #-}
expensive k = sum [1 .. 2000 + k `mod` 7]
f :: (Int, Int) -> Int -> Int
{-# NOINLINE f #-}
f p = case p of (a, b) -> let t = expensive a in \y -> t + b + y
main :: IO ()
main = print (sum [let g = f (k, 1) in sum (map g [1 .. 1000]) | k <- [1 .. 200]])
```

#### adv/t15606/W8_cheapguard_pap.hs

```haskell
module Main (main) where
expensive :: Int -> Int
{-# NOINLINE expensive #-}
expensive k = sum [1 .. 2000 + k `mod` 7]
f :: Int -> Int -> Int
{-# NOINLINE f #-}
f x | x > 0 = \y -> expensive x + y
f _ = id
main :: IO ()
main = print (sum [let g = f k in sum (map g [1 .. 1000]) | k <- [1 .. 200]])
```

#### adv/t15606/W9_cheapcase_pap_local.hs

```haskell
module Main (main) where
expensive :: Int -> Int
{-# NOINLINE expensive #-}
expensive k = sum [1 .. 2000 + k `mod` 7]
f :: (Int, Int) -> Int -> Int
{-# NOINLINE f #-}
f p = case p of (a, b) -> \y -> let { go :: Int -> Int; go 0 = b; go m = go (m - 1) + 1 } in go (2000 + a `mod` 7) + y
main :: IO ()
main = print (sum [let g = f (k, 1) in sum (map g [1 .. 1000]) | k <- [1 .. 200]])
```

#### adv/t15606/W11_value_closure_pap.hs

```haskell
module Main (main) where
expensive :: Int -> Int
{-# NOINLINE expensive #-}
expensive k = sum [1 .. 2000 + k `mod` 7]
app :: (Int -> Int) -> Int -> Int
{-# NOINLINE app #-}
app g y = g y + g (y + 1)
f :: (Int, Int) -> Int -> Int
{-# NOINLINE f #-}
f p = case p of (a, b) -> \y -> let g = \z -> a * z + b in app g y
main :: IO ()
main = print (sum [let h = f (k, 1) in sum (map h [1 .. 1000]) | k <- [1 .. 2000]])
```

#### adv/t15606/W12_value_con_expensive_field_pap.hs

```haskell
module Main (main) where
expensive :: Int -> Int
{-# NOINLINE expensive #-}
expensive k = sum [1 .. 2000 + k `mod` 7]
f :: (Int, Int) -> Int -> Int
{-# NOINLINE f #-}
f p = case p of (a, b) -> \y -> let q = (expensive a, b) in fst q + snd q + y
main :: IO ()
main = print (sum [let h = f (k, 1) in sum (map h [1 .. 1000]) | k <- [1 .. 200]])
```

#### adv/t15606/W13_cheapguard_localconst_pap.hs

```haskell
module Main (main) where
expensive :: Int -> Int
{-# NOINLINE expensive #-}
expensive k = sum [1 .. 2000 + k `mod` 7]
f :: Int -> Int -> Int
{-# NOINLINE f #-}
f x | x > 0 = \y -> let { go :: Int -> Int; go 0 = x; go m = go (m - 1) + 1 } in go 1000 + go (y `mod` 3) + y
f _ = id
main :: IO ()
main = print (sum [let g = f k in sum (map g [1 .. 1000]) | k <- [1 .. 200]])
```

#### adv/t15606/W14_cheapcase_localconst_pap.hs

```haskell
module Main (main) where
expensive :: Int -> Int
{-# NOINLINE expensive #-}
expensive k = sum [1 .. 2000 + k `mod` 7]
f :: (Int, Int) -> Int -> Int
{-# NOINLINE f #-}
f p = case p of (a, b) -> \y -> let { go :: Int -> Int; go 0 = a; go m = go (m - 1) + b } in go 1000 + go (y `mod` 3) + y
main :: IO ()
main = print (sum [let g = f (k, 1) in sum (map g [1 .. 1000]) | k <- [1 .. 200]])
```

#### adv/t15606/W15_value_dep_loop_alts.hs

```haskell
module Main (main) where
expensive :: Int -> Int
{-# NOINLINE expensive #-}
expensive k = sum [1 .. 2000 + k `mod` 7]
app :: (Int -> Int) -> Int -> Int
{-# NOINLINE app #-}
app g y = g y + g (y + 1)
f :: Int -> Int -> Int
{-# NOINLINE f #-}
f x n = go 0 0
  where
    go :: Int -> Int -> Int
    go acc i
      | i == n = acc
      | otherwise = let h = \z -> z * x + i in case i `mod` 3 of
          0 -> go (acc + app h i) (i + 1)
          1 -> go (acc + app h (i + 1)) (i + 1)
          _ -> go (acc + 1) (i + 1)
main :: IO ()
main = print (sum [f k 10000 | k <- [1 .. 200]])
```

#### adv/t15606/W16_value_inv_joinloop_alts.hs

```haskell
module Main (main) where
expensive :: Int -> Int
{-# NOINLINE expensive #-}
expensive k = sum [1 .. 2000 + k `mod` 7]
app :: (Int -> Int) -> Int -> Int
{-# NOINLINE app #-}
app g y = g y + g (y + 1)
f :: Int -> Int -> Int
{-# NOINLINE f #-}
f x n = let h = \z -> z * x + n in
  let go :: Int -> Int -> Int
      go acc i
        | i == n = acc
        | otherwise = case i `mod` 3 of
            0 -> go (acc + app h i) (i + 1)
            1 -> go (acc + app h (i + 1)) (i + 1)
            _ -> go (acc + 1) (i + 1)
  in go 0 0
main :: IO ()
main = print (sum [f k 10000 | k <- [1 .. 200]])
```

#### funtopneg/Neg2.hs

```haskell
module Main (main) where

-- A local recursive function free only in x, called twice (so a real closure,
-- not a join point) inside a many-shot lambda: floating it out of \y saves one
-- closure per list element.
f :: Int -> [Int] -> [Int]
{-# NOINLINE f #-}
f x = map (\y -> let go :: Int -> Int
                     go 0 = x
                     go n = go (n - 1) + 1
                 in go (y `mod` 3) * go (y `mod` 5))

main :: IO ()
main = print (sum (concat [f k [1 .. 1000] | k <- [1 .. 2000]]))
```

## Across modules

The case's function in another module (fmap2m: Lib.hs with the `\case`, LibArg.hs with the argument form, Main.hs the caller), the same with a dictionary passed to `ev` (fmapev), and an interpreter with a class context specialised by its caller in another module (fmaprepro: Ox.hs mirrors the ox-arrays index types; run.sh builds the importer-specialised variant GD and the defining-module `SPECIALISE` variant G2G; Lib-ww.hs has the worker/wrapper split for arity written by hand and Lib-arg.hs the argument form).

#### fmap2m/run.sh

```bash
#!/bin/bash
# run.sh GHC LABEL FLAGS...: \case form vs argument form
G=$1; L=$2; shift 2
for form in Lib LibArg; do d=o-$L-$form; rm -rf $d; mkdir $d; cp $form.hs $d/Lib.hs; cp Main.hs $d/
  (cd $d && $G "$@" Main.hs -o r > build.log 2>&1) || { echo "$d build failed"; continue; }
  printf '%-8s %-7s %-40s %s\n' "$L" "$form" "$*" "$(cd $d && ./r +RTS -s 2>&1 | command grep 'bytes allocated' | sed 's/^ *//; s/ bytes.*//')"
done
```

#### fmap2m/Lib.hs

```haskell
{-# LANGUAGE LambdaCase, DataKinds, GADTs, KindSignatures, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes #-}
module Lib (Sp(..), KnownS, E(..), interp) where

data Sp = F | P
data SSp (s :: Sp) where
  SF :: SSp 'F
  SP :: SSp 'P
class KnownS (s :: Sp) where sing :: SSp s
instance KnownS 'F where sing = SF
instance KnownS 'P where sing = SP

data Dict where Dict :: Dict
mkDict :: SSp s -> Dict
{-# NOINLINE mkDict #-}
mkDict SF = Dict
mkDict SP = Dict

data E (s :: Sp) = Lit Int | Var | Add (E s) (E s)
  | I1 (E s) [E 'P] | I2 (E s) [E 'P] | I3 (E s) [E 'P]

mapS :: (a -> b) -> [a] -> [b]
{-# INLINE mapS #-}
mapS f l =
  let go [] = []
      go (x : xs) = let y = f x; rest = go xs in y `seq` rest `seq` (y : rest)
  in go l

interp :: forall s a. (Num a, KnownS s) => a -> E s -> a
{-# INLINABLE interp #-}
interp env | Dict <- mkDict (sing @s) = \case
  Lit n -> fromIntegral n
  Var -> env
  Add a b -> interp env a + interp env b
  I1 a ix -> interp env a + sum (mapS (interp env) ix)
  I2 a ix -> interp env a * sum (mapS (interp env) ix)
  I3 a ix -> interp env a - sum (mapS (interp env) ix)
```

#### fmap2m/LibArg.hs

```haskell
{-# LANGUAGE LambdaCase, DataKinds, GADTs, KindSignatures, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes #-}
module Lib (Sp(..), KnownS, E(..), interp) where

data Sp = F | P
data SSp (s :: Sp) where
  SF :: SSp 'F
  SP :: SSp 'P
class KnownS (s :: Sp) where sing :: SSp s
instance KnownS 'F where sing = SF
instance KnownS 'P where sing = SP

data Dict where Dict :: Dict
mkDict :: SSp s -> Dict
{-# NOINLINE mkDict #-}
mkDict SF = Dict
mkDict SP = Dict

data E (s :: Sp) = Lit Int | Var | Add (E s) (E s)
  | I1 (E s) [E 'P] | I2 (E s) [E 'P] | I3 (E s) [E 'P]

mapS :: (a -> b) -> [a] -> [b]
{-# INLINE mapS #-}
mapS f l =
  let go [] = []
      go (x : xs) = let y = f x; rest = go xs in y `seq` rest `seq` (y : rest)
  in go l

interp :: forall s a. (Num a, KnownS s) => a -> E s -> a
{-# INLINABLE interp #-}
interp env t | Dict <- mkDict (sing @s) = case t of
  Lit n -> fromIntegral n
  Var -> env
  Add a b -> interp env a + interp env b
  I1 a ix -> interp env a + sum (mapS (interp env) ix)
  I2 a ix -> interp env a * sum (mapS (interp env) ix)
  I3 a ix -> interp env a - sum (mapS (interp env) ix)
```

#### fmap2m/Main.hs

```haskell
{-# LANGUAGE DataKinds #-}
import Lib

mk :: Int -> E 'F
mk 0 = Var
mk n = Add (mk (n - 1)) (if even n then Lit n else I1 (Lit 1) [Var, Lit 2])

run :: KnownS s => Int -> E s -> Int
{-# NOINLINE run #-}
run = interp

main :: IO ()
main = print (sum [run k (mk 20) | k <- [1 .. 200000]])
```

#### fmapev/run.sh

```bash
#!/bin/bash
# run.sh GHC LABEL FLAGS...: \case form vs argument form
G=$1; L=$2; shift 2
for form in Lib LibArg; do d=o-$L-$form; rm -rf $d; mkdir $d; cp $form.hs $d/Lib.hs; cp Main.hs $d/
  (cd $d && $G "$@" Main.hs -o r > build.log 2>&1) || { echo "$d build failed"; continue; }
  printf '%-8s %-7s %-40s %s\n' "$L" "$form" "$*" "$(cd $d && ./r +RTS -s 2>&1 | command grep 'bytes allocated' | sed 's/^ *//; s/ bytes.*//')"
done
```

#### fmapev/Lib.hs

```haskell
{-# LANGUAGE LambdaCase, DataKinds, GADTs, KindSignatures, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes #-}
module Lib (Sp(..), KnownS, E(..), interp) where

data Sp = F | P
data SSp (s :: Sp) where
  SF :: SSp 'F
  SP :: SSp 'P
class KnownS (s :: Sp) where sing :: SSp s
instance KnownS 'F where sing = SF
instance KnownS 'P where sing = SP

data Dict where Dict :: Dict

ev :: Num a => a -> Int -> a
{-# NOINLINE ev #-}
ev env i = env + fromIntegral i

mkDict :: SSp s -> Dict
{-# NOINLINE mkDict #-}
mkDict SF = Dict
mkDict SP = Dict

data E (s :: Sp) = Lit Int | Var | Add (E s) (E s)
  | I1 (E s) [Int] | I2 (E s) [Int] | I3 (E s) [Int]

mapS :: (a -> b) -> [a] -> [b]
{-# INLINE mapS #-}
mapS f l =
  let go [] = []
      go (x : xs) = let y = f x; rest = go xs in y `seq` rest `seq` (y : rest)
  in go l

interp :: forall s a. (Num a, KnownS s) => a -> E s -> a
{-# INLINABLE interp #-}
interp env | Dict <- mkDict (sing @s) = \case
  Lit n -> fromIntegral n
  Var -> env
  Add a b -> interp env a + interp env b
  I1 a ix -> interp env a + sum (mapS (ev env) ix)
  I2 a ix -> interp env a * sum (mapS (ev env) ix)
  I3 a ix -> interp env a - sum (mapS (ev env) ix)
```

#### fmapev/LibArg.hs

```haskell
{-# LANGUAGE LambdaCase, DataKinds, GADTs, KindSignatures, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes #-}
module Lib (Sp(..), KnownS, E(..), interp) where

data Sp = F | P
data SSp (s :: Sp) where
  SF :: SSp 'F
  SP :: SSp 'P
class KnownS (s :: Sp) where sing :: SSp s
instance KnownS 'F where sing = SF
instance KnownS 'P where sing = SP

data Dict where Dict :: Dict

ev :: Num a => a -> Int -> a
{-# NOINLINE ev #-}
ev env i = env + fromIntegral i

mkDict :: SSp s -> Dict
{-# NOINLINE mkDict #-}
mkDict SF = Dict
mkDict SP = Dict

data E (s :: Sp) = Lit Int | Var | Add (E s) (E s)
  | I1 (E s) [Int] | I2 (E s) [Int] | I3 (E s) [Int]

mapS :: (a -> b) -> [a] -> [b]
{-# INLINE mapS #-}
mapS f l =
  let go [] = []
      go (x : xs) = let y = f x; rest = go xs in y `seq` rest `seq` (y : rest)
  in go l

interp :: forall s a. (Num a, KnownS s) => a -> E s -> a
{-# INLINABLE interp #-}
interp env t | Dict <- mkDict (sing @s) = case t of
  Lit n -> fromIntegral n
  Var -> env
  Add a b -> interp env a + interp env b
  I1 a ix -> interp env a + sum (mapS (ev env) ix)
  I2 a ix -> interp env a * sum (mapS (ev env) ix)
  I3 a ix -> interp env a - sum (mapS (ev env) ix)
```

#### fmapev/Main.hs

```haskell
{-# LANGUAGE DataKinds #-}
import Lib

mk :: Int -> E 'F
mk 0 = Var
mk n = Add (mk (n - 1)) (if even n then Lit n else I1 (Lit 1) [1, 2])

run :: KnownS s => Int -> E s -> Int
{-# NOINLINE run #-}
run = interp

main :: IO ()
main = print (sum [run k (mk 20) | k <- [1 .. 200000]])
```

#### fmaprepro/run.sh

```bash
#!/bin/bash
# variant name, phase, spec line
G=${GHC:-/opt/ghcsrc/_build/stage1/bin/ghc-guard}
F="-O -fexpose-overloaded-unfoldings -fspecialise-aggressively -fdicts-cheap -fkeep-auto-rules"
v() { d=$1; rm -rf $d; mkdir -p $d; sed -e "s/PHASE/$2/" -e "s/^SPEC$/$3/" Lib.hs > $d/Lib.hs; cp Main.hs Ox.hs $d/;
  (cd $d && $G $F -ddump-stg-final -ddump-to-file -dsuppress-uniques Main.hs -o Main > build.log 2>&1) || { echo "$d build failed"; return; }
  echo "== $d: $(cd $d && ./Main +RTS -s 2>&1 | command grep -E 'bytes allocated' | sed 's/^ *//')"; }
v GD "" ""
v G2G "[1]" "{-# SPECIALISE interp :: KnownS s => Int -> E s -> Int #-}"
```

#### fmaprepro/Ox.hs

```haskell
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Ox (ListX(..), IxX(..), IxS(..)) where

newtype ListX i = ListX [i]

instance Functor ListX where
  {-# INLINE fmap #-}
  fmap f (ListX l) =
    let fmap' [] = []
        fmap' (x : xs) = let y = f x
                             rest = fmap' xs
                         in y `seq` rest `seq` (y : rest)
    in ListX (fmap' l)

newtype IxX i = IxX (ListX i) deriving Functor
newtype IxS i = IxS (IxX i) deriving Functor
```

#### fmaprepro/Lib.hs

The lines `PHASE` and `SPEC` are placeholders that run.sh replaces with `sed` for each variant.

```
{-# LANGUAGE LambdaCase, BangPatterns, DataKinds, GADTs, KindSignatures, RankNTypes, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes #-}
module Lib (E(..), Sp(..), KnownS(..), SSp(..), interp) where

import Ox

data Sp = F | P
data SSp (s :: Sp) where
  SF :: SSp 'F
  SP :: SSp 'P
class KnownS (s :: Sp) where sing :: SSp s
instance KnownS 'F where sing = SF
instance KnownS 'P where sing = SP

data Dict where Dict :: Dict
mkDict :: SSp s -> Dict
{-# NOINLINE mkDict #-}
mkDict SF = Dict
mkDict SP = Dict

data E (s :: Sp) = Lit Int | Var | Add (E s) (E s)
  | I1 (E s) (IxS (E 'P)) | I2 (E s) (IxS (E 'P)) | I3 (E s) (IxS (E 'P))

sumL :: Num a => IxS a -> a
{-# INLINE sumL #-}
sumL (IxS (IxX (ListX l))) = sum l

interp :: forall s a. (Num a, KnownS s) => a -> E s -> a
{-# INLINABLE PHASE interp #-}
SPEC
interp !env | Dict <- mkDict (sing @s) = \case
  Lit n -> fromIntegral n
  Var -> env
  Add a b -> interp env a + interp env b
  I1 a ix -> interp env a + sumL (interp env <$> ix)
  I2 a ix -> interp env a * sumL (interp env <$> ix)
  I3 a ix -> interp env a - sumL (interp env <$> ix)
```

#### fmaprepro/Main.hs

```haskell
{-# LANGUAGE DataKinds #-}
import Lib
import Ox
mk :: Int -> E 'F
mk 0 = Var
mk n = Add (mk (n - 1)) (if even n then Lit n else I1 (Lit 1) (IxS (IxX (ListX [Var, Lit 2]))))
go :: KnownS s => Int -> E s -> Int
{-# NOINLINE go #-}
go k e = interp k e
main :: IO ()
main = print (sum [go k (mk 20) | k <- [1 .. 200000]])
```

#### fmaprepro/Lib-arg.hs

The lines `PHASE` and `SPEC` are placeholders that run.sh replaces with `sed` for each variant.

```
{-# LANGUAGE LambdaCase, BangPatterns, DataKinds, GADTs, KindSignatures, RankNTypes, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes #-}
module Lib (E(..), Sp(..), KnownS(..), SSp(..), interp) where

import Ox

data Sp = F | P
data SSp (s :: Sp) where
  SF :: SSp 'F
  SP :: SSp 'P
class KnownS (s :: Sp) where sing :: SSp s
instance KnownS 'F where sing = SF
instance KnownS 'P where sing = SP

data Dict where Dict :: Dict
mkDict :: SSp s -> Dict
{-# NOINLINE mkDict #-}
mkDict SF = Dict
mkDict SP = Dict

data E (s :: Sp) = Lit Int | Var | Add (E s) (E s)
  | I1 (E s) (IxS (E 'P)) | I2 (E s) (IxS (E 'P)) | I3 (E s) (IxS (E 'P))

sumL :: Num a => IxS a -> a
{-# INLINE sumL #-}
sumL (IxS (IxX (ListX l))) = sum l

interp :: forall s a. (Num a, KnownS s) => a -> E s -> a
{-# INLINABLE PHASE interp #-}
SPEC
interp !env t | Dict <- mkDict (sing @s) = case t of
  Lit n -> fromIntegral n
  Var -> env
  Add a b -> interp env a + interp env b
  I1 a ix -> interp env a + sumL (interp env <$> ix)
  I2 a ix -> interp env a * sumL (interp env <$> ix)
  I3 a ix -> interp env a - sumL (interp env <$> ix)
```

#### fmaprepro/Lib-ww.hs

The lines `PHASE` and `SPEC` are placeholders that run.sh replaces with `sed` for each variant.

```
{-# LANGUAGE LambdaCase, BangPatterns, DataKinds, GADTs, KindSignatures, RankNTypes, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes #-}
module Lib (E(..), Sp(..), KnownS(..), SSp(..), interp, winterp) where

import Ox

data Sp = F | P
data SSp (s :: Sp) where
  SF :: SSp 'F
  SP :: SSp 'P
class KnownS (s :: Sp) where sing :: SSp s
instance KnownS 'F where sing = SF
instance KnownS 'P where sing = SP

data Dict where Dict :: Dict
mkDict :: SSp s -> Dict
{-# NOINLINE mkDict #-}
mkDict SF = Dict
mkDict SP = Dict

data E (s :: Sp) = Lit Int | Var | Add (E s) (E s)
  | I1 (E s) (IxS (E 'P)) | I2 (E s) (IxS (E 'P)) | I3 (E s) (IxS (E 'P))

sumL :: Num a => IxS a -> a
{-# INLINE sumL #-}
sumL (IxS (IxX (ListX l))) = sum l

interp :: forall s a. (Num a, KnownS s) => a -> E s -> a
{-# INLINE interp #-}
interp !env | Dict <- mkDict (sing @s) = \t -> winterp env t

-- The full-arity worker of the arity worker/wrapper split (GHC #19230):
-- recursive calls go through the inlined wrapper above.
winterp :: forall s a. (Num a, KnownS s) => a -> E s -> a
{-# INLINABLE PHASE winterp #-}
SPEC
winterp !env = \case
  Lit n -> fromIntegral n
  Var -> env
  Add a b -> interp env a + interp env b
  I1 a ix -> interp env a + sumL (interp env <$> ix)
  I2 a ix -> interp env a * sumL (interp env <$> ix)
  I3 a ix -> interp env a - sumL (interp env <$> ix)
```
