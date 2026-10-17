# GHC issue comment: a nullary join point's lost return information costs a thunk under a lazy constructor, 40 bytes a call

Posted 2026-10-17 as a comment on GHC [#27841](https://gitlab.haskell.org/ghc/ghc/-/work_items/27841), "TagInference: nullary join points are treated like thunks" (open), whose fix is GHC [!16719](https://gitlab.haskell.org/ghc/ghc/-/merge_requests/16719) (open, assigned to marge-bot on 2026-10-14); this file stays as the record of the comment, the text from "Here is a program" down being the body as posted. Verified with GHC HEAD 10.1.20260918 and 9.14.1, which give the same STG and bytes, from the files as shown here. Read on 2026-10-17: the issue's description and all its notes, and all notes of !16719; none mentions an allocated thunk or bytes, and the MR's test `inferTags005` checks only the tag signature. horde-ad has no record of #27841. The prose is ASD-STE100 Simplified Technical English. Open: whether !16719 removes the thunk, since no one built the MR.

Here is a program where this costs an allocation, not only an evaluation, at plain `-O`. `convert` returns `T`, a constructor with strict fields, and worker/wrapper gives it a worker `$wconvert` that returns an unboxed triple. When the join point `big` has no arguments, `$wconvert` gets `TagSig: <TagFun[TagDunno]>` (`ghc --show-iface Lib.hi`, on HEAD). Then `wrap`, which puts the result under a lazy `Just`, allocates a thunk that evaluates two fields and then builds `T`. When `big` takes an argument (`-DARG`), `$wconvert` gets `TagSig: <TagFun[TagTuple[TagEPT, TagEPT, TagEPT]]>`, and `wrap` builds `T` directly.

`Lib.hs`:

```haskell
{-# LANGUAGE CPP #-}
module Lib (V (..), T (..), convert, wrap) where
data V = V [Int] | VNone
data T = T ![Int] !Int !V
{-# NOINLINE convert #-}
convert :: [Int] -> T
#if defined(ARG)
convert xs = case xs of
  [] -> big 2
  y : ys | y > 0 -> T ys y (V xs)
         | y < -5 -> big 3
         | otherwise -> T xs 0 VNone
  where big k = T (map (* k) xs) (length xs) (V (reverse xs))
#else
convert xs = case xs of
  [] -> big
  y : ys | y > 0 -> T ys y (V xs)
         | y < -5 -> big
         | otherwise -> T xs 0 VNone
  where big = T (map (* 2) xs) (length xs) (V (reverse xs))
#endif
{-# OPAQUE wrap #-}
wrap :: [Int] -> Maybe T
wrap xs = Just $! convert xs
```

`Main.hs`:

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import Lib
import System.Environment (getArgs)

-- Opaque, so that each iteration converts anew.
{-# OPAQUE pass #-}
pass :: Int -> a -> a
pass _ x = x

main :: IO ()
main = do
  [n] <- map read <$> getArgs
  let xs = [1, 2, 3] :: [Int]
      loop :: Int -> Int -> Int
      loop 0 !acc = acc
      loop r !acc = case wrap (pass r xs) of
        Just (T _ o _) -> loop (r - 1) (acc + o)
        Nothing -> acc
  print (loop n 0)
```

With `ghc -O -c Lib.hs -ddump-stg-final -dsuppress-all -dsuppress-uniques`, `wrap` is:

```
wrap =
    \r [xs]
        case case xs of xs { __DEFAULT -> $wconvert xs; } of wild {
        (#,,#) ww ww1 ww2 ->
        let {
          wrap_sat =
              \u []
                  case ww of ww {
                  __DEFAULT -> case ww2 of ww2 { __DEFAULT -> T [ww ww1 ww2]; };
                  };
        } in  Just [wrap_sat];
        };
```

With `-DARG` added, it is:

```
wrap =
    \r [xs]
        case case xs of xs { __DEFAULT -> $wconvert xs; } of wild {
        (#,,#) ww ww1 ww2 ->
        let { wrap_sat = T! [ww ww1 ww2]; } in  Just [wrap_sat];
        };
```

With `ghc -O -rtsopts -o main Main.hs Lib.hs` (and the same with `-DARG`), the bytes allocated (`./main N +RTS -s`) are:

```
              N = 100000    N = 200000    a call
no -DARG      12,056,056    24,056,072    120
-DARG          8,056,056    16,056,072     80
```

The input `[1, 2, 3]` takes the `y > 0` alternative, so the run never jumps to `big`. The 40 bytes are the thunk. These figures are from GHC HEAD 10.1.20260918, a build of `wip/T27737` on master e2d5702699 with local simplifier patches; 9.14.1 gives the same `wrap` and the same 120 and 80 bytes a call.

Does !16719 remove this thunk? I did not build it. If it does, this program could be a second regression test for #27841: with the fix, `wrap` in `-ddump-stg-final` has `T!` without `-DARG` too.
