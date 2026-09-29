# vector issue: Storable `==` and `compare` allocate a thunk for every element

Filed 2026-09-30 as [vector issue 570][570]; this file stays as the filed record, the text from "## Summary" down being the filed body. Title: **Storable `basicUnsafeIndexM` does not force the element read, so `==` and `compare` allocate 56 bytes an element**. The prose is ASD-STE100 Simplified Technical English. The reproducer is a cabal script and needs only `vector` and `vector-stream`. The defect was found while rewriting orthotope's array comparison, `equalT`, whose index loops now avoid it, on orthotope's unpushed `pr-mikolaj-canonical-dispatch` branch. The open pull request [#489][489] rewrites the same Storable method for an unboxed index and keeps its lazy read, so it does not fix this; the body says so. A search for `eqBy`, `cmpBy`, `thunk`, `unsafeInlineIO` and Storable laziness found no issue or pull request about this defect. A workaround is known and is in the body, so the priority the issue gets does not matter.

## Summary

On `Data.Vector.Storable` vectors, `==` allocates 56 bytes for each element at `-O2`, and `compare` does the same with GHC 9.12.4 and later. On `Data.Vector.Unboxed` vectors, the two functions allocate nothing. The table gives the bytes that one comparison of two equal vectors of one million `Double`s allocates, divided by the length. The program is in "Steps to reproduce".

| GHC | Storable `==` | Storable `compare` | Unboxed `==` | Storable, read forced |
|---|---|---|---|---|
| 9.6.7 | 56 | 0 | 0 | 0 |
| 9.8.4 | 56 | 0 | 0 | 0 |
| 9.10.3 | 56 | 0 | 0 | 0 |
| 9.12.4 | 56 | 56 | 0 | 0 |
| 9.14.1 | 56 | 56 | 0 | 0 |
| HEAD 10.1.20260918 | 56 | 56 | 0 | 0 |

On GHC 9.12.4, in a variant of the program that repeats each comparison 100 times, Storable `==` takes 3.3 ns for each element and Unboxed `==` takes 0.6 ns.

The cause is `basicUnsafeIndexM` in the Storable `Vector` instance ([lines 124 to 128 of Data/Vector/Storable/Unsafe.hs][storable]):

```
  basicUnsafeIndexM (UnsafeVector _ fp) i
    = return
    . unsafeInlineIO
    $ unsafeWithForeignPtr fp $ \p ->
      peekElemOff p i
```

`return` gets the result of `unsafeInlineIO` as a thunk, so the read of the element does not occur in `basicUnsafeIndexM`. The thunk holds the `ForeignPtr` of the vector. The Primitive instance, which `Data.Vector.Unboxed` uses for `Double`, forces its read ([line 107 of Data/Vector/Primitive/Unsafe.hs][primitive]):

```
  basicUnsafeIndexM (UnsafeVector i _ arr) j = return $! indexByteArray arr (i+j)
```

The documentation of `basicUnsafeIndexM` ([lines 91 to 114 of Data/Vector/Generic/Base.hs][doc]) asks for the behavior of the Primitive instance: "indexing (but not the returned element!) is evaluated immediately". For a Storable vector, the read is the indexing.

`eqBy` in `Data.Stream.Monadic` ([lines 632 to 657][eqby]) then keeps the thunk. Its second loop, `eq_loop1`, gets the element of the first stream as an argument. The loop is not strict in that argument, because the branch for the end of the second stream does not use it. Thus the specialised loop gives the thunk from one step to the next. This is from the Core of `==` at `Double`, GHC 9.12.4, `-O2`:

```
jump $s$weq_loop1
  sc
  (+# sc1 1#)
  (case readDoubleOffAddr# ipv1 sc1 realWorld# of
   { (# ipv6, ipv7 #) ->
   case touch# ipv2 ipv6 of { __DEFAULT -> D# ipv7 }
   });
```

Each element thus costs the thunk and, when `==##` forces it, a `D#` box.

`cmpBy` has the same loop, `cmp_loop1` ([lines 660 to 685][cmpby]). GHC 9.10.3 inlines `cmp_loop1` into `cmp_loop0` for a Storable stream, which has no `Skip` step, so the read occurs where its result is used and nothing is allocated; 9.6.7 and 9.8.4 also allocate nothing for `compare`. GHC 9.12.4 keeps `cmp_loop1` as a separate join point and gives it the thunk, and 9.14.1 and HEAD allocate as 9.12.4 does. For `eq_loop1`, no GHC that I tried does this: `==` allocates on all of them.

I measured only `==` and `compare`. Other stream consumers that give an element to a loop that is not strict in it can have the same cost.

## Proposed fix

Force the read in the Storable instance, as the Primitive instance does. This is the change to vector-0.13.2.0 that I tested:

```diff
--- a/vector/src/Data/Vector/Storable.hs
+++ b/vector/src/Data/Vector/Storable.hs
@@ -186,7 +186,7 @@
 import Prelude
   ( Eq, Ord, Num, Enum, Monoid, Traversable, Monad, Read, Show, Bool, Ordering(..), Int, Maybe, Either, IO
   , compare, mempty, mappend, mconcat, showsPrec, return, seq, undefined, div
-  , (*), (<), (<=), (>), (>=), (==), (/=), (&&), (.), ($) )
+  , (*), (<), (<=), (>), (>=), (==), (/=), (&&), (.), ($), ($!) )
 
 import Data.Typeable  ( Typeable )
 import Data.Data      ( Data(..) )
@@ -259,7 +259,7 @@
 
   {-# INLINE basicUnsafeIndexM #-}
   basicUnsafeIndexM (Vector _ fp) i = return
-                                    . unsafeInlineIO
+                                    $! unsafeInlineIO
                                     $ unsafeWithForeignPtr fp $ \p ->
                                       peekElemOff p i
 
```

With this change, on GHC 9.12.4, Storable `==` and `compare` allocate nothing, and `eqBy` and `cmpBy` do not change. The last line of the reproducer shows the same result without a change to vector: it gives the unchanged `eqBy` a stream of the Storable vector in which the read is forced. With the change, all 2808 tests of `vector-tests-O2` pass on GHC 9.10.3. The open pull request [#489][489] changes this method to take an `Int#` and keeps `return .`, so the same change applies there.

If the `peek` of a user type returns an unevaluated value, the change also evaluates that value to weak head normal form.

A bang on the element in `eq_loop1` and `cmp_loop1` also removes the allocation, but it changes the result of `eqBy` for boxed vectors. If `u` is a boxed vector of `undefined` elements, `eqBy (\_ _ -> True) u u` now gives `True`, and with the bang it throws an exception.

Until a fix is released, a loop over `unsafeIndex`, or `Data.Vector.Unboxed`, avoids the allocation.

## Steps to reproduce

1. Save the program below as `Repro.hs`.

2. Run it. To select a compiler, add `-w ghc-VERSION`. For GHC 9.14.1 and HEAD, whose `base` is newer than vector-0.13.2.0 permits, I also added `--allow-newer=base,ghc-prim,ghc-bignum,template-haskell,containers`.

```
cabal run -v0 Repro.hs
```

3. On GHC 9.12.4, the output is:

```
Storable ==        56.0 bytes per element
Storable compare   56.0 bytes per element
Unboxed ==          0.0 bytes per element
Storable, strict    0.0 bytes per element
```

```haskell
{- cabal:
build-depends: base, vector ==0.13.2.0, vector-stream ==0.1.0.1
ghc-options: -O2
-}
-- Reproducer: Storable's == allocates for every element, and so does
-- compare from GHC 9.12 on; Unboxed's do not.
--
-- Run: cabal run -v0 Repro.hs
--
-- The last line compares the same Storable vectors through a stream
-- whose element read is forced, as Data.Vector.Primitive's is.
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import Control.Exception (evaluate)
import Data.Stream.Monadic (Stream (..), Step (..))
import qualified Data.Stream.Monadic as S
import Data.Vector.Fusion.Util (unId)
import qualified Data.Vector.Storable as VS
import qualified Data.Vector.Unboxed as VU
import System.Mem (getAllocationCounter)
import Text.Printf (printf)

-- The stream of a Storable vector, with the element read forced.
strictStream :: Monad m => VS.Vector Double -> Stream m Double
strictStream v = Stream step 0
  where
    step i
      | i >= VS.length v = return Done
      | otherwise = let !x = VS.unsafeIndex v i in return (Yield x (i + 1))

{-# NOINLINE eqS #-}
eqS, eqStrict :: VS.Vector Double -> VS.Vector Double -> Bool
eqS = (==)
{-# NOINLINE eqStrict #-}
eqStrict a b = unId (S.eqBy (==) (strictStream a) (strictStream b))

{-# NOINLINE cmpS #-}
cmpS :: VS.Vector Double -> VS.Vector Double -> Ordering
cmpS = compare

{-# NOINLINE eqU #-}
eqU :: VU.Vector Double -> VU.Vector Double -> Bool
eqU = (==)

-- Bytes allocated, per element, by one comparison of two equal vectors.
perElement :: String -> (v -> v -> r) -> v -> v -> Int -> IO ()
perElement name f a b n = do
  c0 <- getAllocationCounter
  _ <- evaluate (f a b)
  c1 <- getAllocationCounter
  printf "%-17s %5.1f bytes per element\n" name
    (fromIntegral (c0 - c1) / fromIntegral n :: Double)

main :: IO ()
main = do
  let n = 1000000
  a <- evaluate (VS.generate n fromIntegral)
  b <- evaluate (VS.generate n fromIntegral)
  ua <- evaluate (VU.generate n fromIntegral)
  ub <- evaluate (VU.generate n fromIntegral)
  perElement "Storable ==" eqS a b n
  perElement "Storable compare" cmpS a b n
  perElement "Unboxed ==" eqU ua ub n
  perElement "Storable, strict" eqStrict a b n
```

## Expected behavior

Storable `==` and `compare` allocate nothing for each element, as Unboxed `==` and `compare` do.

## Environment

* vector-0.13.2.0 and vector-stream-0.1.0.1, from Hackage. On master at [fd2ebe1534][master], the Storable `basicUnsafeIndexM`, `eqBy` and `cmpBy` have the same code, the Storable constructor renamed `UnsafeVector`.
* GHC 9.6.7, 9.8.4, 9.10.3, 9.12.4, 9.14.1, and HEAD 10.1.20260918 (commit 6913545fd3); cabal-install 3.18.1.0.
* Linux (kernel 7.0.0-31-generic), x86_64 (AMD Ryzen 7 5800X).

[570]: https://github.com/haskell/vector/issues/570
[489]: https://github.com/haskell/vector/pull/489
[storable]: https://github.com/haskell/vector/blob/fd2ebe15344913368c38bd62e4f0452ecbe08e74/vector/src/Data/Vector/Storable/Unsafe.hs#L124-L128
[primitive]: https://github.com/haskell/vector/blob/fd2ebe15344913368c38bd62e4f0452ecbe08e74/vector/src/Data/Vector/Primitive/Unsafe.hs#L107
[doc]: https://github.com/haskell/vector/blob/fd2ebe15344913368c38bd62e4f0452ecbe08e74/vector/src/Data/Vector/Generic/Base.hs#L91-L114
[eqby]: https://github.com/haskell/vector/blob/fd2ebe15344913368c38bd62e4f0452ecbe08e74/vector-stream/src/Data/Stream/Monadic.hs#L632-L657
[cmpby]: https://github.com/haskell/vector/blob/fd2ebe15344913368c38bd62e4f0452ecbe08e74/vector-stream/src/Data/Stream/Monadic.hs#L660-L685
[master]: https://github.com/haskell/vector/tree/fd2ebe15344913368c38bd62e4f0452ecbe08e74
