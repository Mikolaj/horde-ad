# Fresh identifiers under a duplicated evaluation

The programs behind the figures in the module header
of `HordeAd.Core.AstFreshId`, which says why every fresh identifier is drawn
under `unsafePerformIO`, and two ideas this work raised and did not try. Each
program is standalone and needs only `base`. All were built and run
on 2026-10-02 with GHC 9.12.4 on a machine with 16 processors.

## The lambda tear

A mirror of `tlambda`: an identifier drawn by an impure function is paired
with a body using it, and a lazy pattern stores the two halves
in a constructor's two lazy fields, as `tlambda` stores a `funToAst` pair
in `AstLambda`. Two threads on separate capabilities force each freshly
published value, one reading the binder first and the other the body, and count
the values whose body holds a different identifier. Mode `dupable` draws
under `unsafeDupablePerformIO`, mode `plain` under `unsafePerformIO`, and mode
`dupable-case` draws dupably but takes the pair apart with one `case`.

```sh
ghc -O1 -threaded -rtsopts -fno-omit-yields Tear.hs -o tear
./tear dupable 2000000 +RTS -N3 -RTS
```

| Mode | Torn values in 2,000,000, per run |
|---|---|
| `dupable` | 17520, 30213, 35038 |
| `plain` | 0, 0 |
| `dupable-case` | 0, 0 |

```haskell
{-# LANGUAGE BangPatterns #-}
-- Does a lazily destructured pair drawn under unsafeDupablePerformIO tear
-- (binder from one evaluation, body from another) when two threads force it?
-- Mirrors tlambda: let (var, ast) = funToAst ... in AstLambda var ast,
-- with AstLambda's fields lazy.
module Main (main) where

import Control.Concurrent
import Control.Monad
import Data.IORef
import GHC.Conc (forkOn)
import System.Environment (getArgs)
import System.IO.Unsafe

counter :: IORef Int
{-# NOINLINE counter #-}
counter = unsafePerformIO (newIORef 0)

fresh :: IO Int
fresh = atomicModifyIORef' counter (\n -> (n + 1, n))

funToAstD, funToAstP :: Int -> (Int, [Int])
{-# NOINLINE funToAstD #-}
funToAstD k = unsafeDupablePerformIO $ do { !v <- fresh; return (v, [v, k]) }
{-# NOINLINE funToAstP #-}
funToAstP k = unsafePerformIO $ do { !v <- fresh; return (v, [v, k]) }

data Lam = Lam Int [Int]  -- like AstLambda: both fields lazy (no StrictData)

mkLam :: (Int -> (Int, [Int])) -> Int -> Lam
{-# NOINLINE mkLam #-}
mkLam fun k = let (var, body) = fun k in Lam var body

mkLamCase :: (Int -> (Int, [Int])) -> Int -> Lam
{-# NOINLINE mkLamCase #-}
mkLamCase fun k = case fun k of (var, body) -> Lam var body

-- Force binder then body, or body then binder; report a torn lambda.
check :: Bool -> Lam -> IO Bool
check binderFirst (Lam var body) =
  if binderFirst
  then do { !v <- pure var; let { !b = head body }; pure (v /= b) }
  else do { let { !b = head body }; !v <- pure var; pure (v /= b) }

main :: IO ()
main = do
  [mode, itersS] <- getArgs
  let fun = if mode == "plain" then funToAstP else funToAstD
      mk = if mode == "dupable-case" then mkLamCase else mkLam
      iters = read itersS :: Int
  gen <- newIORef (0 :: Int)
  cell <- newIORef (mk fun 0)
  torn <- newIORef (0 :: Int)
  dones <- forM [0, 1 :: Int] $ \w -> do
    done <- newEmptyMVar
    _ <- forkOn (w + 1) $ do
      let loop !g | g > iters = putMVar done ()
                  | otherwise = do
            let spin = do { g' <- readIORef gen; unless (g' >= g) spin }
            spin
            lam <- readIORef cell
            t <- check (w == 0) lam
            when t $ atomicModifyIORef' torn (\n -> (n + 1, ()))
            loop (g + 1)
      loop 1
    pure done
  forM_ [1 .. iters] $ \g -> do
    writeIORef cell (mk fun g)
    atomicWriteIORef gen g
    let wait = do { threadDelay 0; yield }  -- let workers catch up a little
    when (g `mod` 64 == 0) wait
  mapM_ takeMVar dones
  n <- readIORef torn
  putStrLn $ mode ++ ": torn lambdas observed = " ++ show n
    ++ " out of " ++ show iters
```

## The pure wrapper

The same pair taken through a pure function that forces the impure one,
as the body of `tgrad`'s lambda reaches its artifact. Under `unsafePerformIO`
none tears, so `noDuplicate#` claims the enclosing pure thunk as well
as the innermost. The first two runs of each mode were of an earlier version
that also carried a long-work harness, the one the next section replaced;
the third is of the source shown. Each of the two threads counts, so a count can
pass the number of values.

```sh
ghc -O1 -threaded -rtsopts -fno-omit-yields TearNested.hs -o tearnested
./tearnested nested-dupable 1000000 +RTS -N3 -RTS
```

| Mode | Torn values in 1,000,000, per run |
|---|---|
| `nested-dupable` | 1177106, 164623, 947385 |
| `nested-plain` | 0, 0, 0 |

```haskell
{-# LANGUAGE BangPatterns #-}
-- The correlated pair comes from a PURE thunk whose evaluation calls the
-- impure function (like tgrad's lambda body forcing the artifact); does
-- unsafePerformIO's noDuplicate# protect the pure enclosing thunk too?
module Main (main) where

import Control.Concurrent
import Control.Monad
import Data.IORef
import GHC.Conc (forkOn)
import System.Environment (getArgs)
import System.IO.Unsafe

counter :: IORef Int
{-# NOINLINE counter #-}
counter = unsafePerformIO (newIORef 0)

fresh :: IO Int
fresh = atomicModifyIORef' counter (\n -> (n + 1, n))

funD, funP :: Int -> (Int, [Int])
{-# NOINLINE funD #-}
funD k = unsafeDupablePerformIO $ do { !v <- fresh; return (v, [v, k]) }
{-# NOINLINE funP #-}
funP k = unsafePerformIO $ do { !v <- fresh; return (v, [v, k]) }

rewrap :: (Int, [Int]) -> (Int, [Int])
{-# NOINLINE rewrap #-}
rewrap (v, b) = (v, map id b)  -- pure; forces the impure pair

data Lam = Lam Int [Int]  -- lazy fields, like AstLambda

mkNested :: (Int -> (Int, [Int])) -> Int -> Lam
{-# NOINLINE mkNested #-}
mkNested fun k = let (var, body) = rewrap (fun k) in Lam var body

-- Two workers on separate capabilities force the same freshly published
-- value each generation; `act w x` is what worker w does with it.
race :: Int -> IO a -> (Int -> a -> IO ()) -> IO ()
race iters mk act = do
  gen <- newIORef (0 :: Int)
  x0 <- mk
  cell <- newIORef x0
  dones <- forM [0, 1 :: Int] $ \w -> do
    done <- newEmptyMVar
    _ <- forkOn (w + 1) $ do
      let loop !g | g > iters = putMVar done ()
                  | otherwise = do
            let spin = do { g' <- readIORef gen; unless (g' >= g) spin }
            spin
            readIORef cell >>= act w
            loop (g + 1)
      loop 1
    pure done
  forM_ [1 .. iters] $ \g -> do
    x <- mk
    writeIORef cell x
    atomicWriteIORef gen g
    when (g `mod` 64 == 0) yield
  mapM_ takeMVar dones

main :: IO ()
main = do
  [mode, itersS] <- getArgs
  let iters = read itersS
      fun = if mode == "nested-plain" then funP else funD
  torn <- newIORef (0 :: Int)
  race iters (pure (mkNested fun 0) >>= \_ -> do
                k <- atomicModifyIORef' counter (\c -> (c, c))
                pure (mkNested fun k))
       (\w (Lam var body) -> do
          t <- if w == 0
               then do { !v <- pure var; let { !b = head body }; pure (v /= b) }
               else do { let { !b = head body }; !v <- pure var; pure (v /= b) }
          when t $ atomicModifyIORef' torn (\c -> (c + 1, ())))
  n <- readIORef torn
  putStrLn $ mode ++ ": torn " ++ show n ++ " of " ++ show iters
```

## How long a duplicated evaluation survives

Two threads force each value at the same instant, the main thread waiting
for both before it publishes the next, and the value's work, folding a reversed
list of n cells under `unsafeDupablePerformIO`, counts the copies that start
and the copies that finish. Short work, a draw among it, nearly always finished
twice; work of 10^5 cells or more always lost one copy.

```sh
ghc -O1 -threaded -rtsopts -fno-omit-yields Survive.hs -o survive
./survive 10 20000 +RTS -N3 -A32m -RTS
./survive 100000 200 +RTS -N3 -A32m -RTS
```

| n | Values | Copies started | Copies finished |
|---|---|---|---|
| 10 | 20000 | 39802 | 39793 |
| 100 | 20000 | 39994 | 39981 |
| 1000 | 20000 | 39998 | 39841 |
| 10000 | 20000 | 39981 | 36994 |
| 100000 | 200 | 399 | 200 |
| 1000000 | 200 | 395 | 200 |

```haskell
{-# LANGUAGE BangPatterns #-}
-- Two threads force the same fresh thunk at the same moment each generation
-- (main waits for both before publishing the next). The thunk runs
-- allocating work of size n under unsafeDupablePerformIO. Counts how many
-- duplicate copies start and how many run to completion.
module Main (main) where

import Control.Concurrent
import Control.Monad
import Data.IORef
import Data.List (foldl')
import GHC.Conc (forkOn)
import System.Environment (getArgs)
import System.IO.Unsafe

started, finished :: IORef Int
{-# NOINLINE started #-}
started = unsafePerformIO (newIORef 0)
{-# NOINLINE finished #-}
finished = unsafePerformIO (newIORef 0)

work :: Int -> Int -> Int
{-# NOINLINE work #-}
work n seed = unsafeDupablePerformIO $ do
  atomicModifyIORef' started (\c -> (c + 1, ()))
  let !r = foldl' (+) seed (reverse [1 .. n])
  atomicModifyIORef' finished (\c -> (c + 1, ()))
  return r

main :: IO ()
main = do
  [nS, itersS] <- getArgs
  let n = read nS; iters = read itersS :: Int
  gen <- newIORef (0 :: Int)
  acks <- newIORef (0 :: Int)
  cell <- newIORef (work n (-1))
  forM_ [0, 1 :: Int] $ \w -> forkOn (w + 1) $ do
    let loop !g = when (g <= iters) $ do
          let spin = do { g' <- readIORef gen; unless (g' >= g) spin }
          spin
          x <- readIORef cell
          _ <- pure $! x
          atomicModifyIORef' acks (\c -> (c + 1, ()))
          loop (g + 1)
    loop 1
  forM_ [1 .. iters] $ \g -> do
    writeIORef cell (work n g)
    atomicWriteIORef gen g
    let waitAcks = do { a <- readIORef acks; unless (a >= 2 * g) (yield >> waitAcks) }
    waitAcks
  s <- readIORef started; f <- readIORef finished
  putStrLn $ "n=" ++ show n ++ ": thunks " ++ show iters
    ++ ", copies started " ++ show s ++ ", finished " ++ show f
```

## What noDuplicate# costs

Two programs time a draw per call under each primitive: the first over 30,000
nested calls of a non-tail recursion with no update frames on the stack,
the shape of `evalRevFromnMap` under `-flate-dmd-anal`, the second per call
over 10^7 calls of a tail-recursive loop.

```sh
ghc -O1 -threaded -rtsopts CostDeep.hs -o costdeep
./costdeep plain 30000 +RTS -N4 -K1g -RTS
ghc -O1 -threaded -rtsopts -fno-omit-yields CostShallow.hs -o costshallow
./costshallow plain 10000000 +RTS -N4 -RTS
```

| Program | Capabilities | `unsafePerformIO` | `unsafeDupablePerformIO` |
|---|---|---|---|
| deep, 30,000 calls | 1 | 3.5 ms, 3.5 ms | 2.4 ms, 2.5 ms |
| deep, 30,000 calls | 4 | 86 ms, 86 ms | 3.7 ms, 2.5 ms |
| shallow, per call | 1 | 30.8 ns, 30.9 ns | 25.9 ns, 28.2 ns |
| shallow, per call | 4 | 52.0 ns, 49.8 ns | 29.9 ns, 29.4 ns |

```haskell
{-# LANGUAGE BangPatterns #-}
-- Cost of unsafePerformIO vs unsafeDupablePerformIO per call at stack depth,
-- with no update frames on the stack (non-tail recursion), as in
-- evalRevFromnMap under -flate-dmd-anal.
module Main (main) where

import Data.IORef
import System.CPUTime
import System.Environment (getArgs)
import System.IO.Unsafe

counter :: IORef Int
{-# NOINLINE counter #-}
counter = unsafePerformIO (newIORef 0)

tickP, tickD :: Int -> Int
{-# NOINLINE tickP #-}
tickP x = unsafePerformIO $ do { n <- atomicModifyIORef' counter (\c -> (c + 1, c)); return $! n + x }
{-# NOINLINE tickD #-}
tickD x = unsafeDupablePerformIO $ do { n <- atomicModifyIORef' counter (\c -> (c + 1, c)); return $! n + x }

deep :: (Int -> Int) -> Int -> Int
{-# NOINLINE deep #-}
deep _ 0 = 0
deep t n = let !a = t n in a `seq` (a + deep t (n - 1))

main :: IO ()
main = do
  [mode, nS] <- getArgs
  let t = if mode == "plain" then tickP else tickD
  t0 <- getCPUTime
  let !r = deep t (read nS)
  t1 <- getCPUTime
  putStrLn $ mode ++ ": " ++ show (fromIntegral (t1 - t0) / 1e12 :: Double)
    ++ " s CPU (result " ++ show (r `mod` 7) ++ ")"
```

```haskell
{-# LANGUAGE BangPatterns #-}
-- Per-call cost on a SHALLOW stack (tail-recursive loop, no depth).
module Main (main) where

import Data.IORef
import System.CPUTime
import System.Environment (getArgs)
import System.IO.Unsafe

counter :: IORef Int
{-# NOINLINE counter #-}
counter = unsafePerformIO (newIORef 0)

tickP, tickD :: Int -> Int
{-# NOINLINE tickP #-}
tickP x = unsafePerformIO $ do { n <- atomicModifyIORef' counter (\c -> (c + 1, c)); return $! n + x }
{-# NOINLINE tickD #-}
tickD x = unsafeDupablePerformIO $ do { n <- atomicModifyIORef' counter (\c -> (c + 1, c)); return $! n + x }

loop :: (Int -> Int) -> Int -> Int -> Int
{-# NOINLINE loop #-}
loop _ !acc 0 = acc
loop t !acc i = loop t (acc + t i) (i - 1)

main :: IO ()
main = do
  [mode, nS] <- getArgs
  let t = if mode == "plain" then tickP else tickD
      n = read nS
  t0 <- getCPUTime
  let !r = loop t 0 n
  t1 <- getCPUTime
  putStrLn $ mode ++ ": " ++ show (fromIntegral (t1 - t0) / 1e3 / fromIntegral n :: Double)
    ++ " ns/call (" ++ show (r `mod` 7) ++ ")"
```

## Ideas not tried

- **A runtime regression test for the tear.** `tools/check-fresh-draws.py` keeps
  every draw under `unsafePerformIO`, which rules the tear out, but nothing
  exercises the behaviour itself. A test could build a fresh lambda through
  `tlambda` each iteration, made to depend on the iteration so that full
  laziness cannot hoist it, force its binder and its body from two threads
  on separate capabilities in opposite orders, and assert that the body's only
  free variable is the binder; and the same for a `tgrad` lambda, whose artifact
  is forced outside `funToAst`'s claim. It needs at least two capabilities,
  so it should fail rather than skip below two, and its mutant is `funToAst`
  drawing under `unsafeDupablePerformIO` again, which the mirror above, tearing
  about one value in a hundred, suggests a modest iteration count would catch.
- **`OPAQUE` on `evalRevFromnMap`.** Under `-flate-dmd-anal`, GHC
  [#27885](https://gitlab.haskell.org/ghc/ghc/-/work_items/27885) leaves
  the self tail call of the backward-pass loop's worker a non-tail call,
  so the stack grows with the loop and every remaining stack walk
  of `noDuplicate#` lengthens with it. The fix proposed in that issue restores
  the tail call in GHC. `OPAQUE`, which suppresses worker/wrapper, might restore
  it from horde-ad's side, the issue arising in the worker that late
  worker/wrapper splits off; untried, it owes CAFlessTest's time
  with `-flate-dmd-anal`, with and without the pragma.
