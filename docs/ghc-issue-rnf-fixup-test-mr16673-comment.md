# GHC merge request comment: two filed triggers of fixup moves like #27800's, which !16673 probably does not reach

Posted 2026-10-17 as a comment on GHC [!16673](https://gitlab.haskell.org/ghc/ghc/-/merge_requests/16673), "Linear register allocator: allocate loops before the return continuations that enter them (#27800)" (open, by hsyl20, with no review notes on 2026-10-17 and its timeline already showing the mentions from #27980 and #27981), the fix for GHC [#27800](https://gitlab.haskell.org/ghc/ghc/-/work_items/27800); this file stays as the record of the comment, the paragraph from "#27980 and #27981 report" to "leaves both?" being the body as posted. It replaced, the same day, a longer draft kept below under "The longer draft, not posted": a Haskell program, needing `vector` and verified with GHC HEAD 10.1.20260918 only (built with `-package-db ~/.cabal/store/ghc-10.1.20260918-inplace/package.db` added), whose loop pays three fixup moves an element as in #27800, from the trigger of GHC [#27981](https://gitlab.haskell.org/ghc/ghc/-/work_items/27981), filed from `docs/ghc-issue-regalloc-stale-r1.md`, as its allocator liveness dump shows. #27981 and GHC [#27980](https://gitlab.haskell.org/ghc/ghc/-/work_items/27980), filed from `docs/ghc-issue-regalloc-pref-clash.md`, carry base-only programs, so the posted text only asks the question. Read on 2026-10-17: the MR's description, all its notes and its diff (Note [Deferred return continuations], `should_defer`, `processCyclicSCC`), and the description and all notes of #27800; no Haskell test is proposed on either, and !16673 adds only the Cmm test `T27800`. Open: no one built !16673, so that it leaves these moves is inferred from its diff. The prose is ASD-STE100 Simplified Technical English.

#27980 and #27981 report two more triggers of fixup moves on the back edge of a loop with a return continuation in it, which look like #27800 in the assembly. As I read the diff, `should_defer` defers only return continuations whose jumps go into a loop, so it reaches neither: in #27981, R1 stays allocated at the loop's own return continuation; in #27980, that continuation reloads a value into its preferred register, not the header's. I did not build this MR. Is it intended that it leaves both?

## The longer draft, not posted

Here is a Haskell program whose loop pays three fixup moves an element, as in #27800, but from another cause, which this MR probably does not reach. It needs `vector`.

`Lib.hs`:

```haskell
{-# LANGUAGE BangPatterns #-}
-- Forces every element of a slice of a boxed vector, after an out-of-line
-- test of the strides.
module Lib (A (..), rnfA) where

import qualified Data.Vector as V

data A = A [Int] !Int !Int !(V.Vector Double)  -- strides, offset, length

{-# NOINLINE dense #-}
dense :: [Int] -> Bool
dense st = st == [1]

{-# NOINLINE rnfA #-}
rnfA :: A -> ()
rnfA (A st o n v)
  | dense st = V.foldl' (\ _ x -> x `seq` ()) () (V.unsafeSlice o n v)
  | otherwise = ()
```

`Main.hs`:

```haskell
{-# LANGUAGE BangPatterns #-}
module Main (main) where

import qualified Data.Vector as V
import System.Environment (getArgs)
import Lib

-- Calls the forcing as an unknown function, once an iteration.
{-# OPAQUE runNF #-}
runNF :: (A -> ()) -> A -> Int -> Int
runNF f a = go 0
  where
    go !acc 0 = acc
    go !acc r = case f (pass r a) of () -> go (acc + 1) (r - 1 :: Int)

{-# OPAQUE pass #-}
pass :: Int -> A -> A
pass _ a = a

main :: IO ()
main = do
  [ks, rs] <- getArgs
  let k = read ks :: Int
      reps = read rs :: Int
  print (runNF (\ x -> rnfA x) (A [1] 0 k (V.generate k fromIntegral)) reps)
```

On GHC HEAD 10.1.20260918, a build of `wip/T27737` on master e2d5702699 with local simplifier patches, with `ghc -O -package vector -ddump-asm -ddump-asm-stats -ddump-to-file Lib.hs Main.hs -o Main`, `Lib.dump-asm-stats` has `(0, 0, 0, 3, 0, 10)` for `(allocs, clobbers, loads, joinRR, joinRM, reg_reg_moves_remaining)`. In `Lib.dump-asm`, the return continuation of the call to `dense`, `.Lc1pN`, reads R1 and branches to `.Lc1pR`, which gives the header `.Lc1q8` the array in `%rbx`, the offset in `%rcx` and the counter in `%rdx`:

```
.Lc1pN:
	andl $7,%ebx
	cmpq $1,%rbx
	je .Lc1pQ
.Lc1pR:
	movq 16(%rbp),%rax
	movq 32(%rbp),%rbx
	movq 24(%rbp),%rcx
	addq 8(%rbp),%rcx
	xorl %edx,%edx
	leaq GHC.Internal.Types.SPEC_closure+1(%rip),%rsi
	jmp .Lc1q8
```

The loop's own return continuation `.Lc1qo`, after the evaluation of each element, reloads into other registers, and the fixup block `.Lnk` moves them at every element:

```
.Lc1qo:
	movq 16(%rbp),%rax
	movq 32(%rbp),%rcx
	movq 24(%rbp),%rdx
	movq 8(%rbp),%rsi
	incq %rsi
	leaq GHC.Internal.Types.SPEC_closure+1(%rip),%rdi
.Lnk:
	movq %rcx,%rbx
	movq %rdx,%rcx
	movq %rsi,%rdx
.Lc1q8:
	cmpq %rax,%rdx
	jge .Lc1pQ
.Lc1qp:
	movq %rcx,%rax
	addq %rdx,%rax
	movq 24(%rbx,%rax,8),%rax
	movq $.Lblock_c1qo_info,(%rbp)
	movq %rax,%rbx
	movq %rdx,8(%rbp)
	movq %rcx,24(%rbp)
	testb $7,%bl
	jne .Lc1qo
```

`perf stat -e instructions:u ./Main 100000 100`, the same with `200`, differenced and divided by 10^7, gives 20.00 instructions an element.

The continuation of `dense` jumps to `.Lc1pQ` and `.Lc1pR`, neither in the loop; `.Lc1pR` then jumps to the header. As I read the diff, `should_defer` looks only at the continuation's own jump targets, so it does not defer it. The cause of these moves is another one. In `.Lc1qp`, R1 (`%rbx`) is written and is still allocated at `jne .Lc1qo`, although `-ddump-asm-liveness` (with `-fforce-recomp`) gives `(c1qo, {})`. So the element's continuation cannot reload the array into `%rbx`, the header's register. #27981 reports this trigger with a base-only program. I did not build this MR. Is it right that it leaves these three moves?
