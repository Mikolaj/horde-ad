# GHC issue: a loop latch loses its fall-through when its exit block has a second predecessor

Filed as [GHC work item 27799](https://gitlab.haskell.org/ghc/ghc/-/work_items/27799); this file stays as the filed record, the text from "## Summary" down being the filed body, posted under a preface and inside a `<details>` block, neither of which is carried here. Title: **x86 NCG: a loop pays one jump on each iteration when its exit block has a second predecessor, because block layout takes 1/32 off an edge that leaves a conditional branch**. The prose is ASD-STE100 Simplified Technical English. The reproducer needs only `ghc` and `base`. The case that found the defect is an innermost strided copy; a second case, which this report does not need, occurs in a program that uses `vector`.

## Summary

A loop whose test is at the bottom, its latch, can put only one of the two successors of that test immediately after it. The loop body is already before the test, thus the exit block is the only successor that can get the fall-through. If the exit block has a second predecessor, block layout gives the fall-through to that other predecessor. The loop then ends with a conditional jump to the exit and an unconditional jump back to the body, and it executes one more instruction on each iteration. This is a code quality defect and not a wrong code defect.

**#17864 keeps the TODO list of the NCG NOTES file that was removed from the tree**, and it asks that separate issues track the items of that list. Not a single such issue has been written yet. This report is a partial start on that. The defect here has two halves: the choice that the register allocator makes at a join, which is one item of that list and which this report quotes further down, and the price that block layout puts on the edge of a latch, which is not in the list.

The loop loses this competition each time, because the two edges have the same frequency and only one of them gets a modifier. `relevantWeight` in `GHC.CmmToAsm.BlockLayout` multiplies an edge that leaves a conditional branch by 0.96875. Note [Layout relevant edge weights] gives the reason for the modifier, and #18053 is the item that caused it. The other predecessor arrives with an unconditional jump and keeps its full weight. In the reproducer the final CFG gives the edge of the latch 0.14063 and the other edge 0.14062, thus the latch is in front until the modifier puts it at 0.13623.

The modifier is correct that a conditional jump stays in the code after the layout. It is not correct about what a failure to fuse then costs. The other successor of the test is the loop body, which is already placed, thus a failure to fuse the exit does not only keep the conditional jump: it adds an unconditional jump on the back edge. In the reproducer the back edge has the frequency 0.42293 and the exit edge has 0.14063, thus the true price is three times the quantity that the algorithm compares. `buildChains` removes the back edge because that edge would make a cycle, and it does not give a new price to the one edge of the block that is left.

A possible correction has two forms. The narrow form is to not apply the modifier to an edge that leaves a conditional branch when the other successor of that branch is already placed, because a fall-through then does remove an unconditional jump, which is the condition that the note gives for the full weight. The general form is to give a new price to the remaining edge of a block each time that `buildChains` removes one of its edges as a cycle, because the removed edge is then the quantity that a failure to fuse costs. A bonus on the exit edge of a latch that is equal to the weight of the back edge has the same effect.

Which loops get the split shape is decided before block layout, in the linear register allocator. The exit block is a join, and the two arms of the join do not agree about registers, thus the allocator puts a fixup block on one of them. `joinToTargets` keeps the assignment of the first jump to a block and makes fixup code for each later jump, thus the arm that is second in the processing order is the arm that pays. When the fixup is on the arm of the latch, the successor of the latch is a private block that no other block enters, and the loop keeps its fall-through. When the fixup is on the other arm, the latch competes for the shared exit block and loses. The processing order comes from `sccBlocks`, which numbers its vertices in the order of its input, and that input is the entry block and then the blocks of the procedure in the ascending order of their uniques. Thus only the order of the uniques has an effect, and not their values.

Two results follow, and the reproducer shows both. Each compiler makes both shapes, thus this is not a regression: `-fobject-determinism` gives the split shape on HEAD and the fused shape on 9.12.4, and `-fno-object-determinism` gives the opposite. Also, a change that has no relation to the loop can move the shape, because such a change can move the uniques. The TODO for the register allocator part is the one that #17864 keeps: "picking the assignment on entry to a block: better to defer this until we know all the assignments. In a loop, we should pick the assignment from the looping jump (fixpointing?), so that any fixup code ends up *outside* the loop. Otherwise, we should pick the assignment that results in the least fixup code." A deliberate choice there would make the shape stable, but it would not give the fall-through back, because the latch loses the competition each time that the exit block has a second predecessor.

The rule that the two halves make is exact on the twelve loops of this shape that were examined, in three programs and with both compilers: a latch keeps its fall-through if and only if its exit successor has no other predecessor.

These do not move the loop: `-fregs-graph`, `-fblock-layout-weightless`, and a large `backEdgeBonus` through `-fblock-layout-weights`. `-fno-block-layout-cfg` gives a third arrangement and not a correction: it puts the test above the body and makes the back edge an unconditional jump, which has the same price of two instructions on each iteration. Time was not measured for this loop; this report is about the one instruction on each iteration.

Adjacent items, none of them this one: #17823 shows a fixup block that the linear allocator adds because of its order, and #18208 gave a partial answer to it; #14914 asks that the choice of a fall-through target use more than the number of predecessors; #15124 is where the current layout algorithm comes from. #27687 is adjacent also, and a comment on it gives the connection.

## Steps to reproduce

1. Save the program below as `Repro.hs`.

2. Compile it two times, to assembly:

```
ghc -O2 -fobject-determinism    -S Repro.hs -o det.s
ghc -O2 -fno-object-determinism -S Repro.hs -o nodet.s
```

3. Find the innermost loop in each file. It is the block whose two `movsd` instructions are followed by `addq`, `incq` and `cmpq`; another block has a `movsd` pair and is not the loop. On GHC HEAD, `det.s` has the split shape and `nodet.s` has the fused shape. On GHC 9.12.4 the two files exchange the shapes.

The split shape, from HEAD with `-fobject-determinism`:

```
.LQ1C:
	movsd (%rdx,%rdi,8),%xmm0
	movsd %xmm0,(%rbx,%rsi,8)
	addq %rax,%rdi
	incq %rsi
.LQ1y:
	cmpq %rcx,%rsi
	jge .LQ1g
	jmp .LQ1C
```

The fused shape, from 9.12.4 with the same command. The instructions are equal and the registers are equal:

```
.LQ2b:
	movsd (%rdx,%rdi,8),%xmm0
	movsd %xmm0,(%rbx,%rsi,8)
	addq %rax,%rdi
	incq %rsi
.LQ28:
	cmpq %rcx,%rsi
	jl .LQ2b
```

4. Add `-ddump-cfg-weights` to see the cause. In the split build the exit block has two predecessors, the latch and a fixup block of the register allocator, and the edge of the latch is the heavier of the two before the modifier. In the fused build the fixup block is on the arm of the latch, thus the successor of the latch has one predecessor only.

At `-O1` the flag `-fliberate-case` is necessary also. Without it the writer keeps its state on the stack, and no loop in registers is there to lay out. `-O2` supplies that flag.

```haskell
-- Reproducer: a loop latch loses its fall-through when a second predecessor
-- enters its exit block.  Base only.
--
-- Build:  ghc -O2 -fobject-determinism    -S Repro.hs -o det.s
--         ghc -O2 -fno-object-determinism -S Repro.hs -o nodet.s
--
-- The innermost loop, the block with two movsd instructions, ends in
-- "cmpq; jge exit; jmp body" in one of the two files and in "cmpq; jl body"
-- in the other.  Which file gets which shape depends on the compiler version.
{-# LANGUAGE BangPatterns #-}
module Repro (fill) where

import Foreign.Ptr (Ptr)
import Foreign.Storable (peekElemOff, pokeElemOff)
import System.IO.Unsafe (unsafeDupablePerformIO)

idx :: Ptr Int -> Int -> Int
{-# INLINE idx #-}
idx p i = unsafeDupablePerformIO (peekElemOff p i)

fill :: Ptr Double -> Ptr Double -> Ptr Int -> Int -> Int -> IO Int
{-# NOINLINE fill #-}
fill out v p !sInner !tInner = go 0 0 0
  where
    go !lev !outPos !baseOff
      | lev >= 2 =
          let !oEnd = outPos + sInner
              inner !o !src
                | o >= oEnd = return ()
                | otherwise = do
                    x <- peekElemOff v src
                    pokeElemOff out o x
                    inner (o + 1) (src + tInner)
          in  inner outPos baseOff >> return (outPos + sInner)
      | otherwise =
          let !n  = idx p lev
              !st = idx p (lev + 4)
              dim !k !op !boff
                | k <= 0    = return op
                | otherwise = go (lev + 1) op boff >>= \op' -> dim (k - 1) op' (boff + st)
          in  dim n outPos baseOff
```

## Expected behavior

The expected behavior is that the exit block of a loop goes immediately after the test of that loop, and that the loop makes one conditional jump on each iteration. An edge that leaves a conditional branch must be able to win the fall-through against an unconditional edge of the same frequency when the other successor of that branch is already placed.

## Environment

* GHC version used: 9.12.4 and HEAD 10.1.20260803 (commit d415f38a75). Each of the two makes both shapes, and `-fobject-determinism` selects which.

Optional:

* Operating System: Linux (kernel 7.0.0-31-generic)
* System Architecture: x86_64
* Other tools: gcc as the assembler

/label ~"T::bug"
/label ~"needs triage"
