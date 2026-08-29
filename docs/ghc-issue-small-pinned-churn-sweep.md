# The awareness-sweep record for the small-pinned-churn issue

The evidence behind GHC [#27719](https://gitlab.haskell.org/ghc/ghc/-/work_items/27719)'s claim that the mutator-TIME cost of small-pinned churn is unknown upstream --- its preamble's one-sentence summary and its "duplicate" and "conscious trade-off" bullets distill this file. Two sweeps, both 2026-08-18. Not for posting; a quote source if triage challenges the claim.

## Sweep 1: titles, descriptions, full threads, user-facing docs

Method: the GitLab REST API (`api/v4/projects/1/issues?search=` and the `merge_requests` sibling; `search` covers title+description only), the frontend discussions-JSON endpoints for complete comment threads (the `/notes` API answers 401 unauthenticated on gitlab.haskell.org), and direct reads of the user's guide and haddocks. Anubis blocks only HTML routes and never had to be dealt with.

Read in full (threads included): #7257, #7831, #19171, #23221, #19481, #19248, #21483, #19175, #22768, #24246, #13630, #19357, and MRs !5175 and !10524. Every one frames pinned/block fragmentation as a memory/RSS cost.

Load-bearing quotes:

* `Note [Sources of Block Level Fragmentation]` (drafted in #19481, committed in rts/sm/Storage.c): "Having a block-level fragmented heap means your program will never go below a certain memory threshold but it doesn't \"use\" more memory during periods of high residency." and "The block allocator can reuse unused space within a megablock and therefore as residency increases again, the fragmented blocks will get filled up."
* MR !5175 (the accumulator-path introduction, mpickering; found via commit 47d6acd3be): the only time-flavored exchange is about GC scheduling --- bgamari: "I do wonder whether this will result in pathologically premature GC in some cases?"; mpickering: "In fact, this code will mean that it takes potentially longer to reach a GC if you are only allocating pinned blocks." No mutator-time cost is named anywhere in the review.
* #7257 (2012, the closest anything comes to a time cost): Marlow, announcing the allocation-path fix --- "As a bonus, I have made the program go faster by a factor of 10." A bonus of the fix, not a diagnosis of a lingering tax.
* #7831: Marlow --- "I doubt this is ever an issue in practice. The fragmentation that arises this way is bounded ... the fragmented space will be used to store small objects, so it won't be wasted."
* User's guide, runtime-control chapter: the word "pinned" does not occur; the `-A` text points the other way ("in a parallel setting increasing the allocation area to 16MB, or even 64MB can increase gc throughput significantly").
* GHC.ForeignPtr haddocks: "mallocForeignPtr has a heavily optimised implementation in GHC ... Use of mallocForeignPtr and associated functions is strongly recommended" --- no caveat. Data.Vector.Storable haddocks: no occurrence of "pinned" or "fragment".
* GHC wiki, commentary on pinned objects: "using pinned objects may lead to memory fragmentation" --- memory only.

## Sweep 2: all comment bodies, authenticated

Method: `GITLAB_HOST=gitlab.haskell.org glab api 'projects/1/search?scope=notes&search=TERM&per_page=100'`. The instance runs GitLab basic search, so a multi-word term is word-AND over the note body (substring, case-insensitive) --- quoted phrases are not exact, which widens recall and permits direct co-occurrence queries. Every term fit one page at `per_page=100`; page 2 verified empty for the two largest terms.

41 terms over the mechanism vocabulary (allocatePinned, pinned_object_empty, PINNED_EMPTY_SIZE, pinned_object_block, mallocForeignPtrBytes, pinned/nursery/block-level fragmentation, free list fragmentation, empty pinned, 3256, ...) crossed with the symptom vocabulary (slow, slower, slowdown, performance, mutator, cache, LLC, TLB, locality, degrade): 256 unique notes (169 on issues, 87 on MRs), most of them `+RTS -s` dumps or compiler-perf threads, every candidate read in sentence context. Zero hits name a mutator-time cost of pinned or block-level churn; zero hits landed on GHC #27601 (our own filing, excluded as evidence anyway).

The nearest misses, each tying heap layout to mutator time through a different mechanism:

* MR !4523 (hugepages, teo, 2024): "We see a big drop in dTLB misses from approx 20% to 8%, but this doesn't translate to a decrease in elapsed time as memory lookups aren't a bottleneck." --- block-allocator layout measured against mutator time, via TLB, with a null result.
* #14981 (AndreasK, 2023): "GC performs some optimizations (... moving heap objects next to each other) which can be beneficial and change the performance of the mutator, in some cases significantly" --- locality-affects-mutator awareness framed as a GC benefit, no unrepaired-scatter counterpart.
* #13362: literature quote on nursery sizing and L2/TLB misses; #9221: parallel-GC cache thrash; #22782: text-section (code layout) misses; #8732: pinned-allocation lock contention; #27021: FFI demand paging. None of them this condition.

## Caveats carried

Basic search is word-AND, so a comment describing the phenomenon while avoiding both the mechanism and the symptom vocabulary would be missed. Confidential issues beyond the account's visibility are absent from results. Work-item note indexing under the notes scope is unverified --- immaterial, the only relevant work item being our own.
