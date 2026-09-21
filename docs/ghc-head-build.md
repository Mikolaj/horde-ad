# Building on GHC head

What it took on 2026-09-21 to build the library, the example sublibrary
and the benchmark suites with GHC 10.1.20260918 (ghc checkout 6913545
of 2026-09-18), for the benchmark night whose figures
are `bench/baseline-convvjp-ghc-head.tsv` and its siblings. The project file
was an ordinary one with orthotope's
`../orthotope/micro-regime3/cabal.project.ghead` appended and four departures:

1. `inspection-testing` dropped from `benchCommonLibrary`: its 0.6.3 imports
   a wired-in module the compiler no longer has. The dependency line
   in `horde-ad.cabal` and, in `bench/common/BenchMnistTools.hs`
   and `bench/common/BenchProdTools.hs`, the import and every `inspect $` line
   are commented out. The edit stays in the working tree, uncommitted,
   and changes no benchmarked code; it is what the head baselines' headers call
   the inspection-testing removal.

2. `ghc-typelits-knownnat-0.8.4` vendored under a path the project file names
   in `packages`, with its bound on ghc relaxed by `allow-newer`, and its solver
   patched for the wired-in modules that moved. The patch against the Hackage
   tarball, of its solver module, Solver.hs under src/GHC/TypeLits/KnownNat:

   ```diff
   138,139c138,142
   < import GHC.Builtin.Names
   <   ( knownNatClassName )
   ---
   > -- night 2026-09-21: patched for GHC 10.1.20260918, whose wired-in modules moved
   > import GHC.Builtin.KnownKeys
   >   ( knownNatClassKey )
   > import GHC.Core.Class
   >   ( classKey )
   141c144
   < import GHC.Builtin.Types
   ---
   > import GHC.Builtin.WiredIn.Types
   143c146
   < import GHC.Builtin.Types.Literals
   ---
   > import GHC.Builtin.WiredIn.TypeLits
   146c149
   < import GHC.Builtin.Types.Literals
   ---
   > import GHC.Builtin.WiredIn.TypeLits
   318c321
   <     |  className cls == knownNatClassName ||
   ---
   >     |  classKey cls == knownNatClassKey ||
   501c504
   <                          | className cls' == knownNatClassName
   ---
   >                          | classKey cls' == knownNatClassKey
   ```

   `ghc-typelits-natnormalise-0.9.7` and `ghc-tcplugin-api-0.20.1.0` build
   unpatched with their bounds on ghc relaxed the same way.

3. The `-fexcess-precision` of the `package *` stanza dropped:
   `scientific-0.3.8.1` fails to compile under it,
   with `error: Ratio has zero denominator` and no location. That the flag
   is the cause is inferred from the same version sitting in the head store
   built without it, and was not probed further. horde-ad's own
   `-fexcess-precision` stays.

4. `tests: False`, to shrink the solve; the benchmark binaries do not depend
   on it.

The fragment's own directives, each explained in its header comment,
are the rest of what separates a head build from a 9.12.4 one. The RTS options
the suites bake and horde-ad's own cabal flags are as on 9.12.4, but
by the third departure the dependencies and the orthotope sibling build without
`-fexcess-precision` on head, so a head figure against a 9.12.4 one
is the compiler's effect only up to that flag, which is measured nowhere yet;
what the pair of builds moved is in `bench/CLAUDE.md`.
