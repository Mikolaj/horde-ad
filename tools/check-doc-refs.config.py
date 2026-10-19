"""Settings for ~/slop/tools/check-doc-refs.py in this repository, read by its
common.repo_config: the block that stood at the head of the checker while it
lived in this repository's tools/, and which says what each setting does.
"""

SEARCH_ROOTS = ["src", "test", "bench", "example", "tools", ".github"]
# Where the executable's `long "..."` options are declared; "" if the repo
# ships no command-line parser, in which case every `--flag` falls
# through to the external/unknown buckets.
OPTIONS_FILE = ""
# Module prefix owned by this repo, the one namespace where an
# unresolved module is a failure rather than a shrug; "" to disable.
OUR_NAMESPACE = "HordeAd."
# The file whose targets `make <target>` is resolved against; "" if the
# repo has no makefile, which switches that check off.
MAKEFILE = ""
# Sibling checkouts whose files this repo's documents cite. They are
# resolved for real whenever present, and their absence stops the run
# rather than degrading it, the checker's sibling policy. [] to disable.
SIBLING_ROOTS = ["../ox-arrays", "../orthotope",
                 # and ~/slop's shared tools and documents
                 "../tools", "../docs"]
# The shared tools, whose flags the documents name as another tool's.
FLAG_ROOTS = ["../tools"]
ALLOW_FILE = "tools/doc-refs-allow.txt"
# --self-test rows: one scratch document exercising every branch against
# this repo's real tree and siblings, with the expected verdicts beside
# it. Repo-specific like the rest of this block; the checker is not.
SELF_TEST_DOC = """\
`src/HordeAd/Core/NoSuchModule.hs` is unresolved local drift, and
`cabal test noSuchSuite` an unknown target; `HordeAd.Core.NoSuch` is a
missing module of our namespace and `../ox-arrays/no/such/file.hs` is
missing in a live sibling: all four must fail, as must the
wrapped-span row below.
`--noSuchFlag` is listed, never failed, while `--restamp` is external,
another tool's, and so is `--allocation-only`, a tool's in this tree;
`+noSuchFlag` stays unclassified.
A span the formatter wrapped, `two words
across a break`, must not hide `src/HordeAd/Core/NoSuchTwin.hs`, which
fails like the first path.
`Arith/Internal.hs` and `Data.Array.Strided.Arith` resolve in a
sibling, by path and by module name.
`Core/Ast.hs` and `bench/ConvVjpBench.hs` and `cabal test minimalTest`
and `cabal build all` and `HordeAd.Core.Ops` and `HordeAd.ADEngine` and
`+with_expensive_assertions` are passing controls.
`Core/Ops.hs:297,1581` and `Core/Ops.hs:297` and `Core/Ops.hs:297-320`
are pass 1's to check, while the malformed `Core/Ops.hs:297,` stays
unclassified, which keeps the comma form from being a blanket accept.
`GHC.TypeLits` and `X.replicate` are upgrade-only, unclassified.
`blob/master` and `group/bench` and `tests` are prose;
`.../ghc-9.12/...` is an elision, not a sibling path;
`https://example.com/a/b.md` and `https://hackage.haskell.org/` are
URLs. None of these may be read as a path.
A tilde block showing a backtick fence must close only on a tilde fence:
~~~
```
~~~
so this prose line, cabal test noSuchProseSuite, is not a command, while
a block after it still is:
```
cabal test noSuchFencedSuite
```
`../no-such-checkout/tools/t.py` names a checkout nobody configured:
outside the repo, not checked.
An indented fence line is code, not a fence:

    ```

so this prose line, cabal test noSuchIndentedSuite, is not a command.
"""
SELF_TEST_FAILURES = 6
SELF_TEST_FAIL = ["NoSuchModule.hs", "NoSuchTwin.hs", "noSuchSuite",
                  "HordeAd.Core.NoSuch", "../ox-arrays/no/such/file.hs",
                  "noSuchFencedSuite"]
# Prose that a fence of the wrong kind once turned into command text: in no
# FAIL, ok or allow line.
SELF_TEST_PROSE = ["noSuchProseSuite", "noSuchIndentedSuite"]
# A ../ path into a checkout SIBLING_ROOTS does not name: reported with the
# `~` and `/` ones, never resolved against what happens to be mounted.
SELF_TEST_EXTERNAL = ["../no-such-checkout/tools/t.py"]
SELF_TEST_OK = ["Core/Ast.hs", "bench/ConvVjpBench.hs", "minimalTest",
                "target cabal all",
                "Arith/Internal.hs", "Data.Array.Strided.Arith",
                "HordeAd.Core.Ops", "HordeAd.ADEngine",
                "with_expensive_assertions", "--restamp", "--allocation-only"]
# Citation shapes pass 1 owns: skipped here, in no bucket and no row.
SELF_TEST_SKIPPED = ["Core/Ops.hs:297,1581", "Core/Ops.hs:297",
                     "Core/Ops.hs:297-320"]
SELF_TEST_UNCLASSIFIED = ["+noSuchFlag", "Core/Ops.hs:297,", "GHC.TypeLits",
                          "X.replicate", "blob/master", "group/bench",
                          "tests", ".../ghc-9.12/...",
                          "https://example.com/a/b.md",
                          "https://hackage.haskell.org/"]
# The one local-drift row that must degrade to SKIP with the siblings
# off, and the failure count that survives the degradation.
SELF_TEST_DEGRADED_FAILURES = 3
SELF_TEST_DEGRADED_SKIP = "src/HordeAd/Core/NoSuchModule.hs"
