"""Settings for ~/slop/tools/check-plan-citations.py in this repository, read by its
common.repo_config: the block that stood at the head of the checker while it
lived in this repository's tools/, and which says what each setting does.
"""

SEARCH_ROOTS = ["src", "test", "bench", "example", "tools", ".github", "."]
# The ref a pinned commit has to be reachable from to count as published.
# `git show` is an object-database lookup with no reachability requirement,
# so without this a link or stamp naming an unpushed or squashed-away
# commit resolves here and nowhere else.
PUBLISHED_REF = "origin/master"
# Permalinks into another repository that a local clone can check, keyed by
# the URL up to the commit: the clone's path from the root. A commit there
# counts as published when one of the clone's remote-tracking refs holds it.
FOREIGN = {"https://gitlab.haskell.org/ghc/ghc/-/blob/": "../ghc"}
