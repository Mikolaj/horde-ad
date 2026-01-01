#!/usr/bin/env bash

cat <<'EOF'
module Data.Array.Nested.Trace (
  -- * Traced variants
  module Data.Array.Nested.Trace,

  -- * Re-exports from the plain "Data.Array.Nested" module
EOF

sed -n '/^module/,/^) where/!d; /^\s*--\( \|$\)/d; s/ \b[a-z][a-zA-Z0-9_'"'"']*,//g; /^ $/d; s/(\.\., Z.., ([^)]*))/(..)/g; /^ /p; /^$/p' src/Data/Array/Nested.hs

cat <<'EOF'
) where

import Prelude hiding (mappend, mconcat)

import Data.Array.Nested
import Data.Array.Nested.Trace.TH


EOF

# shellcheck disable=SC2016  # dollar in single-quoted string
echo '$(concat <$> mapM convertFun'
sed -n '/^module/,/^) where/!d; /^\s*-- /d; /^ /p' src/Data/Array/Nested.hs |
  grep -o '\b[a-z][a-zA-Z0-9_'"'"']*\b' |
  grep -wv -e 'pattern' -e 'type' |
  tr $'\n' ' ' |
  sed 's/\([^ ]\+\)/'"'"'\1,/g; s/, $/])/; s/^/    [/'
echo
