#!/usr/bin/env bash
# Check every gist displayed in arxiv.md.
#
# Each gist must typecheck on its own, importing only from AvgCaseMls, so that
# a reader can copy one out of the paper and run it without pulling in the
# others.  We therefore check each file independently rather than relying on
# `lake build Gists`, which would let a gist accidentally depend on a sibling.
set -uo pipefail

cd "$(dirname "$0")/.." || exit 1

failed=0
checked=0

for gist in Gists/*.lean; do
  printf '%-46s' "$gist"
  if output=$(lake env lean "$gist" 2>&1); then
    if [[ -n "$output" ]]; then
      echo "WARN"
      echo "$output" | sed 's/^/    /'
    else
      echo "ok"
    fi
  else
    echo "FAIL"
    echo "$output" | sed 's/^/    /'
    failed=$((failed + 1))
  fi
  checked=$((checked + 1))
done

echo
if [[ $failed -eq 0 ]]; then
  echo "All $checked gists check out."
else
  echo "$failed of $checked gists failed."
fi
exit $failed
