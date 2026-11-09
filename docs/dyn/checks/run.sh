#!/usr/bin/env bash
# Elaborate the guide's Lean checks against the package, which must be built: by default the
# one three directories up, or DYN_PACKAGE, a built checkout of the same sources.  Each check
# pins its output with `#guard_msgs`, or reports a text of data/ that differs as an error, so
# any message is a failure.
# Usage: checks/run.sh
# LEAN_WRAPPER, if set, is a command to run each `lake` invocation under, as for generate.sh.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
pkg="${DYN_PACKAGE:-$(cd "$here/../../.." && pwd)}"
wrap=()
if [ -n "${LEAN_WRAPPER:-}" ]; then wrap=("$LEAN_WRAPPER"); fi
status=0
for f in "$here"/*.lean; do
  out="$(cd "$pkg" && ${wrap[@]+"${wrap[@]}"} lake env lean "$f" 2>&1)" || true
  if [ -n "$out" ]; then
    echo "checks: $(basename "$f") failed:"; echo "$out"; status=1
  else
    echo "checks: $(basename "$f") passes"
  fi
done
exit $status
