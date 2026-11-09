#!/usr/bin/env bash
# Build "Introduction to Dyn" and render it to _out/html-multi/, one page per top-level
# section, or with --single to _out/html-single/, then make the output work offline and
# from file:// (scripts/postprocess.py).
# Usage: ./generate.sh [--single]
# LEAN_WRAPPER, if set, is a command to run each `lake` invocation under, such as a script
# that caps its memory.
# Theme files under themes/ are read when the document is rendered, so CSS and JavaScript
# edits need only a re-run. Widget files under widgets/ are compiled in: edit, then re-run.
set -euo pipefail
cd "$(dirname "$0")"
wrap=()
if [ -n "${LEAN_WRAPPER:-}" ]; then wrap=("$LEAN_WRAPPER"); fi
mode=html-multi; flag=()
if [ "${1:-}" = "--single" ]; then mode=html-single; flag=(--single); fi

python3 -I scripts/export-data.py --check
# widgets/* are read with include_str, which Lake does not track, and Lake compares content
# hashes, not times: when a widget file is newer than the module that includes them, delete
# that module's trace so Lake rebuilds it.
for f in widgets/*; do
  if [ "$f" -nt .lake/build/lib/lean/DynIntro/Blocks.olean ] 2>/dev/null; then
    rm -f .lake/build/lib/lean/DynIntro/Blocks.trace; break
  fi
done
${wrap[@]+"${wrap[@]}"} lake build dynintro
rm -rf "_out/$mode"
${wrap[@]+"${wrap[@]}"} lake exe dynintro ${flag[@]+"${flag[@]}"} --output _out
python3 -I scripts/postprocess.py "_out/$mode"
echo "Open: file://$PWD/_out/$mode/index.html"
