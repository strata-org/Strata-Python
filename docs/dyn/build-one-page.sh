#!/usr/bin/env bash
# Build the guide as one self-contained HTML file: a single page, with its stylesheets,
# scripts and fonts inlined, so it can be shared as one file or opened from disk.
# Usage: ./build-one-page.sh [OUT]   (default OUT: _out/dyn-intro.html)
# LEAN_WRAPPER is passed on to generate.sh.
set -euo pipefail
cd "$(dirname "$0")"
out="${1:-_out/dyn-intro.html}"
./generate.sh --single
python3 -I scripts/inline.py _out/html-single/index.html "$out"
echo "One page: $out ($(du -h "$out" | cut -f1))"
