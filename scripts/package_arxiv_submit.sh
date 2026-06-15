#!/usr/bin/env bash
# Build arxiv_with_includes.tex and zip everything arXiv needs to compile it.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

TEX="arxiv_with_includes.tex"
FIGURE="figures/nose.png"
LISTINGS_DIR="build/arxiv-tex-listings"
OUT_DIR="dist"
ZIP="${OUT_DIR}/arxiv_with_includes_submit.zip"

echo "==> Regenerating TeX and Lean listing files"
./scripts/build_arxiv_with_includes_tex.sh

missing=0
if [[ ! -f "$TEX" ]]; then
  echo "error: missing $TEX" >&2
  missing=1
fi
if [[ ! -f "$FIGURE" ]]; then
  echo "error: missing $FIGURE" >&2
  missing=1
fi
if [[ ! -d "$LISTINGS_DIR" ]]; then
  echo "error: missing $LISTINGS_DIR" >&2
  missing=1
fi
lean_count="$(find "$LISTINGS_DIR" -maxdepth 1 -name '*.lean' 2>/dev/null | wc -l)"
if [[ "$lean_count" -eq 0 ]]; then
  echo "error: no .lean files in $LISTINGS_DIR" >&2
  missing=1
fi
if [[ "$missing" -ne 0 ]]; then
  exit 1
fi

mkdir -p "$OUT_DIR"
rm -f "$ZIP"

echo "==> Packaging (paths relative to $TEX)"
zip -r "$ZIP" \
  "$TEX" \
  "$FIGURE" \
  "$LISTINGS_DIR"/*.lean

echo "wrote $ZIP ($(du -h "$ZIP" | cut -f1))"
echo "Contents:"
zipinfo -1 "$ZIP" | sed 's/^/  /'
echo
echo "Upload $ZIP to arXiv. Compile with LuaLaTeX (pdfLaTeX may run out of memory)."
