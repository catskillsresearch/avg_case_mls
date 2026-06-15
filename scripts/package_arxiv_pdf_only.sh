#!/usr/bin/env bash
# PDF-only arXiv upload when TeX source / Check Files UI is blocked.
# arXiv accepts PDF not generated from their own TeX pipeline (upload your locally built PDF).
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

PDF="arxiv_with_includes.pdf"
OUT_DIR="dist"
ZIP="${OUT_DIR}/arxiv_pdf_only_submit.zip"

if [[ ! -f "$PDF" ]]; then
  echo "==> Building PDF first (pdflatex)"
  ./scripts/build_arxiv_with_includes_tex.sh
  pdflatex -interaction=nonstopmode arxiv_with_includes.tex >/dev/null
  pdflatex -interaction=nonstopmode arxiv_with_includes.tex >/dev/null
fi

mkdir -p "$OUT_DIR"
rm -f "$ZIP"
zip -j "$ZIP" "$PDF"

echo "wrote $ZIP ($(du -h "$ZIP" | cut -f1))"
echo "Upload this zip on Add Files, click Check Files, choose PDF (not TeX) if prompted."
