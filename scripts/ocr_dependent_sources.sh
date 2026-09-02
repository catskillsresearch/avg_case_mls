#!/usr/bin/env bash
# OCR the five TR1995-711 dependency papers in sources/ (TR1995-711 itself is separate).
#
# Expected PDFs (download into sources/ before running):
#   RS93.pdf   — Reischuk & Schindelhauer, STACS 1993 (Theorems 4.1–4.4, Example 4.1)
#   CS87.pdf   — Chvatal & Szemeredi, resolution hardness (Theorems 3.1–3.2)
#   COP90.pdf  — Cantone, Omodeo & Policriti, JAR 1990 (Theorem 5.1, Cor 5.2)
#   Gur91.pdf  — Gurevich, JCSS 1991 (Theorem 4.3 padding consequence)
#   Lev86.pdf  — Levin, SIAM 1986 (foundations for Theorem 4.2)
#
# Usage (from repo root):
#   bash scripts/ocr_dependent_sources.sh              # full OCR, all five
#   bash scripts/ocr_dependent_sources.sh --pages 1-2  # smoke test first pages
#   bash scripts/ocr_dependent_sources.sh --status     # resume state only
#   bash scripts/ocr_dependent_sources.sh --png-only   # render PNGs, no API calls
#   bash scripts/ocr_dependent_sources.sh RS93 CS87    # subset by stem
#
# Requires: pdftoppm, pdfinfo, CURSOR_API_KEY in ../tokens_ssto.yaml
# Outputs:  sources/<stem>_vision.md, sources/pages/<stem>/, sources/ocr_<stem>_run.log
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

PIPELINE="$ROOT/scripts/ocr_pdf_pipeline.sh"
if [[ ! -x "$PIPELINE" ]]; then
  echo "FAIL: missing $PIPELINE" >&2
  exit 1
fi

ALL_STEMS=(RS93 CS87 COP90 Gur91 Lev86)

# Partition args: optional stem filters vs flags forwarded to ocr_pdf_pipeline.py
STEMS=()
EXTRA=()
for arg in "$@"; do
  case "$arg" in
    RS93|CS87|COP90|Gur91|Lev86)
      STEMS+=("$arg")
      ;;
    *)
      EXTRA+=("$arg")
      ;;
  esac
done

if [[ ${#STEMS[@]} -eq 0 ]]; then
  STEMS=("${ALL_STEMS[@]}")
fi

missing=0
for stem in "${STEMS[@]}"; do
  pdf="sources/${stem}.pdf"
  if [[ ! -f "$pdf" ]]; then
    echo "MISSING: $pdf" >&2
    missing=1
  fi
done
if [[ "$missing" -ne 0 ]]; then
  echo "Place PDFs in sources/ with names RS93.pdf, CS87.pdf, COP90.pdf, Gur91.pdf, Lev86.pdf" >&2
  exit 1
fi

echo "ocr_dependent_sources: ${#STEMS[@]} paper(s): ${STEMS[*]}" >&2
if [[ ${#EXTRA[@]} -gt 0 ]]; then
  echo "  forwarded flags: ${EXTRA[*]}" >&2
fi

for stem in "${STEMS[@]}"; do
  pdf="sources/${stem}.pdf"
  echo "========== $stem ($pdf) ==========" >&2
  bash "$PIPELINE" "$pdf" "${EXTRA[@]}"
done

echo "ocr_dependent_sources: done." >&2
