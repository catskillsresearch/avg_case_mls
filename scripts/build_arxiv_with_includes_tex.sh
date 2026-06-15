#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/build_arxiv_with_includes_tex.py
# Optional: latexmk arxiv_with_includes.tex  (uses .latexmkrc → LuaLaTeX)
