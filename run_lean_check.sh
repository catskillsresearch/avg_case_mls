#!/usr/bin/env bash
# Typecheck all Lean modules in this project.
set -euo pipefail
cd "$(dirname "$0")"
lake build
