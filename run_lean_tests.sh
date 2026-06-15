#!/usr/bin/env bash
# Print #eval / #print axioms results from AvgCaseMls.Tests.
set -euo pipefail
cd "$(dirname "$0")"
lake build AvgCaseMls.Tests 2>&1 | grep -E "^info: AvgCaseMls/Tests|depends on axioms"
