#!/usr/bin/env bash
# Print all #eval results from AvgCaseMls.Tests.
set -euo pipefail
cd "$(dirname "$0")"
lake build AvgCaseMls.Tests 2>&1 | grep "^info: AvgCaseMls/Tests"
