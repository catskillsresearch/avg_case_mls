#!/usr/bin/env bash
# Project-specific mechanical check: protocol holes in Challenge stay sorry.
set -euo pipefail
python3 - <<'PY'
import json
import re
from pathlib import Path

cfg = json.loads(Path("comparator.json").read_text(encoding="utf-8"))
challenge = Path("Challenge.lean").read_text(encoding="utf-8")
holes = list(cfg.get("definition_names", []))
if not holes:
    raise SystemExit("FAIL: comparator.json has no definition_names")

missing = []
for full in holes:
    short = full.rsplit(".", 1)[-1]
    pat = re.compile(
        rf"(?:^|\n)(?:private\s+|protected\s+|noncomputable\s+)?def\s+{re.escape(short)}\b"
        rf"(?:(?!^(?:private\s+|protected\s+|noncomputable\s+)?"
        rf"(?:def|theorem|structure|inductive|abbrev|namespace|end)\b)[\s\S])*?"
        rf":=\s*sorry\b",
        re.MULTILINE,
    )
    if not pat.search(challenge):
        missing.append(full)

if missing:
    raise SystemExit(
        "FAIL: comparator definition holes must be `sorry` in Challenge.lean:\n  "
        + "\n  ".join(missing)
    )
print(f"OK: {len(holes)} Challenge definition holes are sorry-bodied.")
PY
