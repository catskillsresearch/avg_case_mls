#!/usr/bin/env python3
"""Adjust arxiv.md math delimiters for reliable GitHub rendering."""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MD = ROOT / "arxiv.md"


def split_fences(text: str) -> list[tuple[str, str]]:
    """Split into (kind, segment) where kind is 'fence' or 'text'."""
    parts: list[tuple[str, str]] = []
    pattern = re.compile(r"^```.*?^```", re.MULTILINE | re.DOTALL)
    last = 0
    for m in pattern.finditer(text):
        if m.start() > last:
            parts.append(("text", text[last : m.start()]))
        parts.append(("fence", m.group(0)))
        last = m.end()
    if last < len(text):
        parts.append(("text", text[last:]))
    return parts


def display_to_math_block(segment: str) -> str:
    def repl(m: re.Match[str]) -> str:
        body = m.group(1).strip()
        return f"\n\n```math\n{body}\n```\n\n"

    return re.sub(
        r"^\s*\$\$(.+?)\$\$\s*$",
        repl,
        segment,
        flags=re.MULTILINE | re.DOTALL,
    )


def inline_to_github(segment: str) -> str:
    """Wrap inline math in GitHub's `$`...`$` form (required for many LaTeX constructs)."""

    def repl(m: re.Match[str]) -> str:
        inner = m.group(1)
        if inner.startswith("`") and inner.endswith("`"):
            return m.group(0)
        if "`" in inner:
            return m.group(0)
        return f"$`{inner}`$"

    return re.sub(r"(?<!\$)\$([^$\n]+?)\$(?!\$)", repl, segment)


def main() -> None:
    text = MD.read_text(encoding="utf-8")
    out: list[str] = []
    for kind, segment in split_fences(text):
        if kind == "fence":
            out.append(segment)
        else:
            segment = display_to_math_block(segment)
            segment = inline_to_github(segment)
            out.append(segment)
    result = "".join(out)
    # Collapse runs of 4+ newlines to 3
    result = re.sub(r"\n{4,}", "\n\n\n", result)
    MD.write_text(result, encoding="utf-8")
    print(f"Updated {MD}")


if __name__ == "__main__":
    main()
