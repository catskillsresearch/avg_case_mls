#!/usr/bin/env python3
"""Expand arxiv.md into a portable arxiv_with_includes.md with full Lean sources."""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "arxiv.md"
OUT = ROOT / "arxiv_with_includes.md"
LEAN_DIR = ROOT / "AvgCaseMls"

INCLUDE_MARKER = re.compile(r"<!--\s*include-lean:\s*([^\s>]+)\s*-->")
LINK_RE = re.compile(r"\[([^\]]+)\]\(([^)]+\.lean)\)")
INLINE_LEAN_RE = re.compile(r"`(AvgCaseMls/[^`]+\.lean)`")
STUB_FENCE_RE = re.compile(
    r"<!--\s*include-lean:\s*([^\s>]+)\s*-->\s*\n\n```lean\n.*?\n```\n",
    re.DOTALL,
)


def slug(path: str) -> str:
    return path.lower().replace("/", "-").replace(".", "-").replace("_", "-")


def lean_ref(rel_path: str) -> str:
    return f"[{rel_path}](#{slug(rel_path)})"


def replace_lean_links(text: str) -> str:
    def replace_link(match: re.Match[str]) -> str:
        label, rel_path = match.group(1), match.group(2)
        bare = label.strip("`")
        if bare == rel_path or bare.endswith(".lean") or rel_path.endswith(bare):
            return lean_ref(rel_path)
        return f"`{bare}` ({lean_ref(rel_path)})"

    text = LINK_RE.sub(replace_link, text)
    return INLINE_LEAN_RE.sub(lambda m: lean_ref(m.group(1)), text)


def sanitize_lean_source(text: str) -> str:
    """Remove markdown file links inside Lean sources (doc comments)."""
    return LINK_RE.sub(lambda m: f"`{m.group(2)}`", text)


def read_lean(rel_path: str) -> str:
    path = ROOT / rel_path
    if not path.is_file():
        raise FileNotFoundError(f"Lean file not found: {path}")
    return sanitize_lean_source(path.read_text())


def lean_block(rel_path: str, content: str) -> str:
    anchor = slug(rel_path)
    return (
        f"### {rel_path} {{#{anchor}}}\n\n"
        f"```lean\n{content.rstrip()}\n```\n\n"
    )


def expand_includes(text: str) -> tuple[str, set[str]]:
    included: set[str] = set()

    def expand(rel_path: str) -> str:
        included.add(rel_path)
        return lean_block(rel_path, read_lean(rel_path))

    def replace_stub(match: re.Match[str]) -> str:
        return expand(match.group(1))

    text = STUB_FENCE_RE.sub(replace_stub, text)

    def replace_bare_marker(match: re.Match[str]) -> str:
        return expand(match.group(1))

    text = INCLUDE_MARKER.sub(replace_bare_marker, text)
    return text, included


def normalize_lean_path(rel_path: str) -> str | None:
    if rel_path.startswith("AvgCaseMls/"):
        return rel_path
    if rel_path.endswith(".lean") and "/" not in rel_path:
        candidate = f"AvgCaseMls/{rel_path}"
        if (ROOT / candidate).is_file():
            return candidate
    return None


def lean_paths_in_line(line: str) -> list[str]:
    paths: list[str] = []
    for match in LINK_RE.finditer(line):
        rel_path = normalize_lean_path(match.group(2))
        if rel_path is not None:
            paths.append(rel_path)
    return paths


def inject_at_first_link(text: str, included: set[str]) -> str:
    """Insert full Lean sources immediately after the first markdown link to each module."""
    lines = text.split("\n")
    out: list[str] = []
    for line in lines:
        out.append(line)
        pending: list[str] = []
        for rel_path in lean_paths_in_line(line):
            if rel_path in included:
                continue
            included.add(rel_path)
            pending.append(lean_block(rel_path, read_lean(rel_path)).rstrip())
        if pending:
            out.append("")
            out.extend(pending)
    return "\n".join(out)


def main() -> int:
    if not SRC.is_file():
        print(f"error: missing {SRC}", file=sys.stderr)
        return 1

    body, included = expand_includes(SRC.read_text())
    body = inject_at_first_link(body, included)
    body = replace_lean_links(body)

    OUT.write_text(body.rstrip() + "\n")
    print(f"wrote {OUT.relative_to(ROOT)} ({OUT.stat().st_size:,} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
