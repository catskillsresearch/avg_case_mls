#!/usr/bin/env python3
"""ASCII sanitization for Lean sources included via listings on arXiv (pdfLaTeX)."""

from __future__ import annotations

# Order matters: longer / composite replacements first where needed.
LEAN_UNICODE_REPLACEMENTS: tuple[tuple[str, str], ...] = (
    ("§", "S"),
    ("¬", "not "),
    ("·", "*"),
    ("⁻", "-"),
    ("¹", "1"),
    ("₀", "_0"),
    ("₁", "_1"),
    ("₂", "_2"),
    ("×", "x"),
    ("α", "a"),
    ("μ", "mu"),
    ("–", "-"),
    ("—", "-"),
    ("→", "->"),
    ("←", "<-"),
    ("↔", "<->"),
    ("∀", "forall"),
    ("∃", "exists"),
    ("∅", "empty"),
    ("∈", "in"),
    ("∉", "notin"),
    ("∑", "sum"),
    ("∧", "/\\"),
    ("∨", "\\/"),
    ("∪", "union"),
    ("≠", "/="),
    ("≤", "<="),
    ("≥", ">="),
    ("⊢", "|-"),
    ("◇", "op"),
    ("⟨", "<"),
    ("⟩", ">"),
    ("ℤ", "Int"),
)


def sanitize_lean_for_arxiv(text: str) -> str:
    out = text
    for src, dst in LEAN_UNICODE_REPLACEMENTS:
        out = out.replace(src, dst)
    # Drop any remaining non-ASCII (comments / docstrings) rather than break pdfLaTeX.
    return "".join(ch if ord(ch) < 128 else "?" for ch in out)


def chunk_line_ranges(line_count: int, chunk_size: int = 350) -> list[tuple[int, int]]:
    if line_count <= chunk_size:
        return [(1, line_count)]
    ranges: list[tuple[int, int]] = []
    start = 1
    while start <= line_count:
        end = min(start + chunk_size - 1, line_count)
        ranges.append((start, end))
        start = end + 1
    return ranges
