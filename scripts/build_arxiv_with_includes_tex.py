#!/usr/bin/env python3
"""Convert arxiv_with_includes.md to arxiv_with_includes.tex (icon2lean-style)."""

from __future__ import annotations

import re
import subprocess
import sys
import textwrap
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "arxiv_with_includes.md"
OUT = ROOT / "arxiv_with_includes.tex"
PREAMBLE = Path(__file__).resolve().parent / "tex_preamble.tex"
LISTINGS_DIR = ROOT / "build" / "arxiv-tex-listings"

PORTABLE_RE = re.compile(
    r"^> \*\*Portable edition:\*\*.*?(?:\n(?!\n|\#).*)*\n\n",
    re.MULTILINE,
)
GITHUB_INLINE_MATH = re.compile(r"\$`([^`\n]+?)`\$")
HTML_COMMENT = re.compile(r"<!--.*?-->", re.DOTALL)
FENCE_RE = re.compile(r"^```([^\n]*)\n(.*?)^```\s*$", re.MULTILINE | re.DOTALL)
LEAN_HEADER_RE = re.compile(
    r"^###\s+(AvgCaseMls/[^\s{]+(?:\{#[^}]+\})?)\s*$", re.MULTILINE
)


def strip_portable_edition(text: str) -> str:
    return PORTABLE_RE.sub("", text, count=1)


def github_math_to_tex(text: str) -> str:
    return GITHUB_INLINE_MATH.sub(r"$\1$", text)


def strip_html_comments(text: str) -> str:
    return HTML_COMMENT.sub("", text)


def extract_title(text: str) -> tuple[str, str]:
    lines = text.splitlines()
    if lines and lines[0].startswith("# "):
        title = lines[0][2:].strip()
        body = "\n".join(lines[1:]).lstrip("\n")
        return title, body
    return "Untitled", text


def escape_latex(text: str) -> str:
    replacements = [
        ("\\", r"\textbackslash{}"),
        ("&", r"\&"),
        ("%", r"\%"),
        ("$", r"\$"),
        ("#", r"\#"),
        ("_", r"\_"),
        ("{", r"\{"),
        ("}", r"\}"),
        ("~", r"\textasciitilde{}"),
        ("^", r"\textasciicaret{}"),
    ]
    out = text
    for old, new in replacements:
        out = out.replace(old, new)
    return out


def lean_block_latex(title: str | None, code: str, listing_name: str) -> str:
    LISTINGS_DIR.mkdir(parents=True, exist_ok=True)
    listing_path = LISTINGS_DIR / listing_name
    listing_path.write_text(code.rstrip("\n") + "\n", encoding="utf-8")
    rel_path = listing_path.relative_to(ROOT).as_posix()
    parts: list[str] = []
    if title:
        parts.append(f"\\noindent\\textbf{{{escape_latex(title)}}}\n\n")
    parts.append("\\begin{leancertbox}\n")
    parts.append(f"\\lstinputlisting[style=leanbox]{{{rel_path}}}\n")
    parts.append("\\end{leancertbox}\n\n")
    return "".join(parts)


def extract_lean_titles(text: str) -> dict[str, str]:
    """Map placeholder ids to module titles appearing immediately before ```lean fences."""
    titles: dict[str, str] = {}
    lean_starts = [m.start() for m in re.finditer(r"^```lean\s*$", text, re.MULTILINE)]
    for idx, pos in enumerate(lean_starts):
        prefix = text[:pos].rstrip("\n")
        header_match = None
        for line in reversed(prefix.splitlines()[-4:]):
            m = re.match(r"^###\s+(AvgCaseMls/[^\s{]+)", line.strip())
            if m:
                header_match = m.group(1)
                break
        titles[f"LEANINCLUDE{idx:03d}"] = header_match or f"Lean module {idx + 1}"
    return titles


def replace_fences(text: str) -> tuple[str, dict[str, str]]:
    lean_titles = extract_lean_titles(text)
    placeholders: dict[str, str] = {}
    lean_idx = 0
    math_idx = 0

    def repl(match: re.Match[str]) -> str:
        nonlocal lean_idx, math_idx
        lang = match.group(1).strip().lower()
        body = match.group(2)
        if lang == "lean":
            key = f"LEANINCLUDE{lean_idx:03d}"
            lean_idx += 1
            module = lean_titles.get(key, f"module-{lean_idx}.lean")
            safe_name = module.replace("/", "-")
            placeholders[key] = lean_block_latex(
                module if module.startswith("AvgCaseMls/") else None,
                body,
                safe_name,
            )
            return f"\n\n{key}\n\n"
        if lang == "math":
            key = f"MATHINCLUDE{math_idx:03d}"
            math_idx += 1
            placeholders[key] = f"\\[\n{body.strip()}\n\\]\n"
            return f"\n\n{key}\n\n"
        if lang:
            key = f"CODEINCLUDE{lang.upper()}{math_idx:03d}"
            math_idx += 1
            placeholders[key] = (
                f"\\begin{{verbatim}}\n{body.rstrip()}\n\\end{{verbatim}}\n"
            )
            return f"\n\n{key}\n\n"
        key = f"CODEINCLUDE{math_idx:03d}"
        math_idx += 1
        placeholders[key] = f"\\begin{{verbatim}}\n{body.rstrip()}\n\\end{{verbatim}}\n"
        return f"\n\n{key}\n\n"

    converted = FENCE_RE.sub(repl, text)
    return converted, placeholders


def pandoc_to_latex(markdown: str) -> str:
    proc = subprocess.run(
        [
            "pandoc",
            "-f",
            "markdown+tex_math_dollars+raw_tex+smart",
            "-t",
            "latex",
            "--wrap=none",
        ],
        input=markdown,
        text=True,
        capture_output=True,
        check=False,
    )
    if proc.returncode != 0:
        print(proc.stderr, file=sys.stderr)
        raise RuntimeError("pandoc failed")
    return proc.stdout


def inject_placeholders(latex: str, placeholders: dict[str, str]) -> str:
    out = latex
    for key, value in placeholders.items():
        # Pandoc may wrap bare lines in \emph{} or leave them as paragraphs.
        patterns = [
            key,
            f"\\emph{{{key}}}",
            f"\\text{{{key}}}",
            f"\\passthrough{{\\lstinline!{key}!}}",
        ]
        for pat in patterns:
            if pat in out:
                out = out.replace(pat, value)
                break
        else:
            out = out.replace(key, value)
    return out


def cleanup_pandoc_latex(latex: str) -> str:
    latex = latex.replace("\\pandocbounded{", "{")
    latex = re.sub(r"\\tightlist\n", "", latex)
    latex = latex.replace(
        "build the portable \\texttt{arxiv\\_with\\_includes.md} pipeline",
        "build the \\texttt{arxiv\\_with\\_includes.md} pipeline",
    )
    latex = re.sub(r"\n{3,}", "\n\n", latex)
    return latex


def build_title_page(title: str) -> str:
    abstract = textwrap.dedent(
        """
        We describe a Lean~4 formalization revisiting NYU Courant Technical Report TR1995-711
        on the average-case complexity of Multilevel Syllogistic (MLS). The development encodes
        Reischuk--Schindelhauer average-case classes, an axiomatic MLS/EMLS semantics layer, a
        partial Ferro--Omodeo--Schwartz decision procedure with proved soundness and partial
        completeness on a membership-free fragment, serialization and step budgets, and
        conditional NP-average completeness and non-AvP hardness corollaries modulo explicitly
        documented structural axioms. Full Lean sources are inlined in the appendix modules.
        """
    ).strip()
    return textwrap.dedent(
        f"""
        \\title{{\\textbf{{{escape_latex(title)}}}}}

        \\author[1]{{\\textbf{{Lars Warren Ericson}}}}
        \\affil[1]{{Catskills Research Company}}
        \\affil[1]{{\\texttt{{lars.ericson@catskillsresearch.com}}}}

        \\date{{\\today}}

        \\begin{{document}}

        \\maketitle

        \\begin{{center}}
          \\small
          \\textbf{{ORCID:}} 0000-0001-8299-9361 \\\\
          \\textbf{{Primary Category:}} cs.LO (Logic in Computer Science) \\\\
          \\textbf{{Secondary Category:}} cs.CC (Computational Complexity) \\\\[0.5em]
          \\textbf{{Lean~4 formalization:}} \\url{{https://github.com/catskillsresearch/avg\\_case\\_mls}}
        \\end{{center}}

        \\begin{{abstract}}
        {abstract}
        \\end{{abstract}}
        """
    ).strip()


def main() -> int:
    if not SRC.is_file():
        print(f"error: missing {SRC}", file=sys.stderr)
        return 1
    if not PREAMBLE.is_file():
        print(f"error: missing {PREAMBLE}", file=sys.stderr)
        return 1

    if LISTINGS_DIR.exists():
        for path in LISTINGS_DIR.glob("*.lean"):
            path.unlink()
    LISTINGS_DIR.mkdir(parents=True, exist_ok=True)

    raw = SRC.read_text(encoding="utf-8")
    raw = strip_portable_edition(raw)
    title, body = extract_title(raw)
    body = strip_html_comments(body)
    body = github_math_to_tex(body)
    body, placeholders = replace_fences(body)
    latex_body = pandoc_to_latex(body)
    latex_body = inject_placeholders(latex_body, placeholders)
    latex_body = cleanup_pandoc_latex(latex_body)

    preamble = PREAMBLE.read_text(encoding="utf-8")
    title_page = build_title_page(title)
    document = (
        preamble
        + "\n\n"
        + title_page
        + "\n\n"
        + latex_body
        + "\n\n\\end{document}\n"
    )
    OUT.write_text(document, encoding="utf-8")
    print(f"wrote {OUT.relative_to(ROOT)} ({OUT.stat().st_size:,} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
