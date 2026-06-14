#!/usr/bin/env python3
"""Render TR1995-711 Figure 1: the average-case complexity "nose" diagram."""

from __future__ import annotations

from pathlib import Path

import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "figures" / "nose.png"


def main() -> None:
    fig, ax = plt.subplots(figsize=(8, 6), dpi=150)

    # Abstract axes: average-case T (horizontal), worst-case V (vertical).
    t = np.linspace(0.4, 10, 400)

    y_n = 1.6
    y_pol = 8.2
    # Monotone boundary V = h(T) rising with T (schematic).
    y_h = 2.2 + 0.55 * np.log1p(t - 0.3)

    # Reference horizontals (N, h(T), Pol on V axis).
    ax.axhline(y_n, color="#555555", linewidth=1.0, linestyle="-")
    ax.plot(t, y_h, color="#555555", linewidth=1.0, linestyle="-")
    ax.axhline(y_pol, color="#555555", linewidth=1.0, linestyle="-")

    ax.text(-0.15, y_n, "N", ha="right", va="center", fontsize=11)
    ax.text(-0.15, 4.8, r"$h(T)$", ha="right", va="center", fontsize=11)
    ax.text(-0.15, y_pol, "Pol", ha="right", va="center", fontsize=11)

    # Vertical guides at T = N / Pol boundaries.
    t_n_pol = 2.8
    t_pol_end = 6.5
    ax.axvline(t_n_pol, color="#cccccc", linewidth=0.8, linestyle=":")
    ax.axvline(t_pol_end, color="#cccccc", linewidth=0.8, linestyle=":")

    ax.text(1.4, -0.55, "N", ha="center", va="top", fontsize=11)
    ax.text(t_n_pol, -0.55, "Pol", ha="center", va="top", fontsize=11)
    ax.text(t_pol_end, -0.55, "Pol", ha="center", va="top", fontsize=11)

    # Language curves L1–L4 (worst-case vs average-case, schematic).
    curves = [
        (1.15, 0.95, "L1", "#1f77b4"),
        (1.45, 1.05, "L2", "#ff7f0e"),
        (1.85, 1.15, "L3", "#2ca02c"),
        (2.35, 1.25, "L4", "#d62728"),
    ]
    for a, b, label, color in curves:
        v = a + b * np.log1p(t)
        ax.plot(t, v, color=color, linewidth=1.8, label=label)
        ax.text(t[-1] + 0.08, v[-1], label, color=color, fontsize=11, va="center")

    # Nose region: tractable (Pol, Pol) pocket under h(T), above N.
    t_nose = np.linspace(t_n_pol, t_pol_end, 200)
    nose_top = 2.2 + 0.55 * np.log1p(t_nose - 0.3)
    nose_top = np.minimum(nose_top, y_pol - 0.35)
    nose_bottom = np.full_like(t_nose, y_n + 0.15)
    ax.fill_between(
        t_nose,
        nose_bottom,
        nose_top,
        color="#c8daf5",
        alpha=0.85,
        linewidth=0,
        zorder=0,
    )
    # Nose outline (schematic bump from the original figure).
    t_outline = np.linspace(t_n_pol, t_pol_end, 200)
    outline_top = 2.0 + 0.48 * np.log1p(t_outline - 0.2)
    outline_top = np.clip(outline_top, y_n + 0.2, y_pol - 0.5)
    ax.plot(t_outline, outline_top, color="#4a6fa5", linewidth=1.5)
    ax.plot(
        [t_n_pol, t_pol_end],
        [y_n + 0.15, y_n + 0.15],
        color="#4a6fa5",
        linewidth=1.5,
    )

    nose_x, nose_y = 4.6, 3.35
    ax.plot(nose_x, nose_y, marker="*", markersize=14, color="#c0392b", zorder=5)
    ax.text(nose_x + 0.25, nose_y, "Nose", fontsize=12, fontweight="bold", va="center")

    ax.set_xlim(0, 10.8)
    ax.set_ylim(-0.9, 9.5)
    ax.set_xlabel("Average-Case Complexity ($T$)", fontsize=12)
    ax.set_ylabel("Worst-Case Complexity ($V$)", fontsize=12)
    ax.set_title(
        'The "Nose" of Average-Case Tractability (TR1995-711, Figure 1)',
        fontsize=13,
        pad=12,
    )
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)
    ax.set_xticks([])
    ax.set_yticks([])

    patch = mpatches.Patch(facecolor="#c8daf5", edgecolor="#4a6fa5", label="Nose region")
    ax.legend(handles=[patch], loc="upper left", framealpha=0.9)

    OUT.parent.mkdir(parents=True, exist_ok=True)
    fig.tight_layout()
    fig.savefig(OUT, bbox_inches="tight", facecolor="white")
    plt.close(fig)
    print(f"Wrote {OUT}")


if __name__ == "__main__":
    main()
