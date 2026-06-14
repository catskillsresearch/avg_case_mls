# Definition forks (AvCom)

When the literature leaves a choice implicit, we record it here.

## Finite-support `Distribution` (Phase 1A)

**Literature:** TR1995-711 §3.2 defines $\\mu : \\Sigma^* \\to [0,1]$ with $\\sum_x \\mu(x) \\le 1$ over all strings.

**Lean fork:** `Distribution` carries a finite `support : Finset Bitstring`; mass outside support is zero. Rank (Phase 1B) counts only over `support`, not all of $\\Sigma^*$.

**Rationale:** Executable tests and finite `Finset` sums; avoids noncomputability over infinite domains.

## `lenBot` vs `len` (Phase 1A)

**Literature:** RS93 rank-sum uses $1/|x|$ in denominators.

**Lean fork:** `lenBot s := max 1 (len s)` so the empty bitstring is not a division-by-zero edge case in `IsAvTime`.

**Rationale:** Standard technical fix; does not change behavior on nonempty inputs.
