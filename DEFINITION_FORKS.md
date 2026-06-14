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

## `rank` over finite `support` (Phase 1B)

**Literature:** $\\text{rank}_\\mu(x) = |\\{ z \\in \\Sigma^* : \\mu(z) \\ge \\mu(x) \\}|$, with rank $0$ when $\\mu(x)=0$.

**Lean fork:** Count only over `μ.support` via `(μ.support.filter (fun z => μ.prob x ≤ μ.prob z)).card`. Real comparisons are classical (`noncomputable`).

**Rationale:** Matches the finite-support distribution convention; avoids counting over all of $\\Sigma^*$.

## `T_inv` by partial search (Phase 1B)

**Literature:** $T^{-1}(m) = \\min\\{ n \\mid T(n) \\ge m \\}$.

**Lean fork:** `partial def T_invAux` searches from `n = 0` for `m > 0`; `T_inv T 0 := 0` by convention (matches `min {n | T n ≥ 0} = 0` when `T 0 ≥ 0`). If no such `n` exists for `m > 0`, evaluation may diverge.

**Rationale:** Keeps the definition executable for typical polynomial bounds used in the proof program; a total classical inverse can be added later if needed.

## `IsAvTime` uses `rankLe` (Phase 1C)

**Literature:** RS93 sums over $\\{ x : \\text{rank}_\\mu(x) \\le \\ell \\}$.

**Lean fork:** Sum over `rankLe μ l := μ.support.filter (rank μ · ≤ l)` rather than an arbitrary `Finset` with the same membership (equivalent for verifying the inequality on finite support).

**Rationale:** Canonical witness; aligns the Lean definition with the paper's rank shell.

## `DistTime` without a decider (Phase 1C)

**Literature:** $\\text{DistTime}(T)$ requires a deterministic algorithm $M$ deciding $L$ with $(f_M, \\mu) \\in \\text{Av}(T)$.

**Lean fork:** `DistTime T prob := ∃ f, IsAvTime T f prob.μ` — existence of a running-time witness only; no link to `prob.L` yet.

**Rationale:** No Turing-machine layer in Mathlib at this stage; decider linkage is Phase 1D / future infrastructure.

## POL-rankable (Phase 1C)

**Literature:** POL-rankable requires a polynomial bound on rank **and** polynomial-time computability of $\\text{rank}_\\mu$.

**Lean fork:** `IsPolRankable μ := ∃ V ∈ POL, IsTRankable V μ` — computability of rank omitted until a model is chosen.

**Rationale:** Separates the numeric rank bound (needed for domination/reductions) from executable rank oracles.

## `InNP` stub (Phase 1D)

**Literature:** $\\text{distNP} = \\{(L, \\mu) : L \\in \\text{NP},\\ \\mu \\in \\text{POL-rankable}\\}$.

**Lean fork:** `InNP _L := True` until a Mathlib bitstring $\\text{NP}$ layer exists; `InDistNP` still enforces `IsPolRankable`.

**Rationale:** Keeps distNP-shaped definitions checkable now without axiomatizing Turing machines.

## Domination uses `lenBot` (Phase 1D)

**Literature:** $p_2(f(x)) \\le c_0 |x|^{c_1} p_1(x)$ with $|x| = \\text{len}(x)$.

**Lean fork:** Replace $|x|$ with `lenBot x` in the domination inequality so the identity reduction is provable at the empty string.

**Rationale:** Aligns with the RS93 denominator convention; avoids $0^{c_1}$ collapsing domination at $|x| = 0$.

## Reduction map without poly-time check (Phase 1D)

**Literature:** $f$ is polynomial-time computable.

**Lean fork:** `DistributionalReduction` records correctness and domination only; no bound on $\\text{len}(f(x))$ yet (transitivity of reductions deferred).

**Rationale:** Polynomial-time map verification waits on a concrete encoding of poly-time functions.
