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

## FOS80 decision procedure (Phase 2C)

**Literature:** Ferro–Omodeo–Schwartz [FOS80] §3 model-graph decision for MLS satisfiability.

**Lean fork — Step 3 witness:** When two distinct variables are forced empty (`eqEmpty`) but linked by `neq`, Step 3 returns **unsat** via `hasStep3Obstruction` (sound: empty ≠ empty cannot satisfy `neq`).

**Lean fork — partial Steps 1 & 4:** `formulaToConjunct?` covers `rel` + `and` only; Step 4 cycle check is syntactic (no semantic completeness). `decideMLSSat_complete` remains `sorry`.

**Lean fork — `relationToLiteral?`:** Maps only FOS80 §3 patterns (`var`/`empty`/`∪`/`∩`/`\\` on variables). The `relationToLiteral?_eval` proof uses `sorry` only for the unreachable branch where `relationToLiteral? (eq t1 t2) = some lit` but `(t1,t2)` is outside that fragment (dead code for the soundness path).

**Lean fork — sound fragment:** `InDecideSoundFragment` / `InDecideSoundFormula` hypothesis on `decideMLSSat_sound` and `decideConjunct_sound` (no membership/`eqOp` literals; Step 3 obstruction false).

**Rationale:** Honest partial procedure: proved soundness on the conjunct fragment exercised by tests; completeness deferred past Phase 2C.

## MLS formula encoding (Phase 2D)

**Literature:** TR1995-711 and §8 represent satisfiable MLS formulas as bitstrings in $\\{0,1\\}^*$.

**Lean fork:** Tagged prefix encoding in [`Serialization.lean`](AvgCaseMls/Serialization.lean): 3-bit constructor tags for `Term` / `Formula`, 2-bit tags for `Relation`, unary `encodeNat` for variable indices. [`wireSizeFormula`] (alias [`formulaSize`]) tracks exact `len (serializeFormula f)` via [`len_serializeFormula`].

**Lean fork — step budget:** [`stepsMLS`] = `wireSizeFormula f` + [`stepsConjunct`] when [`formulaToConjunct?`] succeeds; conjunct budget is $O(n^2)$ in literal count (Step 2 pairs). No link to `IsAvTime` yet (Phase 5 / future work).

**Rationale:** Removes the §8 `serializeFormula` axiom; keeps `NEXP_neq_EXP` and `SatMLS_average_hard` as structural placeholders until Phase 4–5.

## NP membership proxy (Phase 3A)

**Literature:** $\\text{SatMLS} \\in \\text{NP}$ via polynomial-size certificates and poly-time verification.

**Lean fork — checker vs semantic language:** [`SatMLSChecker`](AvgCaseMls/NPMembership.lean) is the NP target: decode a bitstring with [`decodeFormula?`], require empty rest, run [`decideMLSSat`]. [`SatMLSChecker_in_NP`] uses certificate length bound `0` and verifier [`verifySatMLS`]. Semantic [`SatMLS`] still uses noncomputable [`evalFormula`]; [`SatMLSChecker_subset_SatMLS`] links checker → semantic language on the decide-sound fragment.

**Lean fork — `InNP`:** [`InNP`](AvgCaseMls/AvCom.lean) is certificate-based ($\\exists$ poly-bounded verify with $x \\in L \\iff \\exists$ cert, not semantic `True`).

**Deferred:** [`decodeFormula?_serializeFormula`] and suffix decode lemmas remain `sorry` (partial-def proof friction); does not block the NP scaffold.

**Rationale:** NP membership is for the poly-time checker on encodings, not full semantic satisfiability without completeness.

## Encoding size bounds (Phase 3B)

**Literature:** $\\Vert\\varphi\\Vert$ is polynomially bounded in syntax size (TR1995-711 / §8).

**Lean fork — syntax mass:** [`formulaAstMass`] = [`formulaNodes`] + [`maxVarFormula`]; [`encodingBound n := nodeBound n + 2`] with [`nodeBound n = (n+2)^2 · 10^{12} + 10^{12}`] (quadratic slack, intentionally loose).

**Lean fork — lemmas:** [`formulaSize_le_encodingBound`], [`encodingBound_poly`], [`formulaSize_le_polyMass`]; wire-size bounds via [`formulaSize_le_nodeBound`] modulo [`nodeBound_pair_le`] `sorry` (binary combine inequality) and rel/not wrapper steps.

**Rationale:** Delivers checkable polynomial-size targets for Phase 4–5; tighten combine/decode proofs later.
