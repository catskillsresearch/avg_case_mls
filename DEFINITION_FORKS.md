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

**Lean fork:** `DistributionalReduction` records correctness, polynomial **length growth** (`lenBot (f x) ≤ k₀ · lenBot(x)^{k₁}`), and domination. Poly-time **decidability** of $f$ is still deferred.

**Proved:** [`DistributionalReduction.trans`] (compose length + rank bounds).

**Rationale:** Transitivity of reductions (Phase **4C**) no longer blocked on a separate `lenBot (f x)` scaffold.

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

**Rationale:** Removes the §8 `serializeFormula` axiom; [`NEXP_neq_EXP`] lives in [`ComplexityAxioms.lean`](AvgCaseMls/ComplexityAxioms.lean) for Phase **5**.

## NP membership proxy (Phase 3A)

**Literature:** $\\text{SatMLS} \\in \\text{NP}$ via polynomial-size certificates and poly-time verification.

**Lean fork — checker vs semantic language:** [`SatMLSChecker`](AvgCaseMls/NPMembership.lean) is the NP target: decode a bitstring with [`decodeFormula?`], require empty rest, run [`decideMLSSat`]. [`SatMLSChecker_in_NP`] uses certificate length bound `0` and verifier [`verifySatMLS`]. Semantic [`SatMLS`] still uses noncomputable [`evalFormula`]; [`SatMLSChecker_subset_SatMLS`] links checker → semantic language on the decide-sound fragment.

**Lean fork — `InNP`:** [`InNP`](AvgCaseMls/AvCom.lean) is certificate-based ($\\exists$ poly-bounded verify with $x \\in L \\iff \\exists$ cert, not semantic `True`).

**Lean fork — decoders:** [`decodeTerm?`], [`decodeRelation?`], [`decodeFormula?`] are fuel-based total functions (`decodeTermFuel`, etc.) so roundtrip lemmas are provable without `partial def` friction.

**Proved:** [`decodeFormula?_serializeFormula`], [`decodeFormula?_suffix`], [`SatMLSChecker_in_NP`], [`SatMLSChecker_subset_SatMLS`] on the decide-sound fragment.

**Rationale:** NP membership is for the poly-time checker on encodings, not full semantic satisfiability without completeness.

## NBH scaffold (Phase 4A)

**Literature:** Levin bounded halting $`\mathrm{BH} = \{(M,x,1^t)\}`$; TR1995-711 reductions start from NBH with a simple POL-rankable $`\mu_0`$.

**Lean fork — machine table:** [`NBHInstance`](AvgCaseMls/NBH.lean) references [`canonicalMachines`] by `machineId` rather than embedding arbitrary transition tables in the bitstring (Phase **4B** can extend).

**Lean fork — encoding:** `input · [false,false,true] · encodeNat(machineId) · [false,false,true] · encodeNat(bound)`; run certificates use the same delimiter between `state`, `head`, `tapeLen`, and `tape` fields (fourth delimiter separates unary length prefix from tape body).

**Lean fork — checker vs semantic:** [`NBHChecker`] is certificate-based via [`verifyNBH`]; [`NBHSemantic`] uses [`NBH`] on decoded instances. [`NBHChecker_in_NP`], [`nbhProb_in_DistNP`], [`decodeNat?.encode`], [`splitDelim.go_delim_suffix`], [`splitDelim.append`], [`NBHInstance.decode_encode`], [`Config.decode_encode`], and [`decodeRun?_encodeRun`] are proved (via [`encodeNat.delimFree`] / false-count non-collision on [`encodeNat`] outputs).

**Lean fork — well-formed instances:** [`NBHInstance.WellFormed`] requires the encoded `input` field not contain the field delimiter (needed for invertible splitting).

**Lean fork — $`\mu_0`$:** uniform on a singleton support containing the trivial immediate-accept instance; [`μ₀_polRankable`] via [`IsPolRankable.uniformOn_polRankable`].

**Rationale:** Delivers the distNP-complete *core scaffold* for Phase **4B** (reduction into `SatMLS`) without a Mathlib NTM layer.

## NBH → SatMLS reduction (Phase 4B)

**Literature:** TR1995-711 §3.2 distributional reduction with domination into target language/distribution.

**Lean fork — general map (Option B):** [`nbhToMlsMap`] axiomatizes the full TR1995-711 TM→MLS translation for **arbitrary MLS formulas** in paper scope (not the singleton-language restriction). [`reduceNBHToSatMLS`] := [`nbhToMlsMap`]; [`reduce_correct`] follows from [`nbhToMlsMap_correct`].

**Lean fork — scaffold map:** [`reduceNBHToSatMLSStep`] is the old step-function on [`μ₀Support`] / off-support unsat encoding; retained for [`reduce_domination`] and [`nbhToSatMLS_red_on_μ₀`] tests only.

**Lean fork — target problem [`satMLSProb`]:** language [`SatMLSChecker`], distribution [`μ₁`] uniform on `{satTargetEnc}`.

**Proved:** [`reduce_domination`], [`reduce_correct`], [`nbhToSatMLS_red`] (modulo [`nbhToMlsMap_*`] axioms).

**Rationale:** Keeps distributional correctness aligned with full [`NBHChecker`] while honestly deferring the constructive TM→MLS compiler.

## NP-average completeness (Phase 4C)

**Literature:** TR1995-711 Corollary 5.1 — MLS satisfiability is NP-average complete via NBH.

**Lean fork — pipeline:** [`IsNPAverageComplete.of_reductor`] composes a complete intermediate problem with a distributional reduction; [`satMLSProb_NPAverageComplete`] applies this to [`nbhProb_NPAverageComplete`] and [`nbhToSatMLS_red`].

**Lean fork — Levin universal reduction:** [`distNP_reduces_to_nbh`] axiom (every distNP problem reduces to [`nbhProb`]); [`nbhProb_NPAverageComplete`] follows.

**Proved:** [`DistributionalReduction.trans`], [`IsNPAverageComplete.of_reductor`], [`satMLSProb_NPAverageComplete`] (modulo [`distNP_reduces_to_nbh`] and [`nbhToMlsMap_*`] axioms).

**Rationale:** Compositional completeness logic is closed; universal NBH reduction remains the named external obligation.

## Conditional non-AvP (Phase 5)

**Literature:** TR1995-711 Corollary 5.1 consequence — NP-average complete MLS satisfiability is not in AvP under a simple POL-rankable distribution unless $\\text{NEXP} = \\text{EXP}$.

**Lean fork — collapse bundle:** [`NEXP_neq_EXP`], [`distNP_subseteq_AvP_iff_NEXP_eq_EXP`], and [`AvP_pullback`] in [`ComplexityAxioms.lean`] (decades-long literature; not reproved here).

**Lean fork — target problem:** [`SatMLS_average_hard`] and [`exists_simple_rankable_not_AvP`] use [`satMLSProb`] / [`SatMLSChecker`] with [`simpleSatμ`] (= [`μ₁`]).

**Proved:** [`AvP_of_distNP_of_complete_target`], [`NEXP_eq_EXP_of_AvP_complete`], [`not_AvP_of_NPAverageComplete`], [`SatMLS_average_hard`], [`SatMLS_semantic_not_AvP`], [`exists_simple_rankable_not_AvP`], [`nbhProb_not_AvP`] (modulo axioms above).

**Lean fork — semantic AvP:** [`SatMLS_semantic_not_AvP`] uses [`AvP.same_μ`] — average-time depends only on the distribution, so checker hardness on [`simpleSatμ`] transfers to semantic [`SatMLS`].

## Encoding size bounds (Phase 3B)

**Literature:** $\\Vert\\varphi\\Vert$ is polynomially bounded in syntax size (TR1995-711 / §8).

**Lean fork — syntax mass:** [`formulaAstMass`] = [`formulaNodes`] + [`maxVarFormula`]; [`encodingBound n := nodeBound n + 2`] with [`nodeBound n = (n+2)^2 · 10^{12} + 10^{12}`] (quadratic slack, intentionally loose).

**Lean fork — lemmas:** [`formulaSize_le_encodingBound`], [`encodingBound_poly`], [`formulaSize_le_polyMass`]; wire-size bounds via [`formulaSize_le_nodeBound`] using a multiplicative per-node slack (`3 · nodes`) plus quadratic [`nodeBound`] gap — **not** the old false [`nodeBound_pair_le`] at child mass `c−2` (parent mass can be *below* the sum of child masses when max vars overlap; e.g. two `.var 4` unions).

**Lean fork — combine proof:** [`nodeBound_pair_sum_le`] remains for index `a+b+1`; final [`wireSizeTerm_le_nodeBound`] uses [`wireSizeTerm_rec_bound`] (nodes/maxVar multiplicative bound) → [`sqMass_le_nodeBound`].

**Rationale:** Delivers checkable polynomial-size targets for Phase 4–5 without the false child-mass combine step.
