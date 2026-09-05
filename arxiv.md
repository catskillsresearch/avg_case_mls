# Revisiting the Average Case Complexity of Multilevel Syllogistic

> **Portable edition:** run `./scripts/build_arxiv_with_includes.sh` to generate [`arxiv_with_includes.md`](arxiv_with_includes.md), a self-contained copy with each Lean snippet inlined at its `<!-- include-lean -->` marker.

## Abstract

We revisit Cox, Ericson, and Mishra's 1995 Courant technical report TR1995-711 (*The average case complexity of multilevel syllogistic*) in Lean 4. The report's combinatorial core — the Chvátal–Szemerédi resolution lower bound and its averaged corollary — formalizes completely: 6,833 lines across eighteen modules, no `sorry`, no hypothesis packages. So do the three SAT-to-fragment reductions (Theorems 5.1–5.3), Example 4.1 with its explicit normalizing constant, and Theorem 4.4 on the timed layer when honest invertible reductions are taken seriously.

Against that positive record, three independent defects in this repository's
initial untimed adaptation of the Reischuk–Schindelhauer vocabulary make
several encoded theorems carry no complexity content. These are defects of the
Lean adaptation: RS93 and TR1995 tie running time and NP membership to machines,
conditions the adaptation omitted. We prove the resulting collapses
constructively, supply repairs, and re-prove Theorem 4.4 against strengthened
definitions. Every displayed proof has a runnable Lean counterpart in
[`Exposition/`](Exposition/).

---

## 1. Introduction

In the Correct Program Technology (CPT) vision of the 1970s–80s, programmers would write code alongside mathematical specifications, and a compiler integrated with an automated theorem prover would verify conformance [DS77]. Decision procedures for decidable sublanguages of set theory — Multilevel Syllogistic (MLS), Elementary MLS (EMLS), and related fragments — were central to that program [FOS80, Sny90a]. But MLS and EMLS are NP-complete in the worst case, and extensions with Presburger arithmetic are much worse. Goldberg's early experiments [Gol79] suggested that resolution-based SAT solvers might nonetheless perform well on *average* inputs, motivating a formal theory of average-case complexity [BDCGL89, Lev86, RS93, Gur91].

TR1995-711 [CEM95] applies that theory to MLS satisfiability and related verification problems. It states theorems, not conjectures, for resolution lower bounds (Section 3), average-case completeness and transfer (Section 4), and polynomial-time reductions from SAT to MLS, EMLS, and FP/LP (Section 5).

This note asks a narrower question: **what survives contact with a proof assistant?** We formalized the report's definitions and theorems in Lean 4 against Mathlib. The answer splits cleanly. The combinatorial and syntactic content is real and now verified. Several complexity-theoretic statements collapse because the repository's initial untimed encoding omits machine-time conditions and admits zero-mass witnesses.

Our contribution is therefore twofold:

1. **A verified formalization** of the report's resolution lower bounds, Example 4.1, the three Section 5 reductions, and Theorem 4.4 on a timed machine model with honest invertible reductions.
2. **A diagnostic audit** identifying three encoding defects, proving their consequences, and supplying repairs strong enough to restore Theorem 4.4 while excluding the degenerate laws.

Proofs in the text are complete but compact. Where the Lean proof fits in ten lines, the snippet copies it; otherwise the snippet states the theorem and points to the library implementation. Run `./scripts/check_exposition.sh` to verify every snippet independently.

---

## 2. Verified results

This section states the positive canon. Each theorem carries our own number; §6 maps back to TR1995.

### Theorem 1 (Resolution lower bound; TR1995 Theorem 3.1)

Fix constants `c > 0` and `k ≥ 3`. Consider the random dense `k`-CNF model `K(c·n, n, k)`: sample `c·n` clauses independently and uniformly from the ordinary `k`-clauses on `n` variables, then erase sign information. If the density satisfies `7/10 ≤ c · 2^(-k)`, then for some `ε > 0` the following event has probability tending to `1`:

> the formula is unsatisfiable, and its minimum resolution refutation length is at least `(1 + ε)^n`.

**Proof.** The density hypothesis makes the union bound `2^n (1 - 2^(-k))^(cn) → 0` work, since `7/10 > ln 2`. Hence unsatisfiability holds with high probability (WHP) by a direct counting argument.

Separately, project each signed CNF to its unsigned hypergraph and apply CS87's local-sparsity machinery. Lemma 1 (local sparsity) holds WHP on random hypergraphs. Lemma 4 lifts this to joint satisfaction of properties `P(a)` and `Q(a,b)` on the projected hypergraph, WHP. For any formula in the WHP intersection of {unsatisfiable} and {`P ∧ Q`}, resolution completeness supplies a refutation, and CS87 Lemma 5 lower-bounds its length by `(1/4)(e/2)^(a⌊bn⌋/16)`, which eventually exceeds `(1 + ε)^n` for a suitable `ε`. A squeeze argument on event probabilities completes the proof. ∎

The combinatorial chain (Lemmas 1–5, projection, resolution completeness) is fully formalized in `AvgCaseMls/Section3/` with no `sorry`.

<!-- include-lean: Exposition/ResolutionLowerBound.lean -->

### Theorem 2 (Average resolution complexity; TR1995 Theorem 3.2)

Under the same hypotheses as Theorem 1, the expected resolution complexity satisfies

\[
\mathbb{E}[\text{resolutionComplexity}(F)] = \Omega\bigl((1 + \varepsilon)^n\bigr).
\]

**Proof.** Take the `ε > 0` from Theorem 1. Once the event of Theorem 1 has probability at least `1/2`, every formula in that event contributes at least `(1 + ε)^n` to the expectation, and resolution complexity is nonnegative everywhere. Hence the expectation is at least `(1/2)(1 + ε)^n` eventually. Reindexing `n = r + k` yields the stated asymptotic bound. ∎

(See the same snippet as Theorem 1.)

### Theorem 3 (Example 4.1; TR1995 Example 4.1)

Let the **standard law** assign mass `(6/π²) · |x|⁻² · 2^(-|x|)` to each nonempty bitstring `x` (and zero to the empty string). For any `ε > 0`, the shell contributions

\[
\text{shell}_n := \sum_{|x| = n} \mu(x) \cdot T^{-1}(|x|^2) / |x|
\]

with inverse time scale `T⁻¹(t) = t^(1/(1+ε))` satisfy `∑_n shell_n < ∞`. After normalization by `C = max(∑_n shell_n, 1)`, the Levin average-time condition holds for any decider running in at most `|x|²` steps.

**Proof.** On the shell of length `n`, the `2^(-n)` factor cancels and the summand is `(6/π²) · n^(-3 + 2/(1+ε))`. The exponent `-3 + 2/(1+ε)` is strictly below `-1` when `ε > 0`, because `2/(1+ε) < 2`. Comparison with the p-series for exponent `s < -1` gives convergence (Mathlib lemma `Real.summable_nat_rpow`).

Convergence does **not** imply the Levin bound `≤ 1`; that requires dividing by `C`. The standard law itself sums to `1` via `∑ n⁻² = π²/6`. ∎

<!-- include-lean: Exposition/Example41.lean -->

### Theorem 4 (Honest invertible reductions preserve completeness; TR1995 Theorem 4.4)

Work in the **timed layer**: languages are decided by explicit `Program`s within polynomial bounds; distributional problems pair a language with a `Subprobability` whose rank function is computed in polynomial time; reductions are injective, computed in polynomial time, and satisfy a rank-domination inequality.

If `L₁` is NP-average complete, `L₂ ∈ NP`, and `r : L₁ → L₂` is an **honest invertible reduction** (injective, polynomial-time computable, polynomial-time inverse on the range, range recognizable in polynomial time, and honest in output length), then `L₂` is NP-average complete.

**Proof.** Given a distributional-NP source `(L_source, μ_source)`, completeness of `L₁` yields a polynomial-time rankable law `μ` on `L₁` and an injective distributional reduction from the source to `(L₁, μ)`.

Push `μ` forward along `r.map` to obtain a law on `L₂`. Mass is preserved; ranks on the image are preserved exactly (`rankFactor = 1`). Rankability of the pushforward is rebuilt by composing: test membership in `range(r.map)`, apply the inverse, compute the rank — with fuel bounded using the honesty inequality `|x| ≤ honestyBound(|r.map x|)`.

Package this as an injective distributional reduction into `(L₂, r.transport μ)` and compose with the source-to-`L₁` reduction. ∎

<!-- include-lean: Exposition/Theorem44Strong.lean -->

### Theorems 5–7 (SAT reductions; TR1995 Theorems 5.1–5.3)

All three reductions include **correctness** (satisfiability ↔ target satisfiability), **injectivity**, and an **exact size identity**. MLS and EMLS also expose an explicit **left inverse** (decoder). The FPILP core does not yet state a decoder.

**Theorem 5 (SAT → MLS-in).** A distinguished variable `x` (index `0`) represents an element; propositional variable `i` becomes set variable `i+1`. Literal `v_i` becomes `x ∈ s(i)`; literal `¬v_i` becomes `x ∉ s(i)`. The empty clause encodes as `x ∈ x` (foundation-false); the empty CNF as `x ∉ x` (foundation-true, since equality atoms are unavailable in the fragment). Output size: `5 · |φ| - 1` formula nodes.

**Theorem 6 (SAT → EMLS).** Each variable `i` gets positive set `4i+1`, negative set `4i+2`, and intersection gadget `4i+7 = pos ∩ neg = ∅`. Clause gadgets build unions along literal chains; the distinguished element is forced into the union of a satisfied clause's literal sets. The bare semantic core is **not** injective (the complement gadget ignores polarity); tagging with a provenance prefix encoding the source bits repairs this via `toEMLS`.

**Theorem 7 (SAT → FPILP).** Variables are constrained to `{0,1}` by `x_i ≥ 0` and `1 - x_i ≥ 0`. Each clause becomes `∑_{l ∈ c} term(l) ≥ 1` where `v_i` contributes `x_i` and `¬v_i` contributes `1 - x_i`. Constraint count: `2n + |φ|`.

<!-- include-lean: Exposition/Reductions.lean -->

---

## 3. What the formalization found

Auditing the repository's initial untimed approximation of the report's RS93-based vocabulary exposes three independent defects. Each admits a concrete degenerate witness; together they trivialize Theorems 4.1, 4.4 (in the untimed layer), and the entire conditional hardness chain.

### 3.1 Degenerate laws

Both the untimed `AvCom.Distribution` and the timed `Foundation.Subprobability` bound total mass by `1` rather than fixing it at `1`. Both rank functions return `0` wherever probability vanishes. The everywhere-zero law is therefore admissible, polynomial-time rankable, and has rank identically zero — making the domination inequality `0 ≤ _` free.

<!-- include-lean: Exposition/DegenerateLaws.lean -->

### 3.2 Collapse I: membership is free (Theorem 8)

**Theorem 8.** In the untimed `AvCom` layer, `InNP L` holds for every language `L`.

**Proof.** `InNP` quantifies over an arbitrary verifier `verify : Bitstring → Bitstring → Bool` and bounds only certificate *length*, never the cost of running `verify`. Take `verify x w := decide(x ∈ L)` with certificate bound zero. The empty certificate witnesses membership. ∎

<!-- include-lean: Exposition/InNPTrivial.lean -->

**Theorem 9 (Characterization of untimed completeness; no TR1995 counterpart).** `TR1995.IsNPAverageCompleteLanguage L` if and only if `L ≠ ∅` and `L ≠ Bitstring`.

**Proof sketch.** Forward: reduce from the universal and empty sources using the zero law; nontriviality forces a member and a non-member. Backward: given `a ∈ L` and `b ∉ L`, map source members to `a` and non-members to `b`; domination is free because target rank is zero. Full proof in the library. ∎

<!-- include-lean: Exposition/CompletenessCharacterization.lean -->

**Corollary (TR1995 Theorem 4.4 is empty in this layer).** Completeness transfers along any map satisfying the correctness biconditional alone. The injectivity, invertibility, range recognition, forward length, and honesty fields — the hypotheses the report's Theorem 4.4 is about — are never used.

<!-- include-lean: Exposition/Theorem44Vacuous.lean -->

TR1995 Theorem 4.1 (completeness of a distributional problem implies completeness of its language) is a quantifier shift, not a complexity result; we demote it to a remark in §6.

### 3.3 Collapse II: domination is free (Theorem 10)

Moving to the timed layer repairs the verifier and reduction-map gaps: `Foundation.InNP` requires a `Program` deciding within a polynomial bound; injective distributional reductions require a `Program` for the map. But the domination condition still carries no content.

**Theorem 10.** In the timed layer, language-level NP-average completeness is equivalent to `InNP L` together with injective polynomial-time hardness from every distributional-NP source — with no use of rank domination.

**Proof sketch.** Forward: forget the three rank fields. Backward: supply `zeroLaw` as the target; discharge domination with rank factor zero. ∎

<!-- include-lean: Exposition/DominationFree.lean -->

### 3.4 Collapse III: average tractability and conditional hardness (Theorem 11)

**Theorem 11.** `AvCom.AvP p` if and only if `IsPolRankable p.μ`. The language `p.L` is irrelevant.

**Proof.** `AvCom.DistTime T p` reads `∃ f, IsAvTime T f p.μ`. Nothing ties `f` to a decider for `p.L`. Witness `f ≡ 0`; then `T⁻¹ T 0 = 0` and every rank-truncated sum vanishes. Rankability of the law is the only remaining constraint. ∎

<!-- include-lean: Exposition/AvPVacuous.lean -->

**Corollary.** Every distributional-NP problem is in `AvP`, unconditionally. Any `AverageCaseCollapseTheory` package therefore proves `NEXP = EXP` (its characterizing field is `(∀ p, InDistNP p → AvP p) ↔ NEXP = EXP`). No such package satisfies `NEXP ≠ EXP`. Hence every conditional hardness theorem in `AvgCaseMls/NonAvP.lean` — including `SatMLS_average_hard` and `satMLSProb_not_AvP` — has an **unsatisfiable hypothesis**; they are vacuous, not merely conditional.

---

## 4. Repairs

The collapses isolate encoding defects, not errors in the report's combinatorial or syntactic architecture. Two repairs suffice for the definitions the paper actually uses.

### Repair 1: require `mass = 1` of target laws

Define `Subprobability.IsProbability μ` as `μ.mass = 1`. Require both source and target laws in completeness and reduction statements to be probability measures. This excludes `zeroLaw` and forces some point to have positive rank, making domination a genuine numeric constraint wherever the target charges the image.

**Theorem 12 (Theorem 4.4 under the repair).** Honest invertible reductions preserve `IsNPAverageCompleteLanguageStrict` — the strengthened definition requiring probability measures. The proof is unchanged in structure: pushforward along an injection preserves total mass.

<!-- include-lean: Exposition/Repair.lean -->

### Repair 2: tie average time to a decider

Replace the existentially quantified runtime function in `DistTime` by `Foundation.InAverageP`, which quantifies over a genuine `Decider` and measures `actualRuntime`. Unlike `AvP`, this class entails that the language is totally decidable.

Example 4.1 is already stated in this layer (`IsLevinAverageTime` with an explicit `Decider`).

---

## 5. Remaining open interfaces

Three items from the report are packaged as explicit hypothesis structures, not proved:

| Interface | Content | Used for |
|-----------|---------|----------|
| `LevinNBHData` | Universal reduction from every distNP problem to bounded halting | NBH completeness |
| `NBHToMLSData` | Cook–Levin compiler NBH → serialized MLS with domination | SAT-MLS completeness chain |
| `AverageCaseCollapseTheory` | Collapse equivalence + AvP pullback | Conditional hardness (now known vacuous) |

The FOS80 decision procedure `decideMLSSat` is **sound** on a membership-free fragment and **complete** on that same fragment, but **not** complete globally: `(∅ = ∅) ∨ (∅ ≠ ∅)` is satisfiable yet rejected, because disjunction is outside the conjunctive decoder.

These are honest gaps: the report's prose proofs for the Levin universal construction and the full MLS decision procedure were never formalized here.

---

## 6. Mapping to TR1995

| Our # | Statement | TR1995 | Status |
|------:|-----------|--------|--------|
| 1 | Resolution lower bound WHP | Thm 3.1 | **Proved** |
| 2 | Average resolution complexity Ω | Thm 3.2 | **Proved** |
| 3 | Example 4.1 summability + Levin bound | Ex 4.1 | **Proved** (explicit `C`) |
| 4 | Honest invertible reductions preserve completeness | Thm 4.4 | **Proved** (timed layer) |
| 5 | SAT → MLS-in | Thm 5.1 | **Proved** |
| 6 | SAT → EMLS (tagged `toEMLS`) | Thm 5.2 | **Proved** |
| 7 | SAT → FPILP | Thm 5.3 | **Proved** |
| 8 | `InNP` holds for every language | — | **Negative** (Collapse I) |
| 9 | Untimed completeness ↔ nontrivial language | — | **Negative** (Collapse I) |
| 10 | Timed completeness ↔ NP + hard, domination free | — | **Negative** (Collapse II) |
| 11 | `AvP` ↔ rankability; no theory separates | — | **Negative** (Collapse III) |
| 12 | Theorem 4.4 with `mass = 1` laws | Thm 4.4 | **Proved** (repair) |
| — | Completeness of problem ⇒ completeness of language | Thm 4.1 | **Remark** (quantifier shift) |
| — | Levin universal reduction | §4.2–4.3 | Open (`LevinNBHData`) |
| — | NBH → MLS compiler | §5.1, §5.4 | Open (`NBHToMLSData`) |
| — | `decideMLSSat` complete | §7 / FOS80 | **Refuted** globally |

---

## 7. Repository and methodology

The Lean development lives at [github.com/catskillsresearch/avg_case_mls](https://github.com/catskillsresearch/avg_case_mls). As of this writing: **92 modules**, **~27,400 lines**, **~2,100 declarations**, build clean with no `sorry` in the library.

| Layer | Lines | Role |
|-------|------:|------|
| `AvgCaseMls/Section3/` | 6,833 | CS87 resolution lower bounds |
| `AvgCaseMls/Foundation/` | 6,293 | Timed machine model, subprobabilities, reductions |
| `AvgCaseMls/Section4/` | 4,783 | Theorem 4.4, Example 4.1, Cook–Levin |
| Collapse + repair | ~400 | Diagnostic results |
| Section 5 reductions | ~3,000 | MLS-in, EMLS, FPILP |

**Exposition snippets.** The [`Exposition/`](Exposition/) directory holds runnable versions of every proof displayed in this document. Each file restates the theorem in context and either copies the proof (when it fits in ten lines) or applies it from the library. Check all snippets:

```bash
./scripts/check_exposition.sh
```

**Palomar.** `Challenge.lean` remains the comparator surface for external verification; Palomar size caps are deferred until the canon is complete.

---

## References

*   **[Ajt96]** Ajtai, M. (1996). Generating hard instances of lattice problems. *STOC*.
*   **[BDCGL89]** Ben-David, S., Chor, B., Goldreich, O., & Luby, M. (1989). On the theory of average case complexity. *STOC*.
*   **[CEM95]** Cox, J., Ericson, L., & Mishra, B. (1995). The average case complexity of multilevel syllogistic. *NYU Courant Institute Technical Report TR1995-711*.
*   **[COPE24]** Committee on Publication Ethics (COPE). (2024). Authorship and AI tools: COPE position statement. <https://publicationethics.org/guidance/cope-position/authorship-and-ai-tools>
*   **[Cur25]** Anysphere, Inc. Cursor: AI-native code editor and agent environment. <https://cursor.com> (accessed 2025).
*   **[deM08]** de Moura, L., & Bjørner, N. (2008). Z3: An efficient SMT solver. *TACAS*.
*   **[DS77]** Davis, M., & Schwartz, J. T. (1977). Metamathematical extensibility for theorem verifiers. *NYU Technical Report*.
*   **[FOS80]** Ferro, A., Omodeo, E. G., & Schwartz, J. T. (1980). Decision procedures for elementary sublanguages of set theory. *CPAM*.
*   **[Gol79]** Goldberg, A. T. (1979). On the complexity of the satisfiability problem. *NYU PhD Thesis*.
*   **[Gur91]** Gurevich, Y. (1991). Average case completeness. *Journal of Computer and System Sciences*.
*   **[Lev86]** Levin, L. (1986). Average case complete problems. *SIAM Journal on Computing*.
*   **[RS93]** Reischuk, R., & Schindelhauer, C. (1993). Precise average case complexity. *STOC*.
*   **[Ste23a]** Stevens, L. (2023). MLSS Decision Procedure. *Archive of Formal Proofs*. <https://isa-afp.org/entries/MLSS_Decision_Proc.html>
*   **[Ste23b]** Stevens, L. (2023). Towards a Verified Tableau Prover for a Quantifier-Free Fragment of Set Theory. In Pientka, B., & Tinelli, C. (eds.), *Automated Deduction – CADE 29*, LNAI 14132, 491–508. <https://doi.org/10.1007/978-3-031-38499-8_28>
*   **[SY92]** Schnorr, C. P., & Yoshida, T. (1992). Average-case complexity of NP-complete problems. *STOC*.
*   **[Sny90a]** Snyder, W. K. (1990). The SETL2 programming language. *NYU Technical Report*.
*   **[ST01]** Spielman, D. A., & Teng, S. H. (2001). Smoothed analysis of algorithms. *STOC*.
*   **[VR92]** Venkatesan, R., & Rajagopalan, S. (1992). Average case intractability of matrix and Diophantine problems. *STOC*.
