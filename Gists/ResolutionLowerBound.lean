/-
Runnable gist for arxiv.md, displayed with the resolution lower bound.

These are the two headline statements of the report's Section 3, formalizing
the Chvatal-Szemeredi bound and its averaged corollary.  The density
hypothesis `7/10 ≤ c * 2^(-k)` is what makes the union bound
`2^n (1 - 2^(-k))^(cn) → 0` work, since `7/10 > ln 2`.

The proofs are the top-level assembly only; the combinatorial content lives in
the Lemma 1 through Lemma 5 chain, which the paper describes in prose and which
`AvgCaseMls.Section3` proves in full with no hypothesis packages.

Checked against AvgCaseMls.Section3.
-/
import AvgCaseMls.Section3

namespace Gists.ResolutionLowerBound

open AvgCaseMls.Section3

/--
Random dense `k`-CNF needs exponentially long resolution refutations with
probability tending to `1`.  The event asserts both unsatisfiability and the
lower bound `(1 + ε)^n` on minimum refutation length.
-/
theorem theorem_3_1
    (c k : Nat) (hc : 0 < c) (hk : 3 ≤ k)
    (hdensity : (7 / 10 : ℝ) ≤ (c : ℝ) * (2 : ℝ) ^ (-(k : ℤ))) :
    ∃ ε : ℝ, 0 < ε ∧
      WithHighProbability (denseRandomCNF c k)
        (denseTheorem31Event c k ε) :=
  theorem31_with_explicit_constants c k hc hk hdensity

/--
The averaged form.  Since the event has probability tending to `1` it
eventually has probability at least `1/2`, and resolution complexity is
nonnegative everywhere, so the expectation is at least half the bound.
-/
theorem theorem_3_2
    (c k : Nat) (hc : 0 < c) (hk : 3 ≤ k)
    (hdensity : (7 / 10 : ℝ) ≤ (c : ℝ) * (2 : ℝ) ^ (-(k : ℤ))) :
    ∃ ε : ℝ, 0 < ε ∧
      IsAsymptoticOmega (averageResolutionComplexity c k)
        (fun r => (1 + ε) ^ r) :=
  average_resolution_omega c k hc hk hdensity

/-! ## The combinatorial core

CS87 Lemma 5 is the step that produces the exponential bound.  It is a
deterministic implication: a clause family based on a hypergraph with
properties `P(a)` and `Q(a,b)` that admits a refutation at all admits none
shorter than `(1/4)(e/2)^(a⌊bn⌋/16)`.  Theorem 3.1 supplies `P` and `Q` with
high probability, and resolution completeness supplies the refutation. -/

example {n m : Nat} {a b : ℝ} {H : Hypergraph n m} {F : Fin m → Clause n}
    (hbased : ClauseFamilyBasedOn H F)
    (hP : H.HasPropertyP a) (hQ : H.HasPropertyQ a b)
    (ha : 0 ≤ a) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hba : b ≤ a / 8)
    (hrefutes : ∃ cs, ResolutionRefutation F cs) :
    (1 / 4 : ℝ) * (Real.exp 1 / 2) ^ (a * ⌊b * n⌋₊ / 16) ≤
      resolutionComplexity F :=
  cs87_lemma5 hbased hP hQ ha hb0 hb1 hba hrefutes

end Gists.ResolutionLowerBound
