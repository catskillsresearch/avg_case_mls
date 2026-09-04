/-
Runnable snippet for arxiv.md, displayed with the two repairs.

Repair 1 requires target laws to be probability measures.  That excludes the
degenerate law and makes the domination inequality a genuine numeric
constraint, while still admitting the report's Theorem 4.4 -- because
`transport` is a pushforward along an injection, and pushforward preserves
total mass.

Repair 2 replaces the free runtime function by an actual decider, which makes
the class sensitive to the language it is about.

Checked against AvgCaseMls.Repair.
-/
import AvgCaseMls.Repair

namespace Exposition.Repair

open AvgCaseMls.Foundation AvgCaseMls.Section4 AvgCaseMls.Repair

/-! ## Repair 1: probability measures as target laws -/

/-- The degenerate witness is excluded. -/
theorem zeroLaw_not_probability : ¬ Subprobability.IsProbability zeroLaw := by
  rw [Subprobability.IsProbability, zeroLaw_mass]
  exact zero_ne_one

/-- A probability measure charges some point, so its rank is positive there. -/
theorem exists_rank_pos_of_mass_eq_one {μ : Subprobability}
    (h : Subprobability.IsProbability μ) : ∃ x, 0 < μ.rank x := by
  obtain ⟨x, hx⟩ := exists_prob_ne_zero_of_mass_eq_one h
  exact ⟨x, Subprobability.rank_pos μ x hx⟩

/-- Wherever the target charges `map x`, domination is a real inequality
rather than `0 ≤ _`. -/
theorem domination_constrains {source : DistributionalProblem}
    {L : Set Bitstring} {μ : Subprobability}
    (r : InjectiveDistributionalReduction source ⟨L, μ⟩)
    {x : Bitstring} (h : μ.prob (r.map x) ≠ 0) :
    1 ≤ r.rankFactor (len x) * source.distribution.rank x :=
  le_trans (Subprobability.rank_pos μ _ h) (r.rank_domination x)

/-- And the source rank at such a point cannot vanish, so the degenerate
discharge is unavailable. -/
theorem source_rank_pos {source : DistributionalProblem}
    {L : Set Bitstring} {μ : Subprobability}
    (r : InjectiveDistributionalReduction source ⟨L, μ⟩)
    {x : Bitstring} (h : μ.prob (r.map x) ≠ 0) :
    0 < source.distribution.rank x := by
  have hone := domination_constrains r h
  refine Nat.pos_of_ne_zero fun hzero => ?_
  rw [hzero, Nat.mul_zero] at hone
  omega

/-- The report's Theorem 4.4 survives the strengthening. -/
theorem theorem_4_4_strict {L₁ L₂ : Set Bitstring}
    (r : HonestInvertibleReduction L₁ L₂)
    (hL₂NP : InNP L₂)
    (hL₁ : IsNPAverageCompleteLanguageStrict L₁) :
    IsNPAverageCompleteLanguageStrict L₂ := by
  refine ⟨hL₂NP, ?_⟩
  intro source hsource hmass
  obtain ⟨μ, hμmass, hμRankable, hred⟩ := hL₁.2 source hsource hmass
  refine ⟨r.transport μ, ?_, r.transport_rankable hμRankable, ?_⟩
  · -- Pushforward along an injection preserves total mass.
    rw [Subprobability.IsProbability, r.transport_mass]
    exact hμmass
  · exact ⟨InjectiveDistributionalReduction.trans hred.some
      (r.distributionalReduction μ)⟩

/-! ## Repair 2: average time must refer to a decider -/

/-- The repaired class entails that the language is totally decidable, in
exact contrast to `avP_iff_polRankable`. -/
theorem inAverageP_has_decider {p : DistributionalProblem}
    (h : InAverageP p) : Nonempty (Decider p.language) := by
  obtain ⟨d, -⟩ := h
  exact ⟨d⟩

end Exposition.Repair
