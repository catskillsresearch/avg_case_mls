/-
Runnable snippet for arxiv.md, displayed with the two repairs.

Repair 1 requires target laws to be probability measures (`mass = 1`).
Repair 2 replaces the free runtime function by an actual decider.

Checked against AvgCaseMls.Repair.
-/
import AvgCaseMls.Repair

namespace Exposition.Repairs

open AvgCaseMls.Foundation AvgCaseMls.Section4 AvgCaseMls.Repair

theorem zeroLaw_not_probability : ¬ Subprobability.IsProbability zeroLaw := by
  rw [Subprobability.IsProbability, zeroLaw_mass]
  exact zero_ne_one

theorem domination_constrains {source : DistributionalProblem}
    {L : Set Bitstring} {μ : Subprobability}
    (r : InjectiveDistributionalReduction source ⟨L, μ⟩)
    {x : Bitstring} (h : μ.prob (r.map x) ≠ 0) :
    1 ≤ r.rankFactor (len x) * source.distribution.rank x :=
  AvgCaseMls.Repair.domination_constrains r h

theorem theorem_4_4_strict {L₁ L₂ : Set Bitstring}
    (r : HonestInvertibleReduction L₁ L₂)
    (hL₂NP : InNP L₂)
    (hL₁ : IsNPAverageCompleteLanguageStrict L₁) :
    IsNPAverageCompleteLanguageStrict L₂ :=
  AvgCaseMls.Repair.theorem_4_4_strict r hL₂NP hL₁

theorem inAverageP_has_decider {p : DistributionalProblem}
    (h : InAverageP p) : Nonempty (Decider p.language) :=
  AvgCaseMls.Repair.inAverageP_has_decider h

end Exposition.Repairs
