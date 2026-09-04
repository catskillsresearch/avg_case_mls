/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/
import AvgCaseMls.DominationCollapse
import AvgCaseMls.HardnessCollapse

/-!
# Repairing the average-case vocabulary

`EncodingCollapse`, `DominationCollapse`, and `HardnessCollapse` isolate three
independent defects in the formalized Reischuk--Schindelhauer vocabulary.  This
file supplies the two repairs and checks that they are strong enough to exclude
the degenerate witnesses while still weak enough to admit the real theorem.

## Repair 1: target laws must be probability measures

`Subprobability` bounds total mass by `1`.  Requiring `mass = 1` excludes
`Section4.zeroLaw` ([`zeroLaw_not_probability`]) and makes rank positive
somewhere ([`exists_rank_pos_of_mass_eq_one`]), so the domination inequality
becomes a genuine numeric constraint ([`domination_constrains`]) rather than
`0 ≤ _`.

Crucially the repair does not break TR1995 Theorem 4.4: the transported law is
a pushforward along an injection, which preserves total mass, so
[`theorem_4_4_strict`] goes through against the strengthened definition.

## Repair 2: average time must refer to a decider

`AvCom.DistTime` quantifies a free runtime function.  The repair is
`Foundation.InAverageP`, which quantifies over an actual
`Foundation.Decider` and measures its `actualRuntime`.  The contrast is exact:
`AvP` never mentions the language ([`HardnessCollapse.avP_iff_polRankable`]),
whereas the repaired class entails that the language is totally decidable
([`inAverageP_has_decider`]).
-/

namespace AvgCaseMls.Repair

open AvgCaseMls.Foundation AvgCaseMls.Section4

/-! ## Repair 1: probability measures as target laws -/

/-- A `Subprobability` whose total mass is exactly `1`. -/
def Subprobability.IsProbability (μ : Subprobability) : Prop := μ.mass = 1

/-- The degenerate witness of `DominationCollapse` is excluded. -/
theorem zeroLaw_not_probability : ¬ Subprobability.IsProbability zeroLaw := by
  rw [Subprobability.IsProbability, zeroLaw_mass]
  exact zero_ne_one

/-- A probability measure charges some point. -/
theorem exists_prob_ne_zero_of_mass_eq_one {μ : Subprobability}
    (h : Subprobability.IsProbability μ) : ∃ x, μ.prob x ≠ 0 := by
  by_contra hc
  have hzero : μ.prob = fun _ => 0 := by
    funext x
    exact not_not.mp fun hx => hc ⟨x, hx⟩
  rw [Subprobability.IsProbability, Subprobability.mass, hzero, tsum_zero] at h
  exact zero_ne_one h

/-- Hence its rank is positive somewhere, unlike the zero law. -/
theorem exists_rank_pos_of_mass_eq_one {μ : Subprobability}
    (h : Subprobability.IsProbability μ) : ∃ x, 0 < μ.rank x := by
  obtain ⟨x, hx⟩ := exists_prob_ne_zero_of_mass_eq_one h
  exact ⟨x, Subprobability.rank_pos μ x hx⟩

/--
**The domination clause does real work once the target charges the point.**
Wherever the target law gives `map x` positive probability, domination forces a
genuine numeric inequality, in contrast to the `0 ≤ _` of `zeroLaw`.
-/
theorem domination_constrains {source : DistributionalProblem}
    {L : Set Bitstring} {μ : Subprobability}
    (r : InjectiveDistributionalReduction source ⟨L, μ⟩)
    {x : Bitstring} (h : μ.prob (r.map x) ≠ 0) :
    1 ≤ r.rankFactor (len x) * source.distribution.rank x :=
  le_trans (Subprobability.rank_pos μ _ h) (r.rank_domination x)

/-- In particular the source rank at such a point cannot vanish, so the
degenerate discharge used in `DominationCollapse` is unavailable. -/
theorem source_rank_pos {source : DistributionalProblem}
    {L : Set Bitstring} {μ : Subprobability}
    (r : InjectiveDistributionalReduction source ⟨L, μ⟩)
    {x : Bitstring} (h : μ.prob (r.map x) ≠ 0) :
    0 < source.distribution.rank x := by
  have hone := domination_constrains r h
  refine Nat.pos_of_ne_zero fun hzero => ?_
  rw [hzero, Nat.mul_zero] at hone
  omega

/-! ### The repaired notion of language-level completeness -/

/--
`Section4.IsNPAverageCompleteLanguage` with both laws required to be
probability measures.  This is the notion TR1995 and RS93 intend.
-/
def IsNPAverageCompleteLanguageStrict (language : Set Bitstring) : Prop :=
  InNP language ∧
    ∀ source : DistributionalProblem, InDistNP source →
      Subprobability.IsProbability source.distribution →
      ∃ distribution : Subprobability,
        Subprobability.IsProbability distribution ∧
        IsPolynomialTimeRankable distribution ∧
        Nonempty (InjectiveDistributionalReduction source
          ⟨language, distribution⟩)

/--
**The repair is compatible with TR1995 Theorem 4.4.**  Honest, polynomial-time
invertible, injective reductions still transfer language-level completeness
when target laws are required to be probability measures.

The reason the strengthening survives is that `transport` is a pushforward
along an injection, and `Section4.HonestInvertibleReduction.transport_mass`
shows pushforward preserves total mass.  So the transported law is again a
probability measure, and the rest of the original argument is unchanged:
`transport_rankable` rebuilds rankability from range decision plus the
polynomial-time inverse, honesty keeps the composed fuel bound polynomial, and
the two reductions compose.
-/
theorem theorem_4_4_strict {L₁ L₂ : Set Bitstring}
    (r : HonestInvertibleReduction L₁ L₂)
    (hL₂NP : InNP L₂)
    (hL₁ : IsNPAverageCompleteLanguageStrict L₁) :
    IsNPAverageCompleteLanguageStrict L₂ := by
  refine ⟨hL₂NP, ?_⟩
  intro source hsource hmass
  obtain ⟨μ, hμmass, hμRankable, hred⟩ := hL₁.2 source hsource hmass
  refine ⟨r.transport μ, ?_, r.transport_rankable hμRankable, ?_⟩
  · rw [Subprobability.IsProbability, r.transport_mass]
    exact hμmass
  · exact ⟨InjectiveDistributionalReduction.trans hred.some
      (r.distributionalReduction μ)⟩

/-! ## Repair 2: average time must refer to a decider -/

/--
**The repaired average-time class is sensitive to the language.**
`Foundation.InAverageP` quantifies over a genuine `Foundation.Decider`, whose
`actualRuntime` is the step count of an actual halting computation, so it
cannot be witnessed by the free `f ≡ 0` that trivializes `AvCom.DistTime`.

Contrast `HardnessCollapse.avP_iff_polRankable`, which shows `AvCom.AvP` is
equivalent to polynomial rankability of the law and therefore says nothing
whatever about the language -- it holds even when the language admits no
decision procedure at all.
-/
theorem inAverageP_has_decider {p : DistributionalProblem}
    (h : InAverageP p) : Nonempty (Decider p.language) := by
  obtain ⟨d, -⟩ := h
  exact ⟨d⟩

end AvgCaseMls.Repair
