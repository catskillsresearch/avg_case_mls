/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/
import AvgCaseMls.Section4

/-!
# Rank domination is vacuous for subprobabilities

`AvgCaseMls.EncodingCollapse` shows that the untimed `AvCom` encoding of
average-case completeness has no complexity content at all.  Replacing it by
the timed `Foundation` model repairs most of the damage: `Foundation.InNP`
demands a `Program` deciding within a polynomial bound, and
`InjectiveDistributionalReduction` demands a `Program` computing the reduction
map within a polynomial bound.  Those requirements are genuine.

One weakness survives.  `Foundation.Subprobability` bounds total mass by `1`
instead of fixing it at `1`, and `Foundation.Subprobability.rank` returns `0`
wherever the probability vanishes.  The everywhere-zero law is therefore a
legal target law whose rank is identically `0`, and the domination inequality
degenerates to `0 ≤ _`.

The consequence is [`isNPAverageCompleteLanguage_iff`]: language-level
NP-average completeness in this model is *equivalent* to NP membership
together with injective polynomial-time NP-hardness.  The rank domination
condition -- the entire reason Reischuk--Schindelhauer reductions preserve
polynomial average time -- contributes nothing to the notion.

The repair is to require `mass = 1` of a target law, or to force rank to be
positive on support.
-/

namespace AvgCaseMls.Section4

open AvgCaseMls.Foundation

/-! ## The everywhere-zero law -/

/-- The everywhere-zero measure, admitted because `tsum_le_one` bounds total
mass rather than fixing it. -/
noncomputable def zeroLaw : Subprobability where
  prob := fun _ => 0
  summable_prob := summable_zero
  tsum_le_one := by simp
  finite_superlevel := fun _ hx => absurd rfl hx

@[simp] theorem zeroLaw_prob (x : Bitstring) : zeroLaw.prob x = 0 := rfl

@[simp] theorem zeroLaw_rank (x : Bitstring) : zeroLaw.rank x = 0 :=
  Subprobability.rank_eq_zero_of_prob_eq_zero _ _ rfl

/-- The zero law is not a probability measure, which is exactly why it should
not have been an admissible target law. -/
theorem zeroLaw_mass : zeroLaw.mass = 0 := by
  simp [Subprobability.mass]

/-- Its rank function is the constant `0`, computed by a one-step program. -/
theorem zeroLaw_rankable : IsPolynomialTimeRankable zeroLaw := by
  refine ⟨.constant true (encodeNat 0), fun _ => 1, IsPolynomial.const 1,
    monotone_const, ?_⟩
  intro x
  exact ⟨⟨true, encodeNat 0, 1⟩, rfl, by simp⟩

/-! ## Reductions with the domination condition removed -/

/--
An injective polynomial-time many-one reduction carrying every field of
`InjectiveDistributionalReduction` *except* the three rank fields.  This is
plain NP-hardness data: no distribution on the target is mentioned.
-/
structure PolyTimeInjectiveReduction (source : DistributionalProblem)
    (target : Set Bitstring) where
  map : Bitstring → Bitstring
  injective : Function.Injective map
  correct : ∀ x, x ∈ source.language ↔ map x ∈ target
  program : Program
  timeBound : Nat → Nat
  time_polynomial : IsPolynomial timeBound
  time_monotone : Monotone timeBound
  computed : ComputesWithin program map timeBound
  lengthBound : Nat → Nat
  length_polynomial : IsPolynomial lengthBound
  length_monotone : Monotone lengthBound
  length_bound : ∀ x, len (map x) ≤ lengthBound (len x)

namespace PolyTimeInjectiveReduction

/-- Forgetting the domination data of a distributional reduction. -/
def ofDistributional {source : DistributionalProblem}
    {target : DistributionalProblem}
    (r : InjectiveDistributionalReduction source target) :
    PolyTimeInjectiveReduction source target.language where
  map := r.map
  injective := r.injective
  correct := r.correct
  program := r.program
  timeBound := r.timeBound
  time_polynomial := r.time_polynomial
  time_monotone := r.time_monotone
  computed := r.computed
  lengthBound := r.lengthBound
  length_polynomial := r.length_polynomial
  length_monotone := r.length_monotone
  length_bound := r.length_bound

/--
Conversely, any such reduction becomes a full distributional reduction into the
zero law: the domination field is discharged with the zero rank factor, because
the target rank is identically `0`.
-/
noncomputable def toZeroLaw {source : DistributionalProblem}
    {target : Set Bitstring} (r : PolyTimeInjectiveReduction source target) :
    InjectiveDistributionalReduction source ⟨target, zeroLaw⟩ where
  map := r.map
  injective := r.injective
  correct := r.correct
  program := r.program
  timeBound := r.timeBound
  time_polynomial := r.time_polynomial
  time_monotone := r.time_monotone
  computed := r.computed
  lengthBound := r.lengthBound
  length_polynomial := r.length_polynomial
  length_monotone := r.length_monotone
  length_bound := r.length_bound
  rankFactor := fun _ => 0
  rankFactor_polynomial := IsPolynomial.const 0
  rankFactor_monotone := monotone_const
  rank_domination := fun x => by simp

end PolyTimeInjectiveReduction

/-! ## Domination contributes nothing -/

/--
**Rank domination is vacuous.**  Language-level NP-average completeness in the
timed `Foundation` model is equivalent to NP membership together with
injective polynomial-time hardness for every distributional NP source.

Left to right forgets the domination data.  Right to left supplies
[`zeroLaw`] as the target law: it is polynomial-time rankable, and its rank
vanishes identically, so the domination inequality holds with the zero rank
factor no matter what the source law is.

So while the timed model repairs `AvCom`'s failure to constrain verifiers and
reduction maps, it still does not make the domination condition do any work.
-/
theorem isNPAverageCompleteLanguage_iff (L : Set Bitstring) :
    IsNPAverageCompleteLanguage L ↔
      InNP L ∧ ∀ source : DistributionalProblem, InDistNP source →
        Nonempty (PolyTimeInjectiveReduction source L) := by
  constructor
  · rintro ⟨hInNP, hreduce⟩
    refine ⟨hInNP, ?_⟩
    intro source hsource
    obtain ⟨_, _, ⟨r⟩⟩ := hreduce source hsource
    exact ⟨PolyTimeInjectiveReduction.ofDistributional r⟩
  · rintro ⟨hInNP, hhard⟩
    refine ⟨hInNP, ?_⟩
    intro source hsource
    obtain ⟨r⟩ := hhard source hsource
    exact ⟨zeroLaw, zeroLaw_rankable, ⟨r.toZeroLaw⟩⟩

end AvgCaseMls.Section4
