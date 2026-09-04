/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.Foundation
import AvgCaseMls.Section4.RankFamily
import AvgCaseMls.Section4.Padding
import AvgCaseMls.Section4.StandardUnary
import AvgCaseMls.Section4.AverageWorstCase
import AvgCaseMls.Section4.CookLevin

/-!
# TR1995 Section 4: average-case completeness

This file uses the executable, infinite-support foundation.  In particular,
rankability means exact computation of the probability-order rank by a
polynomial-time program; it is not a finite-support rank bound.
-/

namespace AvgCaseMls.Section4

open AvgCaseMls.Foundation

/-- The paper's class `NP^dist`: timed NP paired with a POL-rankable law. -/
def InDistNP (problem : DistributionalProblem) : Prop :=
  InNP problem.language ∧ IsPolynomialTimeRankable problem.distribution

/-- Completeness among distributional NP problems under injective domination reductions. -/
def IsNPDistributionallyComplete (target : DistributionalProblem) : Prop :=
  InDistNP target ∧
    ∀ source : DistributionalProblem, InDistNP source →
      Nonempty (InjectiveDistributionalReduction source target)

/--
Language-level NP-average completeness.  The target distribution may depend
on the source distribution, exactly as in TR1995 §4.2.
-/
def IsNPAverageCompleteLanguage (language : Set Bitstring) : Prop :=
  InNP language ∧
    ∀ source : DistributionalProblem, InDistNP source →
      ∃ distribution : Subprobability,
        IsPolynomialTimeRankable distribution ∧
        Nonempty (InjectiveDistributionalReduction source
          ⟨language, distribution⟩)

/-- **TR1995, Theorem 4.1.** -/
theorem theorem_4_1 {language : Set Bitstring} {distribution : Subprobability}
    (complete : IsNPDistributionallyComplete ⟨language, distribution⟩) :
    IsNPAverageCompleteLanguage language := by
  refine ⟨complete.1.1, ?_⟩
  intro source hsource
  exact ⟨distribution, complete.1.2, complete.2 source hsource⟩

/--
The constructive content of an injective, polynomial-time invertible, honest
polynomial-time language reduction.  Range recognition is explicit because
the transported rank is zero away from the image.
-/
structure HonestInvertibleReduction (L₁ L₂ : Set Bitstring) where
  map : Bitstring → Bitstring
  injective : Function.Injective map
  correct : ∀ x, x ∈ L₁ ↔ map x ∈ L₂
  program : Program
  timeBound : Nat → Nat
  time_polynomial : IsPolynomial timeBound
  time_monotone : Monotone timeBound
  computed : ComputesWithin program map timeBound
  lengthBound : Nat → Nat
  length_polynomial : IsPolynomial lengthBound
  length_monotone : Monotone lengthBound
  length_bound : ∀ x, len (map x) ≤ lengthBound (len x)
  inverse : Bitstring → Bitstring
  inverseProgram : Program
  inverseTimeBound : Nat → Nat
  inverseTime_polynomial : IsPolynomial inverseTimeBound
  inverseTime_monotone : Monotone inverseTimeBound
  inverse_computed : ComputesWithin inverseProgram inverse inverseTimeBound
  left_inverse : Function.LeftInverse inverse map
  rangeProgram : Program
  rangeTimeBound : Nat → Nat
  rangeTime_polynomial : IsPolynomial rangeTimeBound
  rangeTime_monotone : Monotone rangeTimeBound
  range_decided : DecidesWithin rangeProgram (Set.range map) rangeTimeBound
  honestyBound : Nat → Nat
  honesty_polynomial : IsPolynomial honestyBound
  honesty_monotone : Monotone honestyBound
  honesty_bound : ∀ x, len x ≤ honestyBound (len (map x))

namespace HonestInvertibleReduction

variable {L₁ L₂ : Set Bitstring} (r : HonestInvertibleReduction L₁ L₂)

noncomputable def transport (μ : Subprobability) : Subprobability :=
  μ.pushforward r.map r.injective

@[simp] theorem transport_prob_map (μ : Subprobability) (x : Bitstring) :
    (r.transport μ).prob (r.map x) = μ.prob x :=
  Subprobability.pushforward_prob_map μ r.map r.injective x

theorem transport_mass (μ : Subprobability) :
    (r.transport μ).mass = μ.mass :=
  Subprobability.pushforward_mass μ r.map r.injective

@[simp] theorem transport_rank_map (μ : Subprobability) (x : Bitstring) :
    (r.transport μ).rank (r.map x) = μ.rank x :=
  Subprobability.rank_pushforward_map μ r.map r.injective x

theorem inverse_eq_invFun_of_mem_range {y : Bitstring}
    (hy : y ∈ Set.range r.map) :
    r.inverse y = Function.invFun r.map y := by
  obtain ⟨x, rfl⟩ := hy
  rw [r.left_inverse x, Function.leftInverse_invFun r.injective x]

open Classical in
theorem transport_rank_eq (μ : Subprobability) (y : Bitstring) :
    (r.transport μ).rank y =
      if y ∈ Set.range r.map then μ.rank (r.inverse y) else 0 := by
  change (μ.pushforward r.map r.injective).rank y = _
  rw [Subprobability.rank_pushforward_eq μ r.map r.injective y]
  split_ifs with hy
  · rw [r.inverse_eq_invFun_of_mem_range hy]
  · rfl

/-- Algorithmic rankability is preserved by inverse/range machine composition. -/
theorem transport_rankable {μ : Subprobability}
    (hμ : IsPolynomialTimeRankable μ) :
    IsPolynomialTimeRankable (r.transport μ) := by
  obtain ⟨rankProgram, rankTime, rankPolynomial, rankMonotone, rankComputed⟩ := hμ
  let trueProgram := Program.compose r.inverseProgram rankProgram
  let rankTransportProgram :=
    Program.branch r.rangeProgram trueProgram (.constant false (encodeNat 0))
  let T := fun n =>
    r.rangeTimeBound n +
      (r.inverseTimeBound n + rankTime (r.honestyBound n))
  refine ⟨rankTransportProgram, T,
    r.rangeTime_polynomial.add
      (r.inverseTime_polynomial.add
        (rankPolynomial.comp r.honesty_polynomial)),
    ?_, ?_⟩
  · intro a b hab
    exact Nat.add_le_add (r.rangeTime_monotone hab)
      (Nat.add_le_add (r.inverseTime_monotone hab)
        (rankMonotone (r.honesty_monotone hab)))
  · intro y
    obtain ⟨rangeResult, hrange, hrangeCorrect⟩ := r.range_decided y
    have hrangeTime : r.rangeTimeBound (len y) ≤ T (len y) :=
      Nat.le_add_right _ _
    have hrange' := r.rangeProgram.eval_mono hrangeTime hrange
    by_cases hy : y ∈ Set.range r.map
    · obtain ⟨x, rfl⟩ := hy
      obtain ⟨inverseResult, hinverse, hinverseOut⟩ :=
        r.inverse_computed (r.map x)
      obtain ⟨rankResult, hrank, hrankOut⟩ := rankComputed x
      have hinverseValue : r.inverse (r.map x) = x := r.left_inverse x
      have hinverseTime :
          r.inverseTimeBound (len (r.map x)) ≤ T (len (r.map x)) :=
        Nat.le_add_left_of_le (Nat.le_add_right _ _)
      have hrankTime : rankTime (len x) ≤ T (len (r.map x)) := by
        apply (rankMonotone (r.honesty_bound x)).trans
        exact (Nat.le_add_left _ _).trans (Nat.le_add_left _ _)
      have hinverse' := r.inverseProgram.eval_mono hinverseTime hinverse
      have hrank' := rankProgram.eval_mono hrankTime hrank
      have haccept : rangeResult.accept = true := (hrangeCorrect.mpr ⟨x, rfl⟩)
      change r.rangeProgram.eval (T (List.length (r.map x))) (r.map x) =
        some rangeResult at hrange'
      change r.inverseProgram.eval (T (List.length (r.map x))) (r.map x) =
        some inverseResult at hinverse'
      change rankProgram.eval (T (List.length (r.map x))) x =
        some rankResult at hrank'
      refine ⟨{
        rankResult with
        steps := rangeResult.steps + (inverseResult.steps + rankResult.steps)
      }, ?_, ?_⟩
      · simp [rankTransportProgram, trueProgram, Program.eval, hrange',
          haccept, hinverse', hinverseOut, hinverseValue, hrank']
      · simpa [r.transport_rank_map μ x] using hrankOut
    · have haccept : rangeResult.accept = false := by
        cases h : rangeResult.accept
        · rfl
        · exact False.elim (hy (hrangeCorrect.mp h))
      change r.rangeProgram.eval (T (List.length y)) y =
        some rangeResult at hrange'
      refine ⟨⟨false, encodeNat 0, rangeResult.steps + 1⟩, ?_, ?_⟩
      · simp [rankTransportProgram, Program.eval, hrange', haccept]
      · simp [r.transport_rank_eq μ y, hy]

/-- The map into its transported distribution has exact rank domination. -/
def distributionalReduction (μ : Subprobability) :
    InjectiveDistributionalReduction ⟨L₁, μ⟩ ⟨L₂, r.transport μ⟩ where
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
  rankFactor := fun _ => 1
  rankFactor_polynomial := IsPolynomial.const 1
  rankFactor_monotone := monotone_const
  rank_domination := by
    intro x
    simp

end HonestInvertibleReduction

namespace InjectiveDistributionalReduction

/-- Injective distributional reductions compose. -/
noncomputable def trans {first middle last : DistributionalProblem}
    (r₁ : InjectiveDistributionalReduction first middle)
    (r₂ : InjectiveDistributionalReduction middle last) :
    InjectiveDistributionalReduction first last := by
  refine
    { map := fun x => r₂.map (r₁.map x)
      injective := r₂.injective.comp r₁.injective
      correct := fun x => (r₁.correct x).trans (r₂.correct (r₁.map x))
      program := .compose r₁.program r₂.program
      timeBound := fun n =>
        r₁.timeBound n + r₂.timeBound (r₁.lengthBound n)
      time_polynomial := r₁.time_polynomial.add
        (r₂.time_polynomial.comp r₁.length_polynomial)
      time_monotone := by
        intro a b hab
        exact Nat.add_le_add (r₁.time_monotone hab)
          (r₂.time_monotone (r₁.length_monotone hab))
      computed := ?_
      lengthBound := fun n => r₂.lengthBound (r₁.lengthBound n)
      length_polynomial := r₂.length_polynomial.comp r₁.length_polynomial
      length_monotone := r₂.length_monotone.comp r₁.length_monotone
      length_bound := fun x => (r₂.length_bound (r₁.map x)).trans
        (r₂.length_monotone (r₁.length_bound x))
      rankFactor := fun n =>
        r₁.rankFactor n * r₂.rankFactor (r₁.lengthBound n)
      rankFactor_polynomial := r₁.rankFactor_polynomial.mul
        (r₂.rankFactor_polynomial.comp r₁.length_polynomial)
      rankFactor_monotone := by
        intro a b hab
        exact Nat.mul_le_mul (r₁.rankFactor_monotone hab)
          (r₂.rankFactor_monotone (r₁.length_monotone hab))
      rank_domination := ?_ }
  · intro x
    obtain ⟨result₁, hresult₁, hout₁⟩ := r₁.computed x
    obtain ⟨result₂, hresult₂, hout₂⟩ := r₂.computed (r₁.map x)
    let T := r₁.timeBound (len x) +
      r₂.timeBound (r₁.lengthBound (len x))
    have htime₁ : r₁.timeBound (len x) ≤ T := Nat.le_add_right _ _
    have htime₂ : r₂.timeBound (len (r₁.map x)) ≤ T :=
      (r₂.time_monotone (r₁.length_bound x)).trans (Nat.le_add_left _ _)
    have hresult₁' := r₁.program.eval_mono htime₁ hresult₁
    have hresult₂' := r₂.program.eval_mono htime₂ hresult₂
    refine ⟨{ result₂ with steps := result₁.steps + result₂.steps }, ?_, hout₂⟩
    change (Program.compose r₁.program r₂.program).eval T x =
      some { result₂ with steps := result₁.steps + result₂.steps }
    simp [Program.eval, hresult₁', hout₁, hresult₂']
  intro x
  calc
    last.distribution.rank (r₂.map (r₁.map x))
        ≤ r₂.rankFactor (len (r₁.map x)) *
            middle.distribution.rank (r₁.map x) :=
      r₂.rank_domination (r₁.map x)
    _ ≤ r₂.rankFactor (r₁.lengthBound (len x)) *
            middle.distribution.rank (r₁.map x) := by
      gcongr
      exact r₂.rankFactor_monotone (r₁.length_bound x)
    _ ≤ r₂.rankFactor (r₁.lengthBound (len x)) *
            (r₁.rankFactor (len x) * first.distribution.rank x) := by
      gcongr
      exact r₁.rank_domination x
    _ = (r₁.rankFactor (len x) *
            r₂.rankFactor (r₁.lengthBound (len x))) *
            first.distribution.rank x := by
      simp [Nat.mul_assoc, Nat.mul_comm]

end InjectiveDistributionalReduction

/--
**TR1995, Theorem 4.4.**  The paper defines NP-average completeness to include
membership in NP, while an injective reduction only controls the image of its
map.  We therefore state the surrounding Section 4 assumption `L₂ ∈ NP`
explicitly; it cannot be derived for arbitrary behavior of `L₂` off the image.
-/
theorem theorem_4_4 {L₁ L₂ : Set Bitstring}
    (r : HonestInvertibleReduction L₁ L₂)
    (hL₂NP : InNP L₂)
    (hL₁ : IsNPAverageCompleteLanguage L₁) :
    IsNPAverageCompleteLanguage L₂ := by
  refine ⟨hL₂NP, ?_⟩
  intro source hsource
  obtain ⟨μ, hμRankable, sourceToL₁⟩ := hL₁.2 source hsource
  exact ⟨r.transport μ, r.transport_rankable hμRankable,
    ⟨InjectiveDistributionalReduction.trans sourceToL₁.some
      (r.distributionalReduction μ)⟩⟩

end AvgCaseMls.Section4
