/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.Foundation.TimedNP

namespace AvgCaseMls.Foundation

/--
An injective polynomial-time distributional many-one reduction with the
paper's rank domination.  Polynomial output length is recorded independently
of machine time so later serialization proofs must account for wire size.
-/
structure InjectiveDistributionalReduction
    (source target : DistributionalProblem) where
  map : Bitstring → Bitstring
  injective : Function.Injective map
  correct : ∀ x, x ∈ source.language ↔ map x ∈ target.language
  program : Program
  timeBound : Nat → Nat
  time_polynomial : IsPolynomial timeBound
  time_monotone : Monotone timeBound
  computed : ComputesWithin program map timeBound
  lengthBound : Nat → Nat
  length_polynomial : IsPolynomial lengthBound
  length_monotone : Monotone lengthBound
  length_bound : ∀ x, len (map x) ≤ lengthBound (len x)
  rankFactor : Nat → Nat
  rankFactor_polynomial : IsPolynomial rankFactor
  rankFactor_monotone : Monotone rankFactor
  rank_domination :
    ∀ x, target.distribution.rank (map x) ≤
      rankFactor (len x) * source.distribution.rank x

/-- Optional stronger pointwise mass domination for transport arguments. -/
def HasProbabilityDomination
    {source target : DistributionalProblem}
    (r : InjectiveDistributionalReduction source target) : Prop :=
  ∃ factor : Nat → Nat, IsPolynomial factor ∧
    ∀ x, source.distribution.prob x ≤
      (factor (len x) : NNReal) * target.distribution.prob (r.map x)

/--
A distributional reduction with a polynomial-time inverse on its image and an
explicit polynomial honesty bound.  This is stronger than an injective
distributional reduction and is kept as a distinct notion.
-/
structure PolynomiallyInvertibleHonestReduction
    (source target : DistributionalProblem)
    extends InjectiveDistributionalReduction source target where
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
  honesty_bound : ∀ x, len x ≤ honestyBound (len (map x))

namespace InjectiveDistributionalReduction

def identityMachine : Machine :=
  ⟨#[.halt true]⟩

@[simp] theorem identityMachine_eval (x : Bitstring) :
    eval identityMachine 1 x = some ⟨true, x, 1⟩ := by
  cases x <;> simp [eval, evalFrom, step, identityMachine, initial, tapeOutput]

def refl (p : DistributionalProblem) :
    InjectiveDistributionalReduction p p := by
  refine
    { map := id
      injective := Function.injective_id
      correct := by simp
      program := .machine identityMachine
      timeBound := fun _ => 1
      time_polynomial := IsPolynomial.const 1
      time_monotone := monotone_const
      computed := ?_
      lengthBound := id
      length_polynomial := IsPolynomial.id
      length_monotone := monotone_id
      length_bound := by simp
      rankFactor := fun _ => 1
      rankFactor_polynomial := IsPolynomial.const 1
      rankFactor_monotone := monotone_const
      rank_domination := by simp }
  intro x
  exact ⟨⟨true, x, 1⟩, by simp, rfl⟩

@[simp] theorem refl_map (p : DistributionalProblem) (x : Bitstring) :
    (refl p).map x = x := by
  rfl

theorem refl_hasProbabilityDomination (p : DistributionalProblem) :
    HasProbabilityDomination (refl p) := by
  refine ⟨fun _ => 1, IsPolynomial.const 1, ?_⟩
  intro x
  simp

end InjectiveDistributionalReduction

namespace PolynomiallyInvertibleHonestReduction

def refl (p : DistributionalProblem) :
    PolynomiallyInvertibleHonestReduction p p where
  toInjectiveDistributionalReduction := InjectiveDistributionalReduction.refl p
  inverse := id
  inverseProgram := .machine InjectiveDistributionalReduction.identityMachine
  inverseTimeBound := fun _ => 1
  inverseTime_polynomial := IsPolynomial.const 1
  inverseTime_monotone := monotone_const
  inverse_computed := by
    intro x
    exact ⟨⟨true, x, 1⟩, by simp, rfl⟩
  left_inverse := fun _ => rfl
  rangeProgram := .machine InjectiveDistributionalReduction.identityMachine
  rangeTimeBound := fun _ => 1
  rangeTime_polynomial := IsPolynomial.const 1
  rangeTime_monotone := monotone_const
  range_decided := by
    intro x
    refine ⟨⟨true, x, 1⟩, by simp, ?_⟩
    simp
  honestyBound := id
  honesty_polynomial := IsPolynomial.id
  honesty_bound := by
    intro x
    change len x ≤ len x
    exact le_rfl

end PolynomiallyInvertibleHonestReduction

end AvgCaseMls.Foundation
