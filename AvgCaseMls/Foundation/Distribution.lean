/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.Foundation.Complexity
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Data.Set.Card

namespace AvgCaseMls.Foundation

/--
An infinite subprobability distribution on all bitstrings.  The superlevel-set
condition is the standard finite-rank condition; it excludes infinitely many
atoms as heavy as a positive-mass input.
-/
structure Subprobability where
  prob : Bitstring → NNReal
  summable_prob : Summable prob
  tsum_le_one : tsum prob ≤ 1
  finite_superlevel :
    ∀ x, prob x ≠ 0 → Set.Finite {y : Bitstring | prob x ≤ prob y}

namespace Subprobability

noncomputable def mass (μ : Subprobability) : NNReal := ∑' x : Bitstring, μ.prob x

theorem mass_le_one (μ : Subprobability) : μ.mass ≤ 1 :=
  μ.tsum_le_one

/-- Rank is the cardinality of strings at least as probable as `x`. -/
noncomputable def rank (μ : Subprobability) (x : Bitstring) : Nat :=
  if μ.prob x = 0 then 0 else Set.ncard {y : Bitstring | μ.prob x ≤ μ.prob y}

@[simp] theorem rank_eq_zero_of_prob_eq_zero (μ : Subprobability) (x : Bitstring)
    (h : μ.prob x = 0) : μ.rank x = 0 := by
  simp [rank, h]

theorem rank_eq_ncard_of_prob_ne_zero (μ : Subprobability) (x : Bitstring)
    (h : μ.prob x ≠ 0) :
    μ.rank x = Set.ncard {y : Bitstring | μ.prob x ≤ μ.prob y} := by
  simp [rank, h]

theorem finite_rank_set (μ : Subprobability) (x : Bitstring)
    (h : μ.prob x ≠ 0) :
    Set.Finite {y : Bitstring | μ.prob x ≤ μ.prob y} :=
  μ.finite_superlevel x h

theorem rank_pos (μ : Subprobability) (x : Bitstring) (h : μ.prob x ≠ 0) :
    0 < μ.rank x := by
  rw [rank_eq_ncard_of_prob_ne_zero μ x h]
  apply (Set.ncard_pos (μ.finite_superlevel x h)).mpr
  refine ⟨x, ?_⟩
  change μ.prob x ≤ μ.prob x
  exact le_rfl

section Pushforward

variable (μ : Subprobability) (f : Bitstring → Bitstring)

/-- Extend the injective pushforward by zero away from the image. -/
noncomputable def pushforwardProb (y : Bitstring) : NNReal := by
  classical
  exact
    if y ∈ Set.range f then μ.prob (Function.invFun f y) else 0

@[simp] theorem pushforwardProb_map (hf : Function.Injective f) (x : Bitstring) :
    pushforwardProb μ f (f x) = μ.prob x := by
  simp [pushforwardProb, Function.leftInverse_invFun hf x]

theorem pushforwardProb_eq_zero_of_not_mem_range {y : Bitstring}
    (hy : y ∉ Set.range f) : pushforwardProb μ f y = 0 := by
  simp [pushforwardProb, hy]

theorem pushforwardProb_support_subset :
    Function.support (pushforwardProb μ f) ⊆ Set.range f := by
  intro y hy
  by_contra hyrange
  exact hy (pushforwardProb_eq_zero_of_not_mem_range μ f hyrange)

theorem summable_pushforwardProb (hf : Function.Injective f) :
    Summable (pushforwardProb μ f) := by
  apply (hf.summable_iff (f := pushforwardProb μ f)
    (fun y hy => pushforwardProb_eq_zero_of_not_mem_range μ f (y := y) hy)).mp
  have heq : pushforwardProb μ f ∘ f = μ.prob := by
    funext x
    exact pushforwardProb_map μ f hf x
  rw [heq]
  exact μ.summable_prob

theorem tsum_pushforwardProb (hf : Function.Injective f) :
    ∑' y, pushforwardProb μ f y = ∑' x, μ.prob x := by
  symm
  calc
    ∑' x, μ.prob x = ∑' x, pushforwardProb μ f (f x) := by
      congr 1
      funext x
      exact (pushforwardProb_map μ f hf x).symm
    _ = ∑' y, pushforwardProb μ f y :=
      hf.tsum_eq (pushforwardProb_support_subset μ f)

noncomputable def pushforward (hf : Function.Injective f) : Subprobability where
  prob := pushforwardProb μ f
  summable_prob := summable_pushforwardProb μ f hf
  tsum_le_one := by
    rw [tsum_pushforwardProb μ f hf]
    exact μ.tsum_le_one
  finite_superlevel := by
    intro y hy
    have hyrange : y ∈ Set.range f := by
      by_contra h
      exact hy (pushforwardProb_eq_zero_of_not_mem_range μ f h)
    obtain ⟨x, rfl⟩ := hyrange
    have hx : μ.prob x ≠ 0 := by
      simpa [pushforwardProb_map μ f hf x] using hy
    have heq :
        {z : Bitstring | pushforwardProb μ f (f x) ≤ pushforwardProb μ f z} =
          f '' {w : Bitstring | μ.prob x ≤ μ.prob w} := by
      ext z
      constructor
      · intro hz
        have hzrange : z ∈ Set.range f := by
          by_contra hzr
          change pushforwardProb μ f (f x) ≤ pushforwardProb μ f z at hz
          rw [pushforwardProb_eq_zero_of_not_mem_range μ f hzr] at hz
          simpa [pushforwardProb_map μ f hf x, hx] using hz
        obtain ⟨w, rfl⟩ := hzrange
        refine ⟨w, ?_, rfl⟩
        simpa only [Set.mem_setOf_eq, pushforwardProb_map μ f hf] using hz
      · rintro ⟨w, hw, rfl⟩
        simpa only [Set.mem_setOf_eq, pushforwardProb_map μ f hf] using hw
    rw [heq]
    exact (μ.finite_superlevel x hx).image f

@[simp] theorem pushforward_prob_map (hf : Function.Injective f) (x : Bitstring) :
    (pushforward μ f hf).prob (f x) = μ.prob x :=
  pushforwardProb_map μ f hf x

theorem pushforward_mass (hf : Function.Injective f) :
    (pushforward μ f hf).mass = μ.mass :=
  tsum_pushforwardProb μ f hf

theorem rank_pushforward_map (hf : Function.Injective f) (x : Bitstring) :
    (pushforward μ f hf).rank (f x) = μ.rank x := by
  by_cases hx : μ.prob x = 0
  · simp [hx, pushforward_prob_map μ f hf x]
  · rw [rank_eq_ncard_of_prob_ne_zero _ _ (by
      simpa [pushforward_prob_map μ f hf x] using hx)]
    rw [rank_eq_ncard_of_prob_ne_zero μ x hx]
    have heq :
        {z : Bitstring |
            (pushforward μ f hf).prob (f x) ≤ (pushforward μ f hf).prob z} =
          f '' {w : Bitstring | μ.prob x ≤ μ.prob w} := by
      ext z
      constructor
      · intro hz
        have hzrange : z ∈ Set.range f := by
          by_contra hzr
          change pushforwardProb μ f (f x) ≤ pushforwardProb μ f z at hz
          rw [pushforwardProb_eq_zero_of_not_mem_range μ f hzr] at hz
          simpa [pushforwardProb_map μ f hf x, hx] using hz
        obtain ⟨w, rfl⟩ := hzrange
        refine ⟨w, ?_, rfl⟩
        simpa only [Set.mem_setOf_eq, pushforward_prob_map μ f hf] using hz
      · rintro ⟨w, hw, rfl⟩
        simpa only [Set.mem_setOf_eq, pushforward_prob_map μ f hf] using hw
    rw [heq, Set.ncard_image_of_injective _ hf]

open Classical in
theorem rank_pushforward_eq (hf : Function.Injective f) (y : Bitstring) :
    (pushforward μ f hf).rank y =
      if y ∈ Set.range f then μ.rank (Function.invFun f y) else 0 := by
  classical
  by_cases hy : y ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hy
    rw [if_pos ⟨x, rfl⟩]
    simpa [Function.leftInverse_invFun hf x] using
      rank_pushforward_map μ f hf x
  · rw [if_neg hy]
    apply rank_eq_zero_of_prob_eq_zero
    exact pushforwardProb_eq_zero_of_not_mem_range μ f hy

end Pushforward

end Subprobability

structure DistributionalProblem where
  language : Set Bitstring
  distribution : Subprobability

end AvgCaseMls.Foundation
