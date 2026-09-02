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

end Subprobability

structure DistributionalProblem where
  language : Set Bitstring
  distribution : Subprobability

end AvgCaseMls.Foundation
