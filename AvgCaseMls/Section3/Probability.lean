/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import Mathlib

/-!
# Finite probability and asymptotic vocabulary
-/

namespace AvgCaseMls.Section3

open scoped BigOperators
open Filter

/-- A probability mass function on a finite type. -/
structure FinitePMF (α : Type*) [Fintype α] where
  prob : α → ℝ
  prob_nonneg : ∀ x, 0 ≤ prob x
  sum_prob : ∑ x, prob x = 1

namespace FinitePMF

noncomputable def eventProb {α : Type*} [Fintype α]
    (μ : FinitePMF α) (E : Set α) : ℝ := by
  classical
  exact Finset.sum (Finset.univ.filter (· ∈ E)) μ.prob

def expectation {α : Type*} [Fintype α]
    (μ : FinitePMF α) (X : α → ℝ) : ℝ :=
  ∑ x, μ.prob x * X x

theorem eventProb_nonneg {α : Type*} [Fintype α]
    (μ : FinitePMF α) (E : Set α) :
    0 ≤ μ.eventProb E := by
  classical
  exact Finset.sum_nonneg fun i _ => μ.prob_nonneg i

@[simp] theorem eventProb_univ {α : Type*} [Fintype α] (μ : FinitePMF α) :
    μ.eventProb Set.univ = 1 := by
  classical
  simp [eventProb, μ.sum_prob]

@[simp] theorem eventProb_empty {α : Type*} [Fintype α] (μ : FinitePMF α) :
    μ.eventProb ∅ = 0 := by
  classical
  simp [eventProb]

theorem eventProb_le_one {α : Type*} [Fintype α]
    (μ : FinitePMF α) (E : Set α) :
    μ.eventProb E ≤ 1 := by
  classical
  rw [← μ.sum_prob]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset _ _
  · intro i _ _
    exact μ.prob_nonneg i

theorem eventProb_compl {α : Type*} [Fintype α]
    (μ : FinitePMF α) (E : Set α) :
    μ.eventProb Eᶜ = 1 - μ.eventProb E := by
  classical
  rw [eventProb, eventProb, ← μ.sum_prob]
  have h := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun x : α => x ∈ E) μ.prob
  simp only [Set.mem_compl_iff] at h ⊢
  linarith

@[simp] theorem expectation_const {α : Type*} [Fintype α]
    (μ : FinitePMF α) (c : ℝ) :
    μ.expectation (fun _ => c) = c := by
  rw [expectation, ← Finset.sum_mul, μ.sum_prob, one_mul]

/-- Uniform probability on a finite nonempty type. -/
noncomputable def uniform (α : Type*) [Fintype α] [Nonempty α] : FinitePMF α where
  prob := fun _ => 1 / (Fintype.card α : ℝ)
  prob_nonneg := fun _ => div_nonneg zero_le_one (Nat.cast_nonneg _)
  sum_prob := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    exact mul_div_cancel₀ 1 hcard

@[simp] theorem uniform_apply (α : Type*) [Fintype α] [Nonempty α] (x : α) :
    (uniform α).prob x = 1 / Fintype.card α := rfl

theorem uniform_eventProb (α : Type*) [Fintype α] [Nonempty α] (E : Finset α) :
    (uniform α).eventProb (E : Set α) =
      (E.card : ℝ) / Fintype.card α := by
  classical
  simp [eventProb, uniform, div_eq_mul_inv, Finset.sum_const, nsmul_eq_mul]

end FinitePMF

/-- Events `E n` occur with high probability under `μ n`. -/
def WithHighProbability {Ω : Nat → Type*} [∀ n, Fintype (Ω n)]
    (μ : ∀ n, FinitePMF (Ω n)) (E : ∀ n, Set (Ω n)) : Prop :=
  Tendsto (fun n => (μ n).eventProb (E n)) atTop (nhds 1)

/-- Pointwise asymptotic `Ω`, with an eventually positive constant factor. -/
def IsAsymptoticOmega (f g : Nat → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, c * g n ≤ f n

theorem isAsymptoticOmega_iff (f g : Nat → ℝ) :
    IsAsymptoticOmega f g ↔
      ∃ c : ℝ, 0 < c ∧ ∃ N, ∀ n ≥ N, c * g n ≤ f n := by
  simp only [IsAsymptoticOmega, eventually_atTop]

end AvgCaseMls.Section3
