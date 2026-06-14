/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp

/-!
Average-case complexity definitions (Reischuk–Schindelhauer framework).

Extracted from [`arxiv.md`](../arxiv.md) §5.

**Phase 1A:** `Bitstring`, `len`, `Distribution`, `DistributionalProblem`, `IsPolynomial`.

**Phase 1B+:** `rank`, `T_inv`, `IsAvTime`, `AvP` — placeholders (`sorry`).
-/

open Finset

namespace AvCom

/-! ## Phase 1A — inputs, distributions, POL -/

/-- Binary inputs $x \in \\{0,1\\}^*$ (TR1995-711 §3.2). -/
abbrev Bitstring := List Bool

/-- Length $|x|$ as `List.length`. -/
def len (s : Bitstring) : Nat := s.length

/--
Length used in RS93 denominators: `max 1 |x|` so the empty string is guarded.
See `DEFINITION_FORKS.md`.
-/
def lenBot (s : Bitstring) : Nat := max 1 s.length

theorem lenBot_empty : lenBot ([] : Bitstring) = 1 := rfl

theorem lenBot_ne_zero (s : Bitstring) : 0 < lenBot s := by
  have : 1 ≤ lenBot s := le_max_left 1 s.length
  omega

/--
A **finite-support** probability distribution on bitstrings.

Literature: $\\mu : \\Sigma^* \\to [0,1]$ with $\\sum_x \\mu(x) \\le 1$.
We restrict to an explicit finite `support` so rank and testing are well-defined (Phase 1B).
-/
structure Distribution where
  support : Finset Bitstring
  prob : Bitstring → Real
  prob_nonneg : ∀ s, 0 ≤ prob s
  prob_zero_outside : ∀ s, s ∉ support → prob s = 0
  prob_sum_le_one : support.sum prob ≤ 1

namespace Distribution

/-- Total mass on the declared support. -/
noncomputable def mass (μ : Distribution) : Real :=
  μ.support.sum μ.prob

theorem mass_le_one (μ : Distribution) : μ.mass ≤ 1 :=
  μ.prob_sum_le_one

end Distribution

noncomputable def pointMassProb (x : Bitstring) (p : Real) (s : Bitstring) : Real :=
  if s = x then p else 0

noncomputable def uniformProb (S : Finset Bitstring) (s : Bitstring) : Real :=
  if s ∈ S then 1 / (S.card : Real) else 0

/-- Point mass $p$ on a single string (requires $0 \\le p \\le 1$). -/
noncomputable def pointMass (x : Bitstring) (p : Real)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Distribution where
  support := {x}
  prob := pointMassProb x p
  prob_nonneg s := by
    unfold pointMassProb
    split_ifs with h
    · exact hp0
    · exact le_rfl
  prob_zero_outside s hs := by
    unfold pointMassProb
    by_cases h : s = x
    · exfalso
      exact hs (mem_singleton.mpr h)
    · simp [h]
  prob_sum_le_one := by
    rw [sum_singleton]
    simp only [pointMassProb]
    exact hp1

/-- Uniform distribution on a nonempty finite support. -/
noncomputable def uniformOn (S : Finset Bitstring) (h : S.Nonempty) : Distribution where
  support := S
  prob := uniformProb S
  prob_nonneg s := by
    unfold uniformProb
    split_ifs with hs
    · exact div_nonneg zero_le_one (Nat.cast_nonneg S.card)
    · exact le_rfl
  prob_zero_outside s hs := by
    unfold uniformProb
    by_cases hmem : s ∈ S
    · exfalso
      exact hs hmem
    · simp [hmem]
  prob_sum_le_one := by
    have hcard0 : (0 : Real) < S.card :=
      Nat.cast_pos.mpr (card_pos.mpr h)
    have hsum : (S.sum (uniformProb S) : Real) = S.sum fun _ => 1 / (S.card : Real) :=
      sum_congr rfl fun s hs => by simp [uniformProb, hs]
    calc
      (S.sum (uniformProb S) : Real) = S.sum fun _ => 1 / (S.card : Real) := hsum
      _ = (S.card : Real) * (1 / (S.card : Real)) := by rw [sum_const, nsmul_eq_mul]
      _ = 1 := by
        have hne : (S.card : Real) ≠ 0 := Nat.cast_ne_zero.mpr (card_pos.mpr h).ne'
        field_simp [hne]
      _ ≤ 1 := le_rfl

theorem uniformOn_mass (S : Finset Bitstring) (h : S.Nonempty) : (uniformOn S h).mass = 1 := by
  unfold Distribution.mass uniformOn
  have hsum : (S.sum (uniformProb S) : Real) = S.sum fun _ => 1 / (S.card : Real) :=
    sum_congr rfl fun s hs => by simp [uniformProb, hs]
  calc
    (S.sum (uniformProb S) : Real) = S.sum fun _ => 1 / (S.card : Real) := hsum
    _ = (S.card : Real) * (1 / (S.card : Real)) := by rw [sum_const, nsmul_eq_mul]
    _ = 1 := by
      have hne : (S.card : Real) ≠ 0 := Nat.cast_ne_zero.mpr (card_pos.mpr h).ne'
      field_simp [hne]

/--
A **distributional problem** $(L, \\mu)$: a language over bitstrings paired with a distribution.
-/
structure DistributionalProblem where
  L : Set Bitstring
  μ : Distribution

/--
**POL** (polynomial complexity bounds): $T(n) \\le c n^k + c$ for some constants $c, k$.
-/
def IsPolynomial (T : Nat → Nat) : Prop :=
  ∃ c k : Nat, ∀ n, T n ≤ c * n ^ k + c

namespace IsPolynomial

theorem id : IsPolynomial id := ⟨1, 1, fun n => by simp⟩

theorem const (c : Nat) : IsPolynomial (fun _ => c) := ⟨c, 0, fun n => by simp⟩

theorem add_one (T : Nat → Nat) (h : IsPolynomial T) : IsPolynomial fun n => T n + 1 := by
  obtain ⟨c, k, hT⟩ := h
  refine ⟨c + 1, k, fun n => ?_⟩
  calc
    T n + 1 ≤ c * n ^ k + c + 1 := Nat.add_le_add_right (hT n) 1
    _ ≤ (c + 1) * n ^ k + (c + 1) := by
      rw [Nat.add_mul, Nat.one_mul]
      omega

end IsPolynomial

/-! ## Phase 1B — rank and inverse bounds (open) -/

noncomputable def rank (μ : Distribution) (x : Bitstring) : Nat :=
  if μ.prob x = 0 then 0
  else
    -- Phase 1B: |{ z ∈ μ.support : μ.prob z ≥ μ.prob x }|
    sorry

def T_inv (T : Nat → Nat) (m : Nat) : Nat :=
  -- Phase 1B: min { n | T n ≥ m }
  sorry

/-! ## Phase 1C — average time (depends on 1B) -/

def IsAvTime (T : Nat → Nat) (f : Bitstring → Nat) (μ : Distribution) : Prop :=
  ∀ l : Nat, l ≥ 1 →
    ∃ S : Finset Bitstring,
      (∀ x, x ∈ S ↔ rank μ x ≤ l) ∧
      S.sum (fun x => (T_inv T (f x) : Real) / (lenBot x : Real)) ≤ (l : Real)

/-! ## Phase 1D — AvP (depends on 1C) -/

def AvP (prob : DistributionalProblem) : Prop :=
  ∃ f : Bitstring → Nat, ∃ T : Nat → Nat,
    IsPolynomial T ∧ IsAvTime T f prob.μ

end AvCom
