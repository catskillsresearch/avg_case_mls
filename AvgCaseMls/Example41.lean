/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.TR1995

/-!
# The full shell calculation in Example 4.1

This file formalizes the standard mass from Example 4.1 directly on
`List Bool`.  It does not use `AvCom.Distribution`, because that structure has
finite support whereas the standard distribution has infinite support.

The report writes `|x|⁻²` and `1 / |x|`, which are undefined at the empty
string.  Following the report convention, `standardMass []` is set to zero;
for the Levin denominator we use `AvCom.lenBot`, the repository's transparent
`max 1 |x|` guard.  Thus the empty string contributes zero and every nonempty
shell agrees exactly with the displayed formula in the report.
-/

namespace Example41

open scoped BigOperators
open AvCom

/-- The report's standard mass, with zero assigned to the empty string. -/
noncomputable def standardMass (x : List Bool) : ℝ :=
  if x.isEmpty then 0
  else (6 / Real.pi ^ 2) * (x.length : ℝ) ^ (-2 : ℝ) / (2 : ℝ) ^ x.length

@[simp] theorem standardMass_empty : standardMass [] = 0 := by
  simp [standardMass]

theorem standardMass_of_length {x : List Bool} {n : ℕ}
    (hx : x.length = n) (hn : 0 < n) :
    standardMass x =
      (6 / Real.pi ^ 2) * (n : ℝ) ^ (-2 : ℝ) / (2 : ℝ) ^ n := by
  cases x with
  | nil => simp at hx; omega
  | cons b x => simp [standardMass, hx]

/-- Bitstrings in the length-`n` shell, represented without a finite-support fork. -/
abbrev Shell (n : ℕ) := Fin n → Bool

/-- Convert a shell element to the requested `List Bool` input representation. -/
def Shell.toList {n : ℕ} (x : Shell n) : List Bool :=
  List.ofFn x

@[simp] theorem shell_toList_length {n : ℕ} (x : Shell n) :
    x.toList.length = n := by
  simp [Shell.toList]

/-- There are exactly `2^n` Boolean strings in the length-`n` shell. -/
theorem shell_card (n : ℕ) : Fintype.card (Shell n) = 2 ^ n := by
  simp [Shell]

/-- Total standard mass in a shell. -/
noncomputable def shellMass (n : ℕ) : ℝ :=
  ∑ x : Shell n, standardMass x.toList

/-- Shell counting cancels the per-string factor `2⁻ⁿ`. -/
theorem shellMass_eq {n : ℕ} (hn : 0 < n) :
    shellMass n = (6 / Real.pi ^ 2) * (n : ℝ) ^ (-2 : ℝ) := by
  rw [shellMass]
  simp_rw [standardMass_of_length (shell_toList_length _) hn]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : Finset.card (Finset.univ : Finset (Shell n)) = 2 ^ n := by
    exact shell_card n
  rw [hcard, Nat.cast_pow, Nat.cast_ofNat]
  have htwo : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

/-- Quadratic running time on an input of length `n`. -/
def quadraticTime (x : List Bool) : ℕ :=
  x.length ^ 2

/--
The real-valued inverse of the proposed `n ↦ n^(1+ε)` bound.

This is the exact analytic inverse used in the paper's big-O calculation;
the discrete `AvCom.T_inv` is not suitable for a nonintegral exponent.
-/
noncomputable def inversePower (ε : ℝ) (t : ℕ) : ℝ :=
  (t : ℝ) ^ (1 / (1 + ε) : ℝ)

/-- One input's probability-weighted Levin expression. -/
noncomputable def levinTerm (ε : ℝ) (x : List Bool) : ℝ :=
  standardMass x * inversePower ε (quadraticTime x) / (lenBot x : ℝ)

/-- The complete probability-weighted Levin expression on shell `n`. -/
noncomputable def shellLevin (ε : ℝ) (n : ℕ) : ℝ :=
  ∑ x : Shell n, levinTerm ε x.toList

/--
On every nonempty shell, quadratic time followed by the inverse
`n^(1+ε)` bound is `n^(2/(1+ε))`.
-/
theorem inversePower_quadratic {ε : ℝ} {n : ℕ} (hn : 0 < n) :
    inversePower ε (n ^ 2) = (n : ℝ) ^ (2 / (1 + ε) : ℝ) := by
  rw [inversePower, Nat.cast_pow, ← Real.rpow_natCast]
  rw [← Real.rpow_mul (Nat.cast_pos.mpr hn).le]
  congr 1
  ring

/-- The exact shell term is the p-series term already identified in `TR1995`. -/
theorem shellLevin_eq_contribution {ε : ℝ} {n : ℕ} (hn : 0 < n) :
    shellLevin ε n = TR1995.example41Contribution ε n := by
  rw [shellLevin]
  simp_rw [levinTerm, standardMass_of_length (shell_toList_length _) hn,
    quadraticTime, shell_toList_length, inversePower_quadratic hn]
  have hlenBot : ∀ x : Shell n, lenBot x.toList = n := by
    intro x
    simp [lenBot, shell_toList_length, Nat.one_le_iff_ne_zero, hn.ne']
  simp_rw [hlenBot]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : Finset.card (Finset.univ : Finset (Shell n)) = 2 ^ n := by
    exact shell_card n
  rw [hcard, Nat.cast_pow, Nat.cast_ofNat]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have htwo : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [TR1995.example41Contribution, TR1995.example41Exponent]
  field_simp
  calc
    (n : ℝ) ^ (-2 : ℝ) * (n : ℝ) ^ (2 / (1 + ε) : ℝ) =
        (n : ℝ) ^ ((-2 : ℝ) + 2 / (1 + ε)) :=
      (Real.rpow_add (Nat.cast_pos.mpr hn) _ _).symm
    _ = (n : ℝ) ^ ((1 : ℝ) + (-3 + 2 / (1 + ε))) := by
      congr 1
      ring
    _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-3 + 2 / (1 + ε)) :=
      Real.rpow_add (Nat.cast_pos.mpr hn) _ _
    _ = (n : ℝ) * (n : ℝ) ^ (-3 + 2 / (1 + ε)) := by
      rw [Real.rpow_one]

/-- The full sequence of shell contributions, with the empty shell included as zero. -/
noncomputable def levinShellSeries (ε : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else shellLevin ε n

theorem levinShellSeries_eq (ε : ℝ) :
    levinShellSeries ε = fun n =>
      if n = 0 then 0 else TR1995.example41Contribution ε n := by
  funext n
  by_cases hn : n = 0
  · simp [levinShellSeries, hn]
  · simp [levinShellSeries, hn, shellLevin_eq_contribution (Nat.pos_of_ne_zero hn)]

/--
**Example 4.1, full shell form.** For every `ε > 0`, the standard distribution
on Boolean strings makes the probability-weighted Levin expression for a
quadratic-time machine summable against the inverse `n^(1+ε)` bound.
-/
theorem summable_levinShellSeries {ε : ℝ} (hε : 0 < ε) :
    Summable (levinShellSeries ε) := by
  rw [levinShellSeries_eq]
  have hexp : TR1995.example41Exponent ε ≠ 0 :=
    ne_of_lt (lt_trans (TR1995.example41Exponent_lt_neg_one hε) (by norm_num))
  apply (TR1995.example_4_1 hε).congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp [TR1995.example41Contribution, hexp]
  · simp [hn]

/--
The hidden positive big-O constant can be chosen so that the complete shell
sum satisfies Levin's normalized `≤ 1` conclusion.
-/
theorem normalized_levin_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      Summable (levinShellSeries ε) ∧
      (∑' n : ℕ, levinShellSeries ε n / C) ≤ 1 := by
  have hsum := summable_levinShellSeries hε
  let S := ∑' n : ℕ, levinShellSeries ε n
  let C := max S 1
  refine ⟨C, lt_of_lt_of_le zero_lt_one (le_max_right _ _), hsum, ?_⟩
  rw [tsum_div_const]
  exact (div_le_one (lt_of_lt_of_le zero_lt_one (le_max_right S 1))).2
    (le_max_left S 1)

end Example41
