/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.TR1995
import AvgCaseMls.Foundation.AverageTime

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
open AvgCaseMls.Foundation

-- `standardMass` is declared in `AvgCaseMls/TR1995.lean`, immediately after
-- `example41Contribution`, so that it reuses that module's `Nat.AtLeastTwo`
-- `_proof_*` auxiliaries exactly as `Challenge.lean` does.

@[simp] theorem standardMass_empty : standardMass [] = 0 := by
  simp [standardMass]

theorem standardMass_of_length {x : List Bool} {n : ℕ}
    (hx : x.length = n) (hn : 0 < n) :
    standardMass x =
      (6 / Real.pi ^ 2) * (n : ℝ) ^ (-2 : ℝ) / (2 : ℝ) ^ n := by
  cases x with
  | nil => simp at hx; omega
  | cons b x => simp [standardMass, hx]

theorem standardMass_nonneg (x : List Bool) : 0 ≤ standardMass x := by
  by_cases hx : x.isEmpty
  · simp [standardMass, hx]
  · rw [standardMass, if_neg hx]
    positivity

/-- The displayed mass, packaged as a nonnegative real number. -/
noncomputable def standardProb (x : List Bool) : NNReal :=
  NNReal.mk (standardMass x) (standardMass_nonneg x)

@[simp] theorem standardProb_coe (x : List Bool) :
    (standardProb x : ℝ) = standardMass x :=
  NNReal.coe_mk _ _

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

/-- Every finite bitstring belongs to exactly one length shell. -/
noncomputable def shellEquiv : (Σ n, Shell n) ≃ List Bool :=
  Equiv.ofBijective (fun x => x.2.toList) ⟨by
    rintro ⟨n, x⟩ ⟨m, y⟩ h
    have hnm : n = m := by
      simpa only [shell_toList_length] using congrArg List.length h
    subst m
    exact Sigma.ext rfl (heq_of_eq (List.ofFn_injective h)), by
      intro x
      exact ⟨⟨x.length, x.get⟩, List.ofFn_get x⟩⟩

@[simp] theorem shellEquiv_apply (x : Σ n, Shell n) :
    shellEquiv x = x.2.toList :=
  rfl

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

@[simp] theorem shellMass_zero : shellMass 0 = 0 := by
  simp [shellMass, standardMass]

theorem summable_shellMass : Summable shellMass := by
  have hp : Summable (fun n : Nat => (n : ℝ) ^ (-2 : ℝ)) :=
    (Real.summable_nat_rpow).2 (by norm_num)
  apply (hp.mul_left (6 / Real.pi ^ 2)).congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  · exact (shellMass_eq (Nat.pos_of_ne_zero hn)).symm

-- Elaborating the dependent sigma-family summability criterion needs more
-- reduction than the project-wide default permits.
set_option maxHeartbeats 800000 in
theorem summable_standardMass_sigma :
      Summable (fun x : Σ n, Shell n => standardMass x.2.toList) := by
  apply (summable_sigma_of_nonneg
    (α := Nat) (β := Shell)
    (f := fun x : Σ n, Shell n => standardMass x.2.toList)
    (fun x => standardMass_nonneg x.2.toList)).2
  refine ⟨fun n => (hasSum_fintype _).summable, ?_⟩
  refine summable_shellMass.congr ?_
  intro n
  rw [shellMass, tsum_fintype]

theorem summable_standardMass : Summable standardMass := by
  have hsigma := summable_standardMass_sigma
  exact (shellEquiv.summable_iff.mp (by
    simpa only [Function.comp_def, shellEquiv_apply] using hsigma))

theorem summable_standardProb : Summable standardProb := by
  rw [← NNReal.summable_coe]
  simpa only [standardProb_coe] using summable_standardMass

theorem tsum_nat_rpow_neg_two :
    (∑' n : Nat, (n : ℝ) ^ (-2 : ℝ)) = Real.pi ^ 2 / 6 := by
  have hc : (∑' n : Nat, 1 / (n : ℂ) ^ 2) = (Real.pi : ℂ) ^ 2 / 6 := by
    calc
      (∑' n : Nat, 1 / (n : ℂ) ^ 2) = riemannZeta (2 : ℕ) :=
        (zeta_nat_eq_tsum_of_gt_one (k := 2) (by norm_num)).symm
      _ = (Real.pi : ℂ) ^ 2 / 6 := by simpa using riemannZeta_two
  have hr : (∑' n : Nat, 1 / (n : ℝ) ^ 2) = Real.pi ^ 2 / 6 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_tsum]
    simpa using hc
  rw [← hr]
  congr 1
  funext n
  rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg (Nat.cast_nonneg n)]
  norm_num [Real.rpow_natCast, div_eq_mul_inv]

theorem tsum_shellMass : (∑' n, shellMass n) = 1 := by
  calc
    (∑' n, shellMass n) =
        ∑' n : Nat, (6 / Real.pi ^ 2) * (n : ℝ) ^ (-2 : ℝ) := by
      apply tsum_congr
      intro n
      by_cases hn : n = 0
      · subst n
        simp
      · exact shellMass_eq (Nat.pos_of_ne_zero hn)
    _ = (6 / Real.pi ^ 2) * ∑' n : Nat, (n : ℝ) ^ (-2 : ℝ) := by
      rw [tsum_mul_left]
    _ = 1 := by
      rw [tsum_nat_rpow_neg_two]
      have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      field_simp

theorem tsum_standardMass : (∑' x, standardMass x) = 1 := by
  calc
    (∑' x, standardMass x) =
        ∑' x : Σ n, Shell n, standardMass x.2.toList :=
      (shellEquiv.tsum_eq standardMass).symm
    _ = ∑' n, ∑' x : Shell n, standardMass x.toList :=
      summable_standardMass_sigma.tsum_sigma
    _ = ∑' n, shellMass n := by
      congr 1
      funext n
      rw [tsum_fintype]
      rfl
    _ = 1 := tsum_shellMass

theorem tsum_standardProb : (∑' x, standardProb x) = 1 := by
  apply NNReal.eq
  rw [NNReal.coe_tsum]
  change (∑' x, (standardProb x : ℝ)) = (1 : ℝ)
  simpa only [standardProb_coe] using tsum_standardMass

theorem finite_standardProb_superlevel (x : List Bool) (hx : standardProb x ≠ 0) :
    Set.Finite {y : List Bool | standardProb x ≤ standardProb y} := by
  have hxpos : 0 < (standardProb x : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hx)
  have htend :
      Filter.Tendsto (fun y => (standardProb y : ℝ)) Filter.cofinite (nhds 0) :=
    (NNReal.summable_coe.mpr summable_standardProb).tendsto_cofinite_zero
  have hev :
      {y : List Bool | (standardProb y : ℝ) ∈
        Metric.ball 0 (standardProb x : ℝ)} ∈ Filter.cofinite :=
    htend (Metric.ball_mem_nhds 0 hxpos)
  have hfinite := (Filter.mem_cofinite.mp hev)
  apply hfinite.subset
  intro y hy
  change y ∉ {z : List Bool | (standardProb z : ℝ) ∈
    Metric.ball 0 (standardProb x : ℝ)}
  intro hball
  change (standardProb y : ℝ) ∈ Metric.ball 0 (standardProb x : ℝ) at hball
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)] at hball
  exact (not_lt_of_ge (by exact_mod_cast hy)) hball

/-- The infinite normalized distribution displayed in Example 4.1. -/
noncomputable def standardDistribution : Subprobability where
  prob := standardProb
  summable_prob := summable_standardProb
  tsum_le_one := by rw [tsum_standardProb]
  finite_superlevel := finite_standardProb_superlevel

@[simp] theorem standardDistribution_prob (x : List Bool) :
    (standardDistribution.prob x : ℝ) = standardMass x :=
  standardProb_coe x

theorem standardDistribution_mass : standardDistribution.mass = 1 := by
  exact tsum_standardProb

@[simp] theorem standardDistribution_prob_empty :
    standardDistribution.prob [] = 0 := by
  apply NNReal.eq
  simp

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

theorem levinTerm_nonneg {ε : ℝ} (x : List Bool) :
    0 ≤ levinTerm ε x := by
  unfold levinTerm inversePower
  exact div_nonneg
    (mul_nonneg (standardMass_nonneg x)
      (Real.rpow_nonneg (Nat.cast_nonneg (quadraticTime x)) _))
    (by positivity)

@[simp] theorem shellLevin_zero (ε : ℝ) : shellLevin ε 0 = 0 := by
  simp [shellLevin, levinTerm, standardMass]

theorem summable_levinTerm {ε : ℝ} (hε : 0 < ε) :
    Summable (levinTerm ε) := by
  have hsigma :
      Summable (fun x : Σ n, Shell n => levinTerm ε x.2.toList) := by
    apply (summable_sigma_of_nonneg
      (α := Nat) (β := Shell)
      (f := fun x : Σ n, Shell n => levinTerm ε x.2.toList)
      (fun x => levinTerm_nonneg x.2.toList)).2
    refine ⟨fun n => (hasSum_fintype _).summable, ?_⟩
    refine (summable_levinShellSeries hε).congr ?_
    intro n
    rw [levinShellSeries]
    by_cases hn : n = 0
    · subst n
      simp [levinTerm, standardMass, Shell.toList]
    · rw [if_neg hn, shellLevin, tsum_fintype]
  exact (shellEquiv.summable_iff.mp (by
    simpa only [Function.comp_def, shellEquiv_apply] using hsigma))

theorem tsum_levinTerm_eq_shells {ε : ℝ} (hε : 0 < ε) :
    (∑' x, levinTerm ε x) = ∑' n, levinShellSeries ε n := by
  have hsigma :
      Summable (fun x : Σ n, Shell n => levinTerm ε x.2.toList) := by
    exact shellEquiv.summable_iff.mpr (summable_levinTerm hε)
  calc
    (∑' x, levinTerm ε x) =
        ∑' x : Σ n, Shell n, levinTerm ε x.2.toList :=
      (shellEquiv.tsum_eq (levinTerm ε)).symm
    _ = ∑' n, ∑' x : Shell n, levinTerm ε x.toList := hsigma.tsum_sigma
    _ = ∑' n, levinShellSeries ε n := by
      apply tsum_congr
      intro n
      rw [tsum_fintype, levinShellSeries]
      by_cases hn : n = 0
      · subst n
        simp [levinTerm, standardMass, Shell.toList]
      · rw [if_neg hn, shellLevin]

theorem normalized_levin_list_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      Summable (fun x => levinTerm ε x / C) ∧
      (∑' x, levinTerm ε x / C) ≤ 1 := by
  obtain ⟨C, hC, hshell, hbound⟩ := normalized_levin_bound hε
  refine ⟨C, hC, (summable_levinTerm hε).div_const C, ?_⟩
  rw [tsum_div_const, tsum_levinTerm_eq_shells hε, ← tsum_div_const]
  exact hbound

/--
**TR1995 Example 4.1, full decider-linked statement.**

The displayed mass is a normalized infinite subprobability (indeed a
probability), with zero mass assigned to the empty string.  Every concrete
decider whose actual transition count is at most `|x|²` satisfies Levin's
probability-weighted average-time condition for a genuine real scale
`(C n)^(1 + ε)`, for every `ε > 0`.
-/
theorem example_4_1_full {L : Set (List Bool)} (d : Decider L)
    (hruntime : ∀ x, d.actualRuntime x ≤ x.length ^ 2)
    {ε : ℝ} (hε : 0 < ε) :
    standardDistribution.mass = 1 ∧
    standardDistribution.prob [] = 0 ∧
    (∀ x : List Bool, x ≠ [] →
      (standardDistribution.prob x : ℝ) =
        (6 / Real.pi ^ 2) * (x.length : ℝ) ^ (-2 : ℝ) /
          (2 : ℝ) ^ x.length) ∧
    ∃ C : ℝ, ∃ hC : 0 < C,
      AvgCaseMls.Foundation.IsLevinAverageTime d standardDistribution
        (AvgCaseMls.Foundation.RealTimeScale.scaledPower
          (1 + ε) C (by linarith) hC) ∧
      ∀ n : Nat,
        AvgCaseMls.Foundation.RealTimeScale.scaledPower
            (1 + ε) C (by linarith) hC n =
          (NNReal.mk C hC.le * n) ^ (1 + ε) := by
  refine ⟨standardDistribution_mass, standardDistribution_prob_empty, ?_, ?_⟩
  · intro x hx
    rw [standardDistribution_prob, standardMass, if_neg]
    simpa only [List.isEmpty_iff] using hx
  · obtain ⟨C, hC, hsum, hbound⟩ := normalized_levin_list_bound hε
    let hp : 0 < 1 + ε := by linarith
    let T := AvgCaseMls.Foundation.RealTimeScale.scaledPower (1 + ε) C hp hC
    let cost : List Bool → NNReal := fun x =>
      standardDistribution.prob x * T.inverse (d.actualRuntime x) /
        (max 1 x.length : Nat)
    have hcost_le : ∀ x, (cost x : ℝ) ≤ levinTerm ε x / C := by
      intro x
      rw [show (cost x : ℝ) =
        standardMass x *
            ((d.actualRuntime x : NNReal) ^ (1 / (1 + ε)) /
              NNReal.mk C hC.le : NNReal) /
            (max 1 x.length : Nat) by
          simp only [cost, T,
            AvgCaseMls.Foundation.RealTimeScale.scaledPower_inverse,
            standardDistribution_prob, NNReal.coe_div, NNReal.coe_mul,
            NNReal.coe_rpow, NNReal.coe_natCast, NNReal.coe_mk]]
      rw [levinTerm, inversePower]
      have hinv_nonneg : 0 ≤ 1 / (1 + ε) := (one_div_pos.mpr hp).le
      have hrpow :
          (d.actualRuntime x : ℝ) ^ (1 / (1 + ε)) ≤
            (x.length ^ 2 : ℕ) ^ (1 / (1 + ε) : ℝ) := by
        exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hruntime x) hinv_nonneg
      have hrpow' :
          (d.actualRuntime x : ℝ) ^ (1 / (1 + ε)) ≤
            ((x.length : ℝ) ^ 2) ^ (1 / (1 + ε) : ℝ) := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using hrpow
      have hden' : 0 < ((max 1 x.length : Nat) : ℝ) := by positivity
      have hmass : 0 ≤ standardMass x := standardMass_nonneg x
      rw [NNReal.coe_div, NNReal.coe_rpow, NNReal.coe_natCast, NNReal.coe_mk]
      simp only [quadraticTime, lenBot, Nat.cast_pow]
      calc
        standardMass x *
              (↑(d.actualRuntime x) ^ (1 / (1 + ε)) / C) /
              ↑(max 1 x.length) =
            (standardMass x * ↑(d.actualRuntime x) ^ (1 / (1 + ε)) /
              ↑(max 1 x.length)) / C := by ring
        _ ≤ (standardMass x * ((x.length : ℝ) ^ 2) ^ (1 / (1 + ε)) /
              ↑(max 1 x.length)) / C := by
          apply div_le_div_of_nonneg_right _ hC.le
          exact (div_le_div_iff_of_pos_right hden').2
            (mul_le_mul_of_nonneg_left hrpow' hmass)
    have hcost_summable_real : Summable (fun x => (cost x : ℝ)) :=
      Summable.of_nonneg_of_le (fun _ => by positivity) hcost_le hsum
    have hcost_summable : Summable cost :=
      NNReal.summable_coe.mp hcost_summable_real
    refine ⟨C, hC, ⟨?_, ?_⟩, ?_⟩
    · simpa only [cost, T] using hcost_summable
    · change (∑' x, cost x) ≤ 1
      apply NNReal.coe_le_coe.mp
      rw [NNReal.coe_tsum]
      calc
        (∑' x, (cost x : ℝ)) ≤ ∑' x, levinTerm ε x / C :=
          hcost_summable_real.tsum_le_tsum hcost_le hsum
        _ ≤ 1 := hbound
    · intro n
      rfl

end Example41
