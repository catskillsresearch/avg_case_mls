/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.Section3.RandomCNF

/-!
# High-probability unsatisfiability of dense random ordinary CNFs
-/

namespace AvgCaseMls.Section3

open scoped BigOperators
open Filter

def falsifyingClause (a : Assignment n) (S : ClauseVariables n k) :
    OrdinaryClause n k :=
  ⟨S, fun x => !(a x.val)⟩

theorem evalLiteral_eq_false_iff_sign {a : Assignment n} {x : Fin n} {b : Bool} :
    evalLiteral a (x, b) = false ↔ b = !(a x) := by
  cases hax : a x <;> cases b <;> simp [evalLiteral, hax]

theorem satisfies_ordinary_iff (a : Assignment n) (C : OrdinaryClause n k) :
    SatisfiesClause a C.lits ↔
      ∃ x : C.1.val, evalLiteral a (x.val, C.2 x) = true := by
  simp [SatisfiesClause, OrdinaryClause.lits]

theorem not_satisfies_ordinary_iff (a : Assignment n) (C : OrdinaryClause n k) :
    ¬ SatisfiesClause a C.lits ↔ C.2 = fun x => !(a x.val) := by
  rw [satisfies_ordinary_iff]
  constructor
  · intro h
    funext x
    apply (evalLiteral_eq_false_iff_sign).mp
    cases he : evalLiteral a (x.val, C.2 x)
    · rfl
    · exact absurd ⟨x, he⟩ h
  · intro h ⟨x, hx⟩
    rw [h] at hx
    simp [evalLiteral] at hx

noncomputable def falsifiedClauses (a : Assignment n) (k : Nat) :
    Finset (OrdinaryClause n k) := by
  classical
  exact Finset.univ.filter fun C => ¬ SatisfiesClause a C.lits

noncomputable def satisfyingClauses (a : Assignment n) (k : Nat) :
    Finset (OrdinaryClause n k) := by
  classical
  exact Finset.univ.filter fun C => SatisfiesClause a C.lits

theorem falsifiedClauses_eq_image (a : Assignment n) (k : Nat) :
    falsifiedClauses a k =
      Finset.univ.image (falsifyingClause a : ClauseVariables n k → OrdinaryClause n k) := by
  classical
  ext C
  simp only [falsifiedClauses, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image]
  rw [not_satisfies_ordinary_iff]
  constructor
  · intro h
    exact ⟨C.1, Sigma.ext rfl (heq_of_eq h.symm)⟩
  · rintro ⟨S, rfl⟩
    rfl

@[simp] theorem falsifiedClauses_card (a : Assignment n) (k : Nat) :
    (falsifiedClauses a k).card = n.choose k := by
  rw [falsifiedClauses_eq_image, Finset.card_image_iff.mpr]
  · simp [clauseVariables_card]
  intro S _ T _ h
  exact congrArg Sigma.fst h

@[simp] theorem satisfyingClauses_card (a : Assignment n) (k : Nat) :
    (satisfyingClauses a k).card = n.choose k * (2 ^ k - 1) := by
  classical
  have heq : satisfyingClauses a k =
      Finset.univ \ falsifiedClauses a k := by
    ext C
    simp [satisfyingClauses, falsifiedClauses]
  rw [heq, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    ordinaryClause_cardinality, falsifiedClauses_card]
  simpa using (Nat.mul_sub_left_distrib (n.choose k) (2 ^ k) 1).symm

noncomputable def assignmentSatisfactionEvent (a : Assignment n) (m k : Nat) :
    Finset (OrdinaryCNF n m k) := by
  classical
  exact Finset.univ.filter fun F => SatisfiesCNF a (eraseOrdinary F)

@[simp] theorem mem_assignmentSatisfactionEvent (a : Assignment n) (m k : Nat)
    (F : OrdinaryCNF n m k) :
    F ∈ assignmentSatisfactionEvent a m k ↔
      SatisfiesCNF a (eraseOrdinary F) := by
  classical
  simp [assignmentSatisfactionEvent]

private noncomputable def assignmentEventEquiv (a : Assignment n) (m k : Nat) :
    {F // F ∈ assignmentSatisfactionEvent a m k} ≃
      (Fin m → {C // C ∈ satisfyingClauses a k}) where
  toFun F i := ⟨F.val i, by
    have hp := (mem_assignmentSatisfactionEvent a m k F.val).mp F.property
    simp only [satisfyingClauses, Finset.mem_filter, Finset.mem_univ, true_and]
    change SatisfiesClause a (F.val i).lits
    exact hp i⟩
  invFun f := ⟨fun i => (f i).val, by
    apply (mem_assignmentSatisfactionEvent a m k _).mpr
    intro i
    change SatisfiesClause a ((f i).val).lits
    simpa [satisfyingClauses] using (f i).property⟩
  left_inv F := Subtype.ext (funext fun _ => rfl)
  right_inv f := funext fun _ => Subtype.ext rfl

@[simp] theorem assignmentSatisfactionEvent_card (a : Assignment n) (m k : Nat) :
    (assignmentSatisfactionEvent a m k).card =
      (n.choose k * (2 ^ k - 1)) ^ m := by
  rw [← Fintype.card_coe, Fintype.card_congr (assignmentEventEquiv a m k),
    Fintype.card_fun, Fintype.card_fin, Fintype.card_coe,
    satisfyingClauses_card]

theorem clauseSatisfactionRatio {n k : Nat} (hk : k ≤ n) :
    ((n.choose k * (2 ^ k - 1) : Nat) : ℝ) /
        (n.choose k * 2 ^ k : Nat) =
      1 - (2 : ℝ) ^ (-(k : ℤ)) := by
  have hchoose : (n.choose k : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast Nat.choose_pos hk)
  push_cast
  rw [mul_div_mul_left _ _ hchoose]
  rw [Nat.cast_sub (one_le_pow₀ (by norm_num : 1 ≤ (2 : Nat)))]
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  rw [zpow_neg, zpow_natCast]
  field_simp

theorem assignment_satisfaction_probability (hk : k ≤ n) (a : Assignment n) (m : Nat) :
    (randomCNFOfLE n m k hk).eventProb
        (assignmentSatisfactionEvent a m k : Set (OrdinaryCNF n m k)) =
      (1 - (2 : ℝ) ^ (-(k : ℤ))) ^ m := by
  letI : Nonempty (OrdinaryClause n k) := ordinaryClause_nonempty hk
  change (FinitePMF.uniform (OrdinaryCNF n m k)).eventProb
      (assignmentSatisfactionEvent a m k : Set (OrdinaryCNF n m k)) = _
  rw [FinitePMF.uniform_eventProb,
    assignmentSatisfactionEvent_card, ordinaryCNF_cardinality]
  rw [Nat.cast_pow, Nat.cast_pow, ← div_pow]
  rw [clauseSatisfactionRatio hk]

/-- All ordered ordinary CNFs satisfied by at least one assignment. -/
noncomputable def satisfiableEvent (n m k : Nat) : Finset (OrdinaryCNF n m k) := by
  classical
  exact Finset.univ.filter fun F => Satisfiable (eraseOrdinary F)

theorem satisfiableEvent_subset_biUnion (n m k : Nat) :
    satisfiableEvent n m k ⊆
      Finset.univ.biUnion fun a : Assignment n => assignmentSatisfactionEvent a m k := by
  classical
  intro F hF
  simp only [satisfiableEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hF
  rcases hF with ⟨a, ha⟩
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨a, by simp [assignmentSatisfactionEvent, ha]⟩

theorem satisfiableEvent_card_le (n m k : Nat) :
    (satisfiableEvent n m k).card ≤
      2 ^ n * (n.choose k * (2 ^ k - 1)) ^ m := by
  classical
  calc
    _ ≤ (Finset.univ.biUnion fun a : Assignment n =>
        assignmentSatisfactionEvent a m k).card :=
      Finset.card_le_card (satisfiableEvent_subset_biUnion n m k)
    _ ≤ ∑ a : Assignment n, (assignmentSatisfactionEvent a m k).card :=
      Finset.card_biUnion_le
    _ = _ := by simp

theorem satisfiable_probability_le (hk : k ≤ n) (m : Nat) :
    (randomCNFOfLE n m k hk).eventProb
        (satisfiableEvent n m k : Set (OrdinaryCNF n m k)) ≤
      (2 : ℝ) ^ n * (1 - (2 : ℝ) ^ (-(k : ℤ))) ^ m := by
  letI : Nonempty (OrdinaryClause n k) := ordinaryClause_nonempty hk
  change (FinitePMF.uniform (OrdinaryCNF n m k)).eventProb
      (satisfiableEvent n m k : Set (OrdinaryCNF n m k)) ≤ _
  rw [FinitePMF.uniform_eventProb]
  calc
    ((satisfiableEvent n m k).card : ℝ) /
        Fintype.card (OrdinaryCNF n m k) ≤
      (2 ^ n * (n.choose k * (2 ^ k - 1)) ^ m : Nat) /
        Fintype.card (OrdinaryCNF n m k) := by
      gcongr
      exact satisfiableEvent_card_le n m k
    _ = (2 : ℝ) ^ n * (1 - (2 : ℝ) ^ (-(k : ℤ))) ^ m := by
      rw [ordinaryCNF_cardinality]
      push_cast
      rw [mul_div_assoc, ← div_pow]
      have hr := clauseSatisfactionRatio hk
      push_cast at hr
      rw [hr]

theorem exp_seven_tenths_gt_two : (2 : ℝ) < Real.exp (7 / 10 : ℝ) := by
  have h := Real.exp_bound (x := (7 / 10 : ℝ)) (n := 8) (by norm_num) (by norm_num)
  rw [abs_of_nonneg (by positivity : 0 ≤ (7 / 10 : ℝ))] at h
  have hl := neg_le_of_abs_le h
  norm_num [Finset.sum_range_succ, Nat.factorial] at hl
  linarith

theorem density_base_lt_one {c k : Nat}
    (hdensity : (7 / 10 : ℝ) ≤ (c : ℝ) * (2 : ℝ) ^ (-(k : ℤ))) :
    (2 : ℝ) * (1 - (2 : ℝ) ^ (-(k : ℤ))) ^ c < 1 := by
  have hxpos : 0 < (2 : ℝ) ^ (-(k : ℤ)) := zpow_pos (by norm_num) _
  have hxle : (2 : ℝ) ^ (-(k : ℤ)) ≤ 1 := by
    rw [zpow_neg, zpow_natCast]
    exact (inv_le_one₀ (by positivity)).mpr (one_le_pow₀ (by norm_num))
  calc
    2 * (1 - (2 : ℝ) ^ (-(k : ℤ))) ^ c
        ≤ 2 * Real.exp (-((c : ℝ) * (2 : ℝ) ^ (-(k : ℤ)))) := by
          gcongr
          calc
            (1 - (2 : ℝ) ^ (-(k : ℤ))) ^ c
                ≤ (Real.exp (-((2 : ℝ) ^ (-(k : ℤ))))) ^ c := by
                  gcongr
                  exact Real.one_sub_le_exp_neg _
            _ = Real.exp (-((c : ℝ) * (2 : ℝ) ^ (-(k : ℤ)))) := by
                  rw [← Real.exp_nat_mul]
                  congr 2
                  ring
    _ ≤ 2 * Real.exp (-(7 / 10 : ℝ)) := by
          gcongr
    _ < 1 := by
          rw [Real.exp_neg]
          exact (div_lt_one (Real.exp_pos _)).mpr exp_seven_tenths_gt_two

/--
The asymptotic family starts at `k` variables: index `r` represents
`n = r + k` variables and exactly `c * n` independently sampled clauses.
Discarding the finitely many impossible sizes `n < k` does not alter a
high-probability statement.
-/
noncomputable def denseRandomCNF (c k r : Nat) :
    FinitePMF (OrdinaryCNF (r + k) (c * (r + k)) k) :=
  randomCNFOfLE (r + k) (c * (r + k)) k (Nat.le_add_left k r)

noncomputable def denseSatisfiableEvent (c k r : Nat) :
    Set (OrdinaryCNF (r + k) (c * (r + k)) k) :=
  satisfiableEvent (r + k) (c * (r + k)) k

noncomputable def denseUnsatisfiableEvent (c k r : Nat) :
    Set (OrdinaryCNF (r + k) (c * (r + k)) k) :=
  (denseSatisfiableEvent c k r)ᶜ

theorem dense_satisfiable_probability_le (c k r : Nat) :
    (denseRandomCNF c k r).eventProb (denseSatisfiableEvent c k r) ≤
      ((2 : ℝ) * (1 - (2 : ℝ) ^ (-(k : ℤ))) ^ c) ^ (r + k) := by
  have h := satisfiable_probability_le (n := r + k) (k := k)
    (Nat.le_add_left k r) (c * (r + k))
  simpa only [denseRandomCNF, denseSatisfiableEvent, pow_mul, mul_pow] using h

theorem dense_satisfiable_probability_tendsto_zero {c k : Nat}
    (hdensity : (7 / 10 : ℝ) ≤ (c : ℝ) * (2 : ℝ) ^ (-(k : ℤ))) :
    Tendsto (fun r => (denseRandomCNF c k r).eventProb
      (denseSatisfiableEvent c k r)) atTop (nhds 0) := by
  let q : ℝ := 2 * (1 - (2 : ℝ) ^ (-(k : ℤ))) ^ c
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    apply mul_nonneg (by norm_num)
    apply pow_nonneg
    rw [sub_nonneg, zpow_neg, zpow_natCast]
    exact (inv_le_one₀ (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hq_lt : q < 1 := density_base_lt_one hdensity
  have hgeom : Tendsto (fun r : Nat => q ^ r) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq_lt
  have hshift : Tendsto (fun r : Nat => q ^ (r + k)) atTop (nhds 0) :=
    (Filter.tendsto_add_atTop_iff_nat k).2 hgeom
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hshift
  · intro r
    exact (denseRandomCNF c k r).eventProb_nonneg _
  · intro r
    exact dense_satisfiable_probability_le c k r

theorem dense_unsatisfiable_probability_tendsto_one {c k : Nat}
    (hdensity : (7 / 10 : ℝ) ≤ (c : ℝ) * (2 : ℝ) ^ (-(k : ℤ))) :
    Tendsto (fun r => (denseRandomCNF c k r).eventProb
      (denseUnsatisfiableEvent c k r)) atTop (nhds 1) := by
  have hzero := dense_satisfiable_probability_tendsto_zero hdensity
  have hone : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hsub := hone.sub hzero
  simpa [denseUnsatisfiableEvent, FinitePMF.eventProb_compl] using hsub

/-- CS87/TR1995's elementary high-probability unsatisfiability component. -/
theorem random_cnf_unsatisfiable_withHighProbability {c k : Nat}
    (_hk : 3 ≤ k)
    (hdensity : (7 / 10 : ℝ) ≤ (c : ℝ) * (2 : ℝ) ^ (-(k : ℤ))) :
    WithHighProbability (denseRandomCNF c k) (denseUnsatisfiableEvent c k) :=
  dense_unsatisfiable_probability_tendsto_one hdensity

end AvgCaseMls.Section3
