/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.NBH
import AvgCaseMls.NPMembership
import AvgCaseMls.EMLS

/-!
Phase **4B:** distributional reduction from NBH (Phase **4A**) into MLS satisfiability.

Literature: TR1995-711 §3.2 reduction with domination. The general TM→MLS translation for
arbitrary MLS formulas in paper scope is axiomatized as [`nbhToMlsMap`]; see
[`DEFINITION_FORKS.md`](../DEFINITION_FORKS.md).
-/

namespace Reduction

open MLS NBH AvCom EMLS

/-!
**Lean fork (general case):** [`nbhToMlsMap`] stands in for the full TR1995-711 compiler from
NBH instances to serialized MLS formulas (any expression in the paper's MLS fragment). The
step-function [`reduceNBHToSatMLSStep`] remains as an explicit domination scaffold on μ₀.
-/

axiom nbhToMlsMap : Bitstring → Bitstring

axiom nbhToMlsMap_correct :
  ∀ x, x ∈ NBHChecker ↔ nbhToMlsMap x ∈ SatMLSChecker

axiom nbhToMlsMap_lenBound :
  ∃ k0 k1 : Nat, ∀ x, lenBot (nbhToMlsMap x) ≤ k0 * (lenBot x) ^ k1

axiom nbhToMlsMap_domination :
  ∃ c0 c1 : Nat, 0 < c0 ∧ 0 < c1 ∧
    ∀ x, rank μ₁ (nbhToMlsMap x) ≤ c0 * (lenBot x) ^ c1 * rank μ₀ x

/-! ### Target formulas and encoding -/

def satTargetFormula : Formula :=
  Formula.rel (Relation.eq Term.empty Term.empty)

def unsatTargetFormula : Formula :=
  Formula.rel (Relation.neq Term.empty Term.empty)

def satTargetEnc : Bitstring :=
  serializeFormula satTargetFormula

def unsatTargetEnc : Bitstring :=
  serializeFormula unsatTargetFormula

theorem satTargetEnc_ne_unsatTargetEnc : satTargetEnc ≠ unsatTargetEnc := by
  native_decide

theorem satTargetEnc_in_checker : satTargetEnc ∈ SatMLSChecker := by
  rw [← verifySatMLS_true_iff]
  native_decide

theorem unsatTargetEnc_not_in_checker : unsatTargetEnc ∉ SatMLSChecker := by
  intro h
  have hver : verifySatMLS unsatTargetEnc [] = true := (verifySatMLS_true_iff unsatTargetEnc).mpr h
  have hf : verifySatMLS unsatTargetEnc [] = false := by
    simp [verifySatMLS, unsatTargetEnc, unsatTargetFormula, serializeFormula,
      decodeFormula?, decideMLSSat, formulaToConjunct?, decideConjunct,
      relationToLiteral?, literalToFormula]
    native_decide
  rw [hf] at hver
  exact nomatch hver

/-! ### Target distributional problem -/

def μ₁Support : Finset Bitstring :=
  {satTargetEnc}

theorem μ₁Support_nonempty : μ₁Support.Nonempty :=
  ⟨satTargetEnc, by simp [μ₁Support]⟩

noncomputable def μ₁ : Distribution :=
  uniformOn μ₁Support μ₁Support_nonempty

theorem μ₁_polRankable : IsPolRankable μ₁ :=
  IsPolRankable.uniformOn_polRankable μ₁Support μ₁Support_nonempty

noncomputable def satMLSProb : DistributionalProblem :=
  { L := SatMLSChecker, μ := μ₁ }

theorem satMLSProb_in_DistNP : InDistNP satMLSProb :=
  InDistNP.intro SatMLSChecker_in_NP μ₁_polRankable

/-! ### Reduction map -/

/--
Step-function scaffold on μ₀ support (domination witness only; not globally correct).
-/
def reduceNBHToSatMLSStep (x : Bitstring) : Bitstring :=
  if x ∈ μ₀Support then satTargetEnc else unsatTargetEnc

/--
Distributional reduction map used in [`nbhToSatMLS_red`]: axiomatized general TM→MLS translation.
-/
noncomputable def reduceNBHToSatMLS : Bitstring → Bitstring := nbhToMlsMap

namespace reduceNBHToSatMLSStep

theorem on_μ₀Support (x : Bitstring) (hx : x ∈ μ₀Support) :
    reduceNBHToSatMLSStep x = satTargetEnc := by
  simp [reduceNBHToSatMLSStep, hx]

theorem off_μ₀Support (x : Bitstring) (hx : x ∉ μ₀Support) :
    reduceNBHToSatMLSStep x = unsatTargetEnc := by
  simp [reduceNBHToSatMLSStep, hx]

end reduceNBHToSatMLSStep

/-! ### Rank helpers for singleton uniform distributions -/

namespace Distribution

theorem mem_support_of_prob_pos (μ : Distribution) (x : Bitstring) (h : 0 < μ.prob x) :
    x ∈ μ.support := by
  by_contra hx
  exact not_lt.mpr (by simp [μ.prob_zero_outside x hx]) h

theorem uniformOn_prob_pos {S : Finset Bitstring} (h : S.Nonempty) {x : Bitstring} (hx : x ∈ S) :
    0 < (uniformOn S h).prob x := by
  have hcard : 0 < (S.card : Real) := Nat.cast_pos.mpr (Finset.card_pos.mpr h)
  simp only [uniformOn, uniformProb, hx]
  exact div_pos zero_lt_one hcard

theorem uniformOn_prob_zero {S : Finset Bitstring} (h : S.Nonempty) {x : Bitstring} (hx : x ∉ S) :
    (uniformOn S h).prob x = 0 := by
  simp [uniformOn, uniformProb, hx]

end Distribution

theorem rank_pos_of_prob_pos (μ : Distribution) (x : Bitstring) (h : 0 < μ.prob x) :
    0 < rank μ x := by
  unfold rank
  split_ifs with h0
  · rw [h0] at h
    norm_num at h
  · have hx : x ∈ μ.support.filter (fun z => μ.prob x ≤ μ.prob z) := by
      simp [Finset.mem_filter, Distribution.mem_support_of_prob_pos μ x h, le_refl]
    exact Finset.card_pos.mpr ⟨x, hx⟩

theorem μ₀_rank_on_support (x : Bitstring) (hx : x ∈ μ₀Support) :
    rank μ₀ x = 1 := by
  have hle : rank μ₀ x ≤ 1 := by
    have := rank.le_support_card μ₀ x
    simp [μ₀, uniformOn, μ₀Support, hx] at this
    exact this
  have hge : 1 ≤ rank μ₀ x := by
    have hprob : 0 < μ₀.prob x := Distribution.uniformOn_prob_pos μ₀Support_nonempty hx
    have : 0 < rank μ₀ x := rank_pos_of_prob_pos μ₀ x hprob
    omega
  omega

theorem μ₀_rank_off_support (x : Bitstring) (hx : x ∉ μ₀Support) :
    rank μ₀ x = 0 :=
  rank.zero μ₀ x (Distribution.uniformOn_prob_zero μ₀Support_nonempty hx)

theorem μ₁_rank_on_target : rank μ₁ satTargetEnc = 1 := by
  have hle : rank μ₁ satTargetEnc ≤ 1 := by
    have := rank.le_support_card μ₁ satTargetEnc
    simp [μ₁, uniformOn, μ₁Support] at this
    exact this
  have hge : 1 ≤ rank μ₁ satTargetEnc := by
    have hprob : 0 < μ₁.prob satTargetEnc :=
      Distribution.uniformOn_prob_pos μ₁Support_nonempty (by simp [μ₁Support])
    have : 0 < rank μ₁ satTargetEnc := rank_pos_of_prob_pos μ₁ satTargetEnc hprob
    omega
  omega

theorem μ₁_rank_off_target (x : Bitstring) (hx : x ∉ μ₁Support) :
    rank μ₁ x = 0 :=
  rank.zero μ₁ x (Distribution.uniformOn_prob_zero μ₁Support_nonempty hx)

/-! ### Domination -/

theorem reduce_domination (x : Bitstring) :
    rank μ₁ (reduceNBHToSatMLSStep x) ≤ 1 * (lenBot x) ^ 1 * rank μ₀ x := by
  by_cases hx : x ∈ μ₀Support
  · rw [reduceNBHToSatMLSStep.on_μ₀Support x hx, μ₁_rank_on_target, μ₀_rank_on_support x hx]
    simp only [one_mul, pow_one]
    exact Nat.le_mul_of_pos_left 1 (lenBot_ne_zero x)
  · rw [reduceNBHToSatMLSStep.off_μ₀Support x hx, μ₀_rank_off_support x hx]
    have hunsat : unsatTargetEnc ∉ μ₁Support := by
      intro hmem
      simp [μ₁Support] at hmem
      exact satTargetEnc_ne_unsatTargetEnc hmem.symm
    rw [μ₁_rank_off_target unsatTargetEnc hunsat]
    simp

/-! ### Correctness (scaffold) -/

theorem reduce_correct_on_μ₀Support (x : Bitstring) (hx : x ∈ μ₀Support) :
    x ∈ NBHChecker ↔ reduceNBHToSatMLSStep x ∈ SatMLSChecker := by
  have heq : x = NBHInstance.encode trivialInstance := by
    simpa [μ₀Support] using hx
  subst heq
  constructor
  · intro _
    simpa [reduceNBHToSatMLSStep.on_μ₀Support _ hx, satTargetEnc_in_checker]
  · intro _
    exact trivialInstance_in_NBHChecker

theorem reduce_correct (x : Bitstring) :
    x ∈ NBHChecker ↔ reduceNBHToSatMLS x ∈ SatMLSChecker :=
  nbhToMlsMap_correct x

/-! ### Distributional reduction -/

theorem nbhToSatMLS_red : DistributionalReduction nbhProb satMLSProb := by
  refine ⟨reduceNBHToSatMLS, reduce_correct, ?_, ?_⟩
  · exact nbhToMlsMap_lenBound
  · exact nbhToMlsMap_domination

theorem nbhToSatMLS_red_on_μ₀ (x : Bitstring) (hx : x ∈ μ₀Support) :
    x ∈ NBHChecker ↔ reduceNBHToSatMLSStep x ∈ SatMLSChecker :=
  reduce_correct_on_μ₀Support x hx

end Reduction
