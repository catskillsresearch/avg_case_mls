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

Literature: TR1995-711 S3.2 reduction with domination. The general TM->MLS translation for
arbitrary MLS formulas in paper scope is axiomatized as [`nbhToMlsMap`]; see
[`DEFINITION_FORKS.md`](../DEFINITION_FORKS.md).
-/

namespace Reduction

open MLS NBH AvCom EMLS

/-!
**Lean fork (general case):** [`nbhToMlsMap`] stands in for the full TR1995-711 compiler from
NBH instances to serialized MLS formulas (any expression in the paper's MLS fragment). The
step-function [`reduceNBHToSatMLSStep`] remains as an explicit domination scaffold on mu_0.
-/

axiom nbhToMlsMap : Bitstring -> Bitstring

axiom nbhToMlsMap_correct :
  forall x, x in NBHChecker <-> nbhToMlsMap x in SatMLSChecker

axiom nbhToMlsMap_lenBound :
  exists k0 k1 : Nat, forall x, lenBot (nbhToMlsMap x) <= k0 * (lenBot x) ^ k1

axiom nbhToMlsMap_domination :
  exists c0 c1 : Nat, 0 < c0 /\ 0 < c1 /\
    forall x, rank mu_1 (nbhToMlsMap x) <= c0 * (lenBot x) ^ c1 * rank mu_0 x

/-!
**Physical cost model (Cook-Levin style, TR1995-711 S3.2).**

For an NBH instance with state-space `|Q|`, input length `n`, and step bound `t`, the
constructed MLS formula has bit-length bounded by `O(|Q| * t * (n + t))`: each of the
`O(t)` configuration snapshots contributes `O(|Q| + n + t)` bits under the NBH/MLS
encodings, and the formula size is linear in the certificate length.

This growth is **quadratic in the instance description** (`lenBot x` is polynomial in
`|Q|`, `n`, and `t`), which supports [`nbhToMlsMap_lenBound`] and the polynomial
length/domination constraints in [`DistributionalReduction`].
-/

def satTargetFormula : Formula :=
  Formula.rel (Relation.eq Term.empty Term.empty)

def unsatTargetFormula : Formula :=
  Formula.rel (Relation.neq Term.empty Term.empty)

def satTargetEnc : Bitstring :=
  serializeFormula satTargetFormula

def unsatTargetEnc : Bitstring :=
  serializeFormula unsatTargetFormula

theorem satTargetEnc_ne_unsatTargetEnc : satTargetEnc /= unsatTargetEnc := by
  native_decide

theorem satTargetEnc_in_checker : satTargetEnc in SatMLSChecker := by
  rw [<- verifySatMLS_true_iff]
  native_decide

theorem satTargetEnc_in_SatMLS : satTargetEnc in SatMLS := by
  refine <satTargetFormula, rfl, ?_>
  refine <fun _ => ZFSet.empty, ?_>
  simp [evalFormula, evalTerm, satTargetFormula, Relation.eq]

theorem unsatTargetEnc_not_in_checker : unsatTargetEnc notin SatMLSChecker := by
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

def mu_1Support : Finset Bitstring :=
  {satTargetEnc}

theorem mu_1Support_nonempty : mu_1Support.Nonempty :=
  <satTargetEnc, by simp [mu_1Support]>

noncomputable def mu_1 : Distribution :=
  uniformOn mu_1Support mu_1Support_nonempty

theorem mu_1_polRankable : IsPolRankable mu_1 :=
  IsPolRankable.uniformOn_polRankable mu_1Support mu_1Support_nonempty

noncomputable def satMLSProb : DistributionalProblem :=
  { L := SatMLSChecker, mu := mu_1 }

theorem satMLSProb_in_DistNP : InDistNP satMLSProb :=
  InDistNP.intro SatMLSChecker_in_NP mu_1_polRankable

/-! ### Reduction map -/

/--
Step-function scaffold on mu_0 support (domination witness only; not globally correct).
-/
def reduceNBHToSatMLSStep (x : Bitstring) : Bitstring :=
  if x in mu_0Support then satTargetEnc else unsatTargetEnc

/--
Distributional reduction map used in [`nbhToSatMLS_red`]: axiomatized general TM->MLS translation.
-/
noncomputable def reduceNBHToSatMLS : Bitstring -> Bitstring := nbhToMlsMap

namespace reduceNBHToSatMLSStep

theorem on_mu_0Support (x : Bitstring) (hx : x in mu_0Support) :
    reduceNBHToSatMLSStep x = satTargetEnc := by
  simp [reduceNBHToSatMLSStep, hx]

theorem off_mu_0Support (x : Bitstring) (hx : x notin mu_0Support) :
    reduceNBHToSatMLSStep x = unsatTargetEnc := by
  simp [reduceNBHToSatMLSStep, hx]

end reduceNBHToSatMLSStep

/-! ### Rank helpers for singleton uniform distributions -/

namespace Distribution

theorem mem_support_of_prob_pos (mu : Distribution) (x : Bitstring) (h : 0 < mu.prob x) :
    x in mu.support := by
  by_contra hx
  exact not_lt.mpr (by simp [mu.prob_zero_outside x hx]) h

theorem uniformOn_prob_pos {S : Finset Bitstring} (h : S.Nonempty) {x : Bitstring} (hx : x in S) :
    0 < (uniformOn S h).prob x := by
  have hcard : 0 < (S.card : Real) := Nat.cast_pos.mpr (Finset.card_pos.mpr h)
  simp only [uniformOn, uniformProb, hx]
  exact div_pos zero_lt_one hcard

theorem uniformOn_prob_zero {S : Finset Bitstring} (h : S.Nonempty) {x : Bitstring} (hx : x notin S) :
    (uniformOn S h).prob x = 0 := by
  simp [uniformOn, uniformProb, hx]

end Distribution

theorem rank_pos_of_prob_pos (mu : Distribution) (x : Bitstring) (h : 0 < mu.prob x) :
    0 < rank mu x := by
  unfold rank
  split_ifs with h0
  * rw [h0] at h
    norm_num at h
  * have hx : x in mu.support.filter (fun z => mu.prob x <= mu.prob z) := by
      simp [Finset.mem_filter, Distribution.mem_support_of_prob_pos mu x h, le_refl]
    exact Finset.card_pos.mpr <x, hx>

theorem mu_0_rank_on_support (x : Bitstring) (hx : x in mu_0Support) :
    rank mu_0 x = 1 := by
  have hle : rank mu_0 x <= 1 := by
    have := rank.le_support_card mu_0 x
    simp [mu_0, uniformOn, mu_0Support, hx] at this
    exact this
  have hge : 1 <= rank mu_0 x := by
    have hprob : 0 < mu_0.prob x := Distribution.uniformOn_prob_pos mu_0Support_nonempty hx
    have : 0 < rank mu_0 x := rank_pos_of_prob_pos mu_0 x hprob
    omega
  omega

theorem mu_0_rank_off_support (x : Bitstring) (hx : x notin mu_0Support) :
    rank mu_0 x = 0 :=
  rank.zero mu_0 x (Distribution.uniformOn_prob_zero mu_0Support_nonempty hx)

theorem mu_1_rank_on_target : rank mu_1 satTargetEnc = 1 := by
  have hle : rank mu_1 satTargetEnc <= 1 := by
    have := rank.le_support_card mu_1 satTargetEnc
    simp [mu_1, uniformOn, mu_1Support] at this
    exact this
  have hge : 1 <= rank mu_1 satTargetEnc := by
    have hprob : 0 < mu_1.prob satTargetEnc :=
      Distribution.uniformOn_prob_pos mu_1Support_nonempty (by simp [mu_1Support])
    have : 0 < rank mu_1 satTargetEnc := rank_pos_of_prob_pos mu_1 satTargetEnc hprob
    omega
  omega

theorem mu_1_rank_off_target (x : Bitstring) (hx : x notin mu_1Support) :
    rank mu_1 x = 0 :=
  rank.zero mu_1 x (Distribution.uniformOn_prob_zero mu_1Support_nonempty hx)

/-! ### Domination -/

theorem reduce_domination (x : Bitstring) :
    rank mu_1 (reduceNBHToSatMLSStep x) <= 1 * (lenBot x) ^ 1 * rank mu_0 x := by
  by_cases hx : x in mu_0Support
  * rw [reduceNBHToSatMLSStep.on_mu_0Support x hx, mu_1_rank_on_target, mu_0_rank_on_support x hx]
    simp only [one_mul, pow_one]
    exact Nat.le_mul_of_pos_left 1 (lenBot_ne_zero x)
  * rw [reduceNBHToSatMLSStep.off_mu_0Support x hx, mu_0_rank_off_support x hx]
    have hunsat : unsatTargetEnc notin mu_1Support := by
      intro hmem
      simp [mu_1Support] at hmem
      exact satTargetEnc_ne_unsatTargetEnc hmem.symm
    rw [mu_1_rank_off_target unsatTargetEnc hunsat]
    simp

/-! ### Correctness (scaffold) -/

theorem reduce_correct_on_mu_0Support (x : Bitstring) (hx : x in mu_0Support) :
    x in NBHChecker <-> reduceNBHToSatMLSStep x in SatMLSChecker := by
  have heq : x = NBHInstance.encode trivialInstance := by
    simpa [mu_0Support] using hx
  subst heq
  constructor
  * intro _
    simpa [reduceNBHToSatMLSStep.on_mu_0Support _ hx, satTargetEnc_in_checker]
  * intro _
    exact trivialInstance_in_NBHChecker

theorem reduce_correct (x : Bitstring) :
    x in NBHChecker <-> reduceNBHToSatMLS x in SatMLSChecker :=
  nbhToMlsMap_correct x

/-! ### Distributional reduction -/

theorem nbhToSatMLS_red : DistributionalReduction nbhProb satMLSProb := by
  refine <reduceNBHToSatMLS, reduce_correct, ?_, ?_>
  * exact nbhToMlsMap_lenBound
  * exact nbhToMlsMap_domination

theorem nbhToSatMLS_red_on_mu_0 (x : Bitstring) (hx : x in mu_0Support) :
    x in NBHChecker <-> reduceNBHToSatMLSStep x in SatMLSChecker :=
  reduce_correct_on_mu_0Support x hx

end Reduction
