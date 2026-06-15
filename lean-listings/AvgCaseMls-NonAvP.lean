/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.ComplexityAxioms
import AvgCaseMls.Completeness
import AvgCaseMls.AverageHardness

/-!
Phase **5A:** conditional non-AvP from NP-average completeness (TR1995-711 S3.2 / Corollary 5.1).

Literature: if an NP-average complete problem were in AvP, bounded halting (NBH) would be in AvP,
collapsing NEXP to EXP. See [`DEFINITION_FORKS.md`](../DEFINITION_FORKS.md).
-/

namespace NonAvP

open Completeness Reduction AvCom NBH MLS

theorem AvP_of_distNP_of_complete_target {target : DistributionalProblem}
    (hComplete : IsNPAverageComplete target) (hAvP : AvP target) :
    forall source, InDistNP source -> AvP source := by
  intro source hdist
  exact AvP_pullback hAvP (hComplete.2 source hdist)

theorem all_distNP_in_AvP_of_complete_target {target : DistributionalProblem}
    (hComplete : IsNPAverageComplete target) (hAvP : AvP target) :
    forall p, InDistNP p -> AvP p :=
  AvP_of_distNP_of_complete_target hComplete hAvP

theorem NEXP_eq_EXP_of_AvP_complete {target : DistributionalProblem}
    (hComplete : IsNPAverageComplete target) (hAvP : AvP target) :
    NEXP_eq_EXP :=
  (distNP_subseteq_AvP_iff_NEXP_eq_EXP).mp (all_distNP_in_AvP_of_complete_target hComplete hAvP)

theorem not_AvP_of_NPAverageComplete {target : DistributionalProblem}
    (hComplete : IsNPAverageComplete target) (h : NEXP_neq_EXP) :
    not  AvP target :=
  fun hAvP => (NEXP_eq_EXP_of_AvP_complete hComplete hAvP) h

theorem nbhProb_not_AvP (h : NEXP_neq_EXP) : not  AvP nbhProb :=
  not_AvP_of_NPAverageComplete nbhProb_NPAverageComplete h

theorem satMLSProb_not_AvP (h : NEXP_neq_EXP) : not  AvP satMLSProb :=
  not_AvP_of_NPAverageComplete satMLSProb_NPAverageComplete h

theorem nbhProb_not_AvP_via_complete (h : NEXP_neq_EXP) : not  AvP nbhProb :=
  not_AvP_of_NPAverageComplete nbhProb_NPAverageComplete h

/-- Simple POL-rankable distribution from Phase **4B** (uniform on [`satTargetEnc`]). -/
noncomputable def simpleSatmu : Distribution := mu_1

theorem simpleSatmu_polRankable : IsPolRankable simpleSatmu := mu_1_polRankable

theorem simpleSatmu_prob_satTarget :
    simpleSatmu.prob satTargetEnc = 1 := by
  simp [simpleSatmu, mu_1, uniformOn, uniformProb, mu_1Support]

theorem exists_simple_rankable_checker_not_AvP (h : NEXP_neq_EXP) :
    exists mu, IsPolRankable mu /\ not  AvP <SatMLSChecker, mu> :=
  <simpleSatmu, simpleSatmu_polRankable, fun hAvP =>
    satMLSProb_not_AvP h (by simpa [satMLSProb] using hAvP)>

/-! ### Phase 5B - MLS average-case hardness corollaries -/

/--
Corollary 5.1 consequence (checker + Phase **4B** distribution): [`satMLSProb`] is not in AvP
assuming NEXP $\neq$ EXP.
-/
theorem SatMLS_average_hard (h : NEXP_neq_EXP) : not  AvP satMLSProb :=
  satMLSProb_not_AvP h

/--
Existential form: a simple POL-rankable distribution on MLS checker encodings is not AvP-tractable.
-/
theorem exists_simple_rankable_not_AvP (h : NEXP_neq_EXP) :
    exists mu, IsPolRankable mu /\ not  AvP <SatMLSChecker, mu> :=
  exists_simple_rankable_checker_not_AvP h

/--
Semantic [`SatMLS`] on the same simple distribution - [`AvP`] depends only on [`simpleSatmu`]
(see [`AvP.same_mu`]), so checker hardness transfers directly.
-/
theorem SatMLS_semantic_not_AvP (h : NEXP_neq_EXP) : not  AvP <SatMLS, simpleSatmu> := by
  intro hAvP
  have hchecker : AvP satMLSProb := by
    simpa [satMLSProb, simpleSatmu] using (AvP.same_mu (L := SatMLS) (L' := SatMLSChecker)).mp hAvP
  exact SatMLS_average_hard h hchecker

/-! ### Axiom audit (peer-review transparency) -/

#print axioms SatMLS_average_hard
#print axioms SatMLS_semantic_not_AvP

end NonAvP
