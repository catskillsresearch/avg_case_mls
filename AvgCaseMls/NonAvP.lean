/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.ComplexityAxioms
import AvgCaseMls.Completeness
import AvgCaseMls.AverageHardness

/-!
Phase **5A:** conditional non-AvP from NP-average completeness (TR1995-711 §3.2 / Corollary 5.1).

Literature: if an NP-average complete problem were in AvP, bounded halting (NBH) would be in AvP,
collapsing NEXP to EXP. See [`DEFINITION_FORKS.md`](../DEFINITION_FORKS.md).
-/

namespace NonAvP

open Completeness Reduction AvCom NBH MLS

theorem AvP_of_distNP_of_complete_target (theory : AverageCaseCollapseTheory)
    {target : DistributionalProblem}
    (hComplete : IsNPDistributionallyComplete target) (hAvP : AvP target) :
    ∀ source, InDistNP source → AvP source := by
  intro source hdist
  exact theory.AvP_pullback hAvP (hComplete.2 source hdist)

theorem all_distNP_in_AvP_of_complete_target (theory : AverageCaseCollapseTheory)
    {target : DistributionalProblem}
    (hComplete : IsNPDistributionallyComplete target) (hAvP : AvP target) :
    ∀ p, InDistNP p → AvP p :=
  AvP_of_distNP_of_complete_target theory hComplete hAvP

theorem NEXP_eq_EXP_of_AvP_complete (theory : AverageCaseCollapseTheory)
    {target : DistributionalProblem}
    (hComplete : IsNPDistributionallyComplete target) (hAvP : AvP target) :
    theory.NEXP_eq_EXP :=
  theory.distNP_subseteq_AvP_iff_NEXP_eq_EXP.mp
    (all_distNP_in_AvP_of_complete_target theory hComplete hAvP)

theorem not_AvP_of_NPDistributionallyComplete (theory : AverageCaseCollapseTheory)
    {target : DistributionalProblem}
    (hComplete : IsNPDistributionallyComplete target) (h : theory.NEXP_neq_EXP) :
    ¬ AvP target :=
  fun hAvP => h (NEXP_eq_EXP_of_AvP_complete theory hComplete hAvP)

theorem nbhProb_not_AvP (theory : AverageCaseCollapseTheory)
    (levin : LevinNBHData) (h : theory.NEXP_neq_EXP) : ¬ AvP nbhProb :=
  not_AvP_of_NPDistributionallyComplete theory (nbhProb_NPDistributionallyComplete levin) h

theorem satMLSProb_not_AvP (theory : AverageCaseCollapseTheory)
    (levin : LevinNBHData) (compiler : NBHToMLSData)
    (h : theory.NEXP_neq_EXP) : ¬ AvP satMLSProb :=
  not_AvP_of_NPDistributionallyComplete theory
    (satMLSProb_NPDistributionallyComplete levin compiler) h

theorem nbhProb_not_AvP_via_complete (theory : AverageCaseCollapseTheory)
    (levin : LevinNBHData) (h : theory.NEXP_neq_EXP) : ¬ AvP nbhProb :=
  not_AvP_of_NPDistributionallyComplete theory (nbhProb_NPDistributionallyComplete levin) h

/-- Simple POL-rankable distribution from Phase **4B** (uniform on [`satTargetEnc`]). -/
noncomputable def simpleSatμ : Distribution := μ₁

theorem simpleSatμ_polRankable : IsPolRankable simpleSatμ := μ₁_polRankable

theorem simpleSatμ_prob_satTarget :
    simpleSatμ.prob satTargetEnc = 1 := by
  simp [simpleSatμ, μ₁, uniformOn, uniformProb, μ₁Support]

theorem exists_simple_rankable_checker_not_AvP
    (theory : AverageCaseCollapseTheory) (levin : LevinNBHData)
    (compiler : NBHToMLSData) (h : theory.NEXP_neq_EXP) :
    ∃ μ, IsPolRankable μ ∧ ¬ AvP ⟨SatMLSChecker, μ⟩ :=
  ⟨simpleSatμ, simpleSatμ_polRankable, fun hAvP =>
    satMLSProb_not_AvP theory levin compiler h (by
      change AvP { L := SatMLSChecker, μ := μ₁ }
      change AvP { L := SatMLSChecker, μ := simpleSatμ } at hAvP
      exact hAvP)⟩

/-! ### Phase 5B — MLS average-case hardness corollaries -/

/--
Corollary 5.1 consequence (checker + Phase **4B** distribution): [`satMLSProb`] is not in AvP
assuming NEXP $`\neq`$ EXP.
-/
theorem SatMLS_average_hard
    (theory : AverageCaseCollapseTheory) (levin : LevinNBHData)
    (compiler : NBHToMLSData) (h : theory.NEXP_neq_EXP) :
    ¬ AvP satMLSProb :=
  satMLSProb_not_AvP theory levin compiler h

/--
Existential form: a simple POL-rankable distribution on MLS checker encodings is not AvP-tractable.
-/
theorem exists_simple_rankable_not_AvP
    (theory : AverageCaseCollapseTheory) (levin : LevinNBHData)
    (compiler : NBHToMLSData) (h : theory.NEXP_neq_EXP) :
    ∃ μ, IsPolRankable μ ∧ ¬ AvP ⟨SatMLSChecker, μ⟩ :=
  exists_simple_rankable_checker_not_AvP theory levin compiler h

/--
Semantic [`SatMLS`] on the same simple distribution — [`AvP`] depends only on [`simpleSatμ`]
(see [`AvP.same_μ`]), so checker hardness transfers directly.
-/
theorem SatMLS_semantic_not_AvP
    (theory : AverageCaseCollapseTheory) (levin : LevinNBHData)
    (compiler : NBHToMLSData) (h : theory.NEXP_neq_EXP) :
    ¬ AvP ⟨SatMLS, simpleSatμ⟩ := by
  intro hAvP
  have hchecker : AvP satMLSProb := by
    simpa [satMLSProb, simpleSatμ] using (AvP.same_μ (L := SatMLS) (L' := SatMLSChecker)).mp hAvP
  exact SatMLS_average_hard theory levin compiler h hchecker

/-! ### Axiom audit (peer-review transparency) -/

#print axioms SatMLS_average_hard
#print axioms SatMLS_semantic_not_AvP

end NonAvP
