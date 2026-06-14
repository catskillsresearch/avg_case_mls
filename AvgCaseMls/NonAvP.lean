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
collapsing NEXP to EXP. Reduction pull-back and NBH average-case lower bounds are deferred until
`DistTime` is linked to deciders — see [`DEFINITION_FORKS.md`](../DEFINITION_FORKS.md).
-/

namespace NonAvP

open Completeness Reduction AvCom NBH MLS

/-!
Pull AvP back along distributional reductions from a complete target.

Deferred: poly-time decider for `target.L` composed with reduction map; needs `DistTime` decider
linkage and poly bound on `len (f x)`.
-/
theorem AvP_of_distNP_of_complete_target {target : DistributionalProblem}
    (hComplete : IsNPAverageComplete target) (hAvP : AvP target) :
    ∀ source, InDistNP source → AvP source := by
  intro source hdist
  sorry

/--
NBH is not in AvP unless NEXP = EXP (Levin / TR1995-711 core).

Deferred: unconditional average-case lower bound for bounded halting.
-/
theorem nbhProb_not_AvP (h : NEXP_neq_EXP) : ¬ AvP nbhProb := by
  intro hAvP
  sorry

/--
Completeness + AvP on a distNP-complete target implies NEXP = EXP.

Deferred: compose [`AvP_of_distNP_of_complete_target`] with [`nbhProb_not_AvP`].
-/
theorem NEXP_eq_EXP_of_AvP_complete {target : DistributionalProblem}
    (hComplete : IsNPAverageComplete target) (hAvP : AvP target) :
    NEXP_eq_EXP := by
  sorry

theorem not_AvP_of_NPAverageComplete {target : DistributionalProblem}
    (hComplete : IsNPAverageComplete target) (h : NEXP_neq_EXP) :
    ¬ AvP target :=
  fun hAvP => (NEXP_eq_EXP_of_AvP_complete hComplete hAvP) h

theorem satMLSProb_not_AvP (h : NEXP_neq_EXP) : ¬ AvP satMLSProb :=
  not_AvP_of_NPAverageComplete satMLSProb_NPAverageComplete h

theorem nbhProb_not_AvP_via_complete (h : NEXP_neq_EXP) : ¬ AvP nbhProb :=
  not_AvP_of_NPAverageComplete nbhProb_NPAverageComplete h

/-- Simple POL-rankable distribution from Phase **4B** (uniform on [`satTargetEnc`]). -/
noncomputable def simpleSatμ : Distribution := μ₁

theorem simpleSatμ_polRankable : IsPolRankable simpleSatμ := μ₁_polRankable

theorem simpleSatμ_prob_satTarget :
    simpleSatμ.prob satTargetEnc = 1 := by
  simp [simpleSatμ, μ₁, uniformOn, uniformProb, μ₁Support]

theorem exists_simple_rankable_checker_not_AvP (h : NEXP_neq_EXP) :
    ∃ μ, IsPolRankable μ ∧ ¬ AvP ⟨SatMLSChecker, μ⟩ :=
  ⟨simpleSatμ, simpleSatμ_polRankable, fun hAvP =>
    satMLSProb_not_AvP h (by simpa [satMLSProb] using hAvP)⟩

/-! ### Phase 5B — MLS average-case hardness corollaries -/

/--
Corollary 5.1 consequence (checker + Phase **4B** distribution): [`satMLSProb`] is not in AvP
assuming NEXP $`\neq`$ EXP.
-/
theorem SatMLS_average_hard (h : NEXP_neq_EXP) : ¬ AvP satMLSProb :=
  satMLSProb_not_AvP h

/--
Existential form: a simple POL-rankable distribution on MLS checker encodings is not AvP-tractable.
-/
theorem exists_simple_rankable_not_AvP (h : NEXP_neq_EXP) :
    ∃ μ, IsPolRankable μ ∧ ¬ AvP ⟨SatMLSChecker, μ⟩ :=
  exists_simple_rankable_checker_not_AvP h

/--
Semantic [`SatMLS`] on the same simple distribution — deferred until checker/semantic AvP
equivalence on [`simpleSatμ`] support is formalized.
-/
theorem SatMLS_semantic_not_AvP (h : NEXP_neq_EXP) : ¬ AvP ⟨SatMLS, simpleSatμ⟩ := by
  intro hAvP
  sorry

end NonAvP
