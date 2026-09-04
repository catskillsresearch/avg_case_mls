/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.TR1995
import AvgCaseMls.Example41
import AvgCaseMls.HonestReduction
import AvgCaseMls.MLSInReduction
import AvgCaseMls.EMLSReduction
import AvgCaseMls.FPILP
import AvgCaseMls.EncodingCollapse
import AvgCaseMls.HardnessCollapse
import AvgCaseMls.ComplexityAxioms

/-!
Palomar-facing proofs of the revisit-paper canon: Example 4.1, the three SAT
reduction cores, and five encoding-collapse diagnostics.  Vacuous TR1995
Theorems 4.1 and 4.4 in the untimed layer are omitted.
-/

namespace AvgCasePalomar

open AvCom MLS EMLS

theorem paper_collapse_inNP_trivial (L : Set Bitstring) : InNP L :=
  AvgCaseMls.EncodingCollapse.inNP_trivial L

theorem paper_collapse_completeness_characterization (L : Set Bitstring) :
    TR1995.IsNPAverageCompleteLanguage L ↔ (L ≠ ∅ ∧ L ≠ Set.univ) :=
  AvgCaseMls.EncodingCollapse.npAverageCompleteLanguage_iff_nontrivial L

theorem paper_collapse_theorem44_vacuous {L₁ L₂ : Set Bitstring}
    (map : Bitstring → Bitstring)
    (reduces : ∀ x, x ∈ L₁ ↔ map x ∈ L₂)
    (h₁ : TR1995.IsNPAverageCompleteLanguage L₁) (h₂ : InNP L₂) :
    TR1995.IsNPAverageCompleteLanguage L₂ :=
  AvgCaseMls.EncodingCollapse.npAverageCompleteLanguage_of_reduces map reduces h₁

theorem paper_collapse_avP_characterization (p : DistributionalProblem) :
    AvP p ↔ IsPolRankable p.μ :=
  AvgCaseMls.HardnessCollapse.avP_iff_polRankable p

theorem paper_collapse_no_theory_separates (theory : AverageCaseCollapseTheory) :
    ¬ theory.NEXP_neq_EXP :=
  AvgCaseMls.HardnessCollapse.no_theory_separates theory

theorem paper_example_4_1 :
  ∀ {ε : ℝ}, 0 < ε →
    let C := max (∑' n : Nat, Example41.levinShellSeries ε n) 1
    0 < C ∧ Summable (Example41.levinShellSeries ε) ∧
      (∑' n : Nat, Example41.levinShellSeries ε n / C) ≤ 1 := by
  intro ε hε
  let S := ∑' n : Nat, Example41.levinShellSeries ε n
  refine ⟨lt_of_lt_of_le zero_lt_one (le_max_right S 1),
    Example41.summable_levinShellSeries hε, ?_⟩
  rw [tsum_div_const]
  exact (div_le_one (lt_of_lt_of_le zero_lt_one (le_max_right S 1))).2
    (le_max_left S 1)

theorem paper_theorem_5_1_reduction_core :
  (∀ φ : SAT.CNF,
      SAT.Satisfiable φ ↔ MLSInReduction.MLSSatisfiable (MLSInReduction.toMLS φ)) ∧
  Function.Injective MLSInReduction.toMLS ∧
  (∀ φ : SAT.CNF, MLSInReduction.fromMLS (MLSInReduction.toMLS φ) = some φ) ∧
  ∀ φ : SAT.CNF,
    formulaNodes (MLSInReduction.toMLS φ) + 1 = 5 * SAT.size φ :=
  ⟨MLSInReduction.satisfiable_iff, MLSInReduction.toMLS_injective,
    MLSInReduction.fromMLS_toMLS, MLSInReduction.formulaNodes_toMLS⟩

theorem paper_theorem_5_2_reduction_core :
  (∀ φ : SAT.CNF,
      SAT.Satisfiable φ ↔
        EMLSReduction.EMLSSatisfiable (EMLSReduction.toEMLS φ)) ∧
  Function.Injective EMLSReduction.toEMLS ∧
  (∀ φ : SAT.CNF, EMLSReduction.fromEMLS (EMLSReduction.toEMLS φ) = some φ) ∧
  ∀ φ : SAT.CNF,
    (EMLSReduction.toEMLS φ).length =
      (EMLSReduction.sourceBits φ).length + 2 +
        3 * EMLSReduction.literalCount φ + φ.length :=
  ⟨EMLSReduction.toEMLS_satisfiable_iff, EMLSReduction.toEMLS_injective,
    EMLSReduction.fromEMLS_toEMLS, EMLSReduction.toEMLS_length⟩

theorem paper_theorem_5_3_reduction_core :
  (∀ {n : Nat} (φ : TR1995.FPILPSource.CNF n),
      φ.Satisfiable ↔
        (TR1995.FPILPSource.satToFPILP φ).Feasible) ∧
  (∀ {n : Nat},
      Function.Injective (@TR1995.FPILPSource.satToFPILP n)) ∧
  ∀ {n : Nat} (φ : TR1995.FPILPSource.CNF n),
    (TR1995.FPILPSource.satToFPILP φ).constraints.length =
      2 * n + φ.length :=
  ⟨fun φ => (TR1995.FPILPSource.satToFPILP_feasible_iff φ).symm,
    @TR1995.FPILPSource.satToFPILP_injective,
    TR1995.FPILPSource.satToFPILP_constraint_count⟩

end AvgCasePalomar
