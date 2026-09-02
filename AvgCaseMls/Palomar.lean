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

/-!
Palomar-facing proofs of the six directly stated paper-numbered/core claims,
without the project's open completeness/reduction assumptions.
-/

namespace AvgCasePalomar

open AvCom MLS EMLS

theorem paper_theorem_4_1 :
  ∀ {L : Set Bitstring} {ρ : Distribution},
    IsNPAverageComplete ⟨L, ρ⟩ → TR1995.IsNPAverageCompleteLanguage L :=
  fun h => TR1995.theorem_4_1 h

theorem paper_theorem_4_4 :
  ∀ {L₁ L₂ : Set Bitstring},
    HonestReduction.FaithfulReduction L₁ L₂ →
    TR1995.IsNPAverageCompleteLanguage L₁ →
    InNP L₂ →
    TR1995.IsNPAverageCompleteLanguage L₂ :=
  HonestReduction.npAverageCompleteLanguage_of_faithfulReduction

theorem paper_example_4_1 :
  ∀ {ε : ℝ}, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      Summable (Example41.levinShellSeries ε) ∧
      (∑' n : Nat, Example41.levinShellSeries ε n / C) ≤ 1 :=
  fun hε => Example41.normalized_levin_bound hε

theorem paper_theorem_5_1_reduction_core :
  (∀ φ : SAT.CNF,
      SAT.Satisfiable φ ↔ MLSInReduction.MLSSatisfiable (MLSInReduction.toMLS φ)) ∧
  Function.Injective MLSInReduction.toMLS ∧
  ∀ φ : SAT.CNF,
    formulaNodes (MLSInReduction.toMLS φ) + 1 = 5 * SAT.size φ :=
  ⟨MLSInReduction.satisfiable_iff, MLSInReduction.toMLS_injective,
    MLSInReduction.formulaNodes_toMLS⟩

theorem paper_theorem_5_2_reduction_core :
  (∀ φ : SAT.CNF,
      SAT.Satisfiable φ ↔
        EMLSReduction.EMLSSatisfiable (EMLSReduction.toEMLS φ)) ∧
  Function.Injective EMLSReduction.toEMLS ∧
  ∀ φ : SAT.CNF,
    (EMLSReduction.toEMLS φ).length ≤ 3 * SAT.size φ :=
  ⟨EMLSReduction.toEMLS_satisfiable_iff, EMLSReduction.toEMLS_injective,
    EMLSReduction.toEMLS_length_le⟩

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
