/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.Serialization
import AvgCaseMls.Reduction

/-!
Palomar-facing wrappers for report-related adapted claims that are proved
without the project's open completeness/reduction axioms.
-/

namespace AvgCasePalomar

open AvCom MLS EMLS

def Step2Rejection : Prop :=
  ∀ c : Conjunct, hasStep2Contradiction c = true → decideConjunct c = false

theorem step2_rejection : Step2Rejection :=
  decideConjunct_unsat_step2

def SoundFragmentCompleteness : Prop :=
  ∀ f : Formula, InDecideSoundFormula f → decideMLSSat f = true

theorem sound_fragment_completeness : SoundFragmentCompleteness :=
  decideMLSSat_complete_sound_fragment

def FormulaSerializationRoundtrip : Prop :=
  ∀ f : Formula, decodeFormula? (serializeFormula f) = some (f, [])

theorem formula_serialization_roundtrip : FormulaSerializationRoundtrip :=
  decodeFormula?_serializeFormula

def FormulaEncodingPolynomiallyBounded : Prop :=
  IsPolynomial encodingBound ∧
    ∀ f : Formula, formulaSize f ≤ encodingBound (formulaAstMass f)

theorem formula_encoding_polynomially_bounded : FormulaEncodingPolynomiallyBounded :=
  ⟨encodingBound_poly, formulaSize_le_encodingBound⟩

def DistributionalReductionTransitive : Prop :=
  ∀ {p₁ p₂ p₃ : DistributionalProblem},
    DistributionalReduction p₁ p₂ →
    DistributionalReduction p₂ p₃ →
    DistributionalReduction p₁ p₃

theorem distributional_reduction_transitive : DistributionalReductionTransitive :=
  fun h₁₂ h₂₃ => h₁₂.trans h₂₃

def AverageCompletenessTransfersAlongReduction : Prop :=
  ∀ (source target : DistributionalProblem),
    InDistNP target →
    IsNPAverageComplete source →
    DistributionalReduction source target →
    IsNPAverageComplete target

theorem average_completeness_transfers_along_reduction :
    AverageCompletenessTransfersAlongReduction :=
  fun mid target hTarget hMid hRed =>
    IsNPAverageComplete.of_reductor hTarget hMid hRed

end AvgCasePalomar
