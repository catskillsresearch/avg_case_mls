/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.MLS
import AvgCaseMls.EMLS
import AvgCaseMls.DecideMLS
import AvgCaseMls.Serialization
import AvgCaseMls.NPMembership
import AvgCaseMls.NBH
import AvgCaseMls.Reduction
import AvgCaseMls.Completeness
import AvgCaseMls.NonAvP
import AvgCaseMls.AvCom

/-!
Smoke tests for the MLS embedding and computable fragments of the AvCom definitions.

Run printed values:

```bash
./run_lean_tests.sh
# or
lake build AvgCaseMls.Tests 2>&1 | grep "^info: AvgCaseMls/Tests"
```
-/

namespace AvgCaseMls.Tests

open MLS EMLS AvCom

/-! ### MLS embedding (§6) -/

example : decideMLSSat (Formula.rel (Relation.eq Term.empty Term.empty)) = true := rfl

example : decideMLSSat (Formula.rel (Relation.neq Term.empty Term.empty)) = false := rfl

example : decideMLSSat (Formula.rel (Relation.mem Term.empty Term.empty)) = false := rfl

/-! ### FOS80 EMLS conjuncts (§7) -/

example : decideConjunct [.neq 0 0] = false := rfl

example : decideConjunct [.mem 0 1, .notMem 0 1] = false := rfl

example : decideConjunct [.eqEmpty 0] = true := rfl

example : decideConjunct [.eqEmpty 0, .eqEmpty 1, .neq 0 1] = false := rfl

example :
    decideMLSSat (Formula.and (Formula.rel (Relation.mem (Term.var 0) (Term.var 1)))
      (Formula.rel (Relation.not_mem (Term.var 0) (Term.var 1)))) = false := rfl

/-! ### AvCom Phase 1A (§5) -/

example : len ([] : Bitstring) = 0 := rfl

example : len [true, false] = 2 := rfl

example : lenBot [] = 1 := lenBot_empty

example : (pointMass [true] 1 (by norm_num) (by norm_num)).prob [true] = 1 := rfl

example : (pointMass [true] 1 (by norm_num) (by norm_num)).prob [false] = 0 := rfl

example : (uniformOn {[], [true]} (by decide)).mass = 1 :=
  uniformOn_mass _ (by decide)

example : IsPolynomial (fun n => n + 1) := IsPolynomial.add_one id IsPolynomial.id

example : IsPolynomial (fun n => 2 * n ^ 2 + 3) := by
  refine ⟨5, 2, fun n => ?_⟩
  calc
    2 * n ^ 2 + 3 ≤ 5 * n ^ 2 + 5 := by gcongr; omega

/-! ### AvCom Phase 1B (§5) -/

example : rank (pointMass [true] 0 (by norm_num) (by norm_num)) [true] = 0 :=
  rank.zero _ _ rfl

example : rank (uniformOn {[], [true]} (by decide)) [] ≤ 2 := by
  have h := rank.le_support_card (uniformOn {[], [true]} (by decide)) []
  simpa using h

/-! ### AvCom Phase 1C (§5) -/

noncomputable def testProb : DistributionalProblem where
  L := ∅
  μ := uniformOn {[], [true]} (by decide)

example : IsAvTime id (fun _ => 0) testProb.μ :=
  IsAvTime.zero id testProb.μ

example : DistTime id testProb :=
  DistTime.zero id testProb

example : IsTRankable (fun _ => 2) testProb.μ :=
  IsTRankable.of_support _ _ fun x _ =>
    rank.le_support_card testProb.μ x

example : AvDTime id (fun _ => 2) testProb :=
  AvDTime.of_distTime
    (IsTRankable.of_support _ _ fun x _ => rank.le_support_card testProb.μ x)
    (DistTime.zero id testProb)

/-! ### AvCom Phase 1D (§5) -/

example : InDistNP testProb :=
  InDistNP.intro InNP.empty (IsPolRankable.uniformOn_polRankable {[], [true]} (by decide))

example : AvP testProb :=
  AvP.zero (IsPolRankable.uniformOn_polRankable {[], [true]} (by decide)) IsPolynomial.id

example : DistributionalReduction testProb testProb :=
  DistributionalReduction.refl testProb

/-! ### EMLS Phase 2B (§6) -/

example : conjunctToFormula ([] : Conjunct) = none := by
  simp [conjunctToFormula_none_iff]

example : conjunctToFormula [.mem 0 1] = some (literalToFormula (.mem 0 1)) :=
  conjunctToFormula_singleton _

example :
    conjunctToFormula [.mem 0 1, .eqEmpty 0] =
      some (Formula.and (literalToFormula (.mem 0 1)) (literalToFormula (.eqEmpty 0))) := by
  simp [conjunctToFormula, conjunctToFormula_singleton]

example :
    relationToLiteral? (Relation.eq (Term.var 0) (Term.union (Term.var 1) (Term.var 2))) =
      some (Literal.eqOp 0 1 2 BinOp.union) := rfl

example : decideEMLSSat [.neq 0 0] = false := rfl

/-! ### Phase 2C — decision procedure unit tests (§7) -/

/-- Satisfiable flat formula: `x = y ∪ z` (eqOp literal; outside sound fragment). -/
def formulaSat : Formula :=
  Formula.rel (Relation.eq (Term.var 1) (Term.union (Term.var 2) (Term.var 3)))

example : decideMLSSat formulaSat = true := rfl

/-- Step 2 contradiction: `x ≠ x`. -/
def formulaUnsatStep2 : Formula :=
  Formula.rel (Relation.neq (Term.var 1) (Term.var 1))

example : decideMLSSat formulaUnsatStep2 = false := rfl

/-- Step 3 contradiction: `x ∈ y ∧ x ∉ y`. -/
def formulaUnsatStep3 : Formula :=
  Formula.and
    (Formula.rel (Relation.mem (Term.var 1) (Term.var 2)))
    (Formula.rel (Relation.not_mem (Term.var 1) (Term.var 2)))

example : decideMLSSat formulaUnsatStep3 = false := rfl

example : 0 < wireSizeFormula formulaSat := formulaSize_pos formulaSat

example : 0 < wireSizeFormula formulaUnsatStep2 := formulaSize_pos formulaUnsatStep2

#eval decideMLSSat formulaSat
#eval decideMLSSat formulaUnsatStep2
#eval decideMLSSat formulaUnsatStep3

/-! ### Serialization Phase 2D (§8) -/

example :
    len (serializeFormula (Formula.rel (Relation.eq Term.empty Term.empty))) =
      wireSizeFormula (Formula.rel (Relation.eq Term.empty Term.empty)) :=
  len_serializeFormula _

example : stepsMLS (Formula.rel (Relation.eq Term.empty Term.empty)) > 0 :=
  stepsMLS_pos _

example :
    stepsMLS (Formula.and (Formula.rel (Relation.eq (Term.var 0) Term.empty))
      (Formula.rel (Relation.eq (Term.var 1) Term.empty))) >
      wireSizeFormula (Formula.and (Formula.rel (Relation.eq (Term.var 0) Term.empty))
        (Formula.rel (Relation.eq (Term.var 1) Term.empty))) := by
  simp [stepsMLS, stepsConjunct, formulaToConjunct?_and]
  decide

/-! ### Phase 3A — NP membership (§3) -/

example : InNP SatMLSChecker := SatMLSChecker_in_NP

example :
    verifySatMLS (serializeFormula (Formula.rel (Relation.eq Term.empty Term.empty))) [] = true := by
  rw [verifySatMLS_true_iff]
  simp [SatMLSChecker, decodeFormula?_serializeFormula, decideMLSSat, formulaToConjunct?,
    decideConjunct, relationToLiteral?, literalToFormula]
  decide

example :
    serializeFormula (Formula.rel (Relation.eq Term.empty Term.empty)) ∈ SatMLSChecker := by
  rw [← verifySatMLS_true_iff]
  simp [verifySatMLS, decodeFormula?_serializeFormula, decideMLSSat, formulaToConjunct?,
    decideConjunct, relationToLiteral?, literalToFormula]
  decide

/-! ### Phase 3B — encoding size bounds (§3) -/

example :
    formulaSize (Formula.rel (Relation.eq (Term.var 2) Term.empty)) ≤
      encodingBound (formulaAstMass (Formula.rel (Relation.eq (Term.var 2) Term.empty))) :=
  formulaSize_le_encodingBound _

example : IsPolynomial encodingBound := encodingBound_poly

example :
    formulaSize (Formula.and (Formula.rel (Relation.eq (Term.var 0) Term.empty))
      (Formula.rel (Relation.neq (Term.var 0) (Term.var 1)))) ≤
      encodingBound 10 := by
  refine formulaSize_le_polyMass _ 10 ?_
  simp [formulaAstMass, formulaNodes, relationNodes, termNodes, maxVarFormula,
    maxVarRelation, maxVarTerm]

/-! ### Phase 4A — NBH + POL-rankable μ₀ (§4) -/

open NBH

example : InNP NBHChecker := NBHChecker_in_NP

example : IsPolRankable μ₀ := μ₀_polRankable

example : InDistNP nbhProb := nbhProb_in_DistNP

example : NBHInstance.encode trivialInstance ∈ NBHChecker := trivialInstance_in_NBHChecker

example : μ₀.prob (NBHInstance.encode trivialInstance) = 1 := μ₀_mass_on_trivial

/-! ### Phase 4B — NBH → SatMLS reduction (§4) -/

open Reduction

example : DistributionalReduction nbhProb satMLSProb := nbhToSatMLS_red

example :
    NBHInstance.encode trivialInstance ∈ NBHChecker ↔
      reduceNBHToSatMLSStep (NBHInstance.encode trivialInstance) ∈ SatMLSChecker :=
  nbhToSatMLS_red_on_μ₀ _ (by simp [μ₀Support])

example : reduceNBHToSatMLSStep (NBHInstance.encode trivialInstance) = satTargetEnc := by
  simp [reduceNBHToSatMLSStep, μ₀Support]

/-! ### Phase 4C — NP-average completeness (Corollary 5.1) -/

open Completeness

example : IsNPAverageComplete satMLSProb := satMLSProb_NPAverageComplete

example : InDistNP satMLSProb := satMLSProb_in_DistNP

/-! ### Phase 5 — conditional non-AvP (§8) -/

open NonAvP

example : IsPolRankable simpleSatμ := simpleSatμ_polRankable

example (h : NEXP_neq_EXP) : ¬ AvP satMLSProb := SatMLS_average_hard h

example (h : NEXP_neq_EXP) :
    ∃ μ, IsPolRankable μ ∧ ¬ AvP ⟨SatMLSChecker, μ⟩ :=
  exists_simple_rankable_not_AvP h

#eval verifyNBH (NBHInstance.encode trivialInstance) trivialCert

#eval decideMLSSat (Formula.rel (Relation.eq Term.empty Term.empty))
#eval decideConjunct [.mem 0 1]
#eval decideConjunct [.mem 0 0]
#eval lenBot ([] : Bitstring)
#eval T_inv id 5
#eval T_inv (fun _ => 10) 3
-- `rank` and `Distribution.mass` are noncomputable; see `example` proofs above.

end AvgCaseMls.Tests
