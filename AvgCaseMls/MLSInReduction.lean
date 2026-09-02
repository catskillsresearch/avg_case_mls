/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.SAT
import AvgCaseMls.Serialization

/-!
# The CNF-SAT substitution into MLS

This is the substitution used in Theorem 5.1 of TR1995-711.  MLS variable
`0` is the distinguished set variable `x`; propositional variable `vᵢ` is
represented by MLS variable `i + 1`.  Thus `vᵢ` becomes `x ∈ setVar i` and
`¬vᵢ` becomes `x ∉ setVar i`.  Disjunctions and conjunctions are retained.
-/

namespace MLSInReduction

open MLS

def distinguishedTerm : Term := .var 0

def setTerm (i : Nat) : Term := .var (Nat.succ i)

def literalToMLS : SAT.Literal → Formula
  | .pos i => .rel (.mem distinguishedTerm (setTerm i))
  | .neg i => .rel (.not_mem distinguishedTerm (setTerm i))

/-- The empty clause is represented by the foundation-false atom `x ∈ x`. -/
def falseFormula : Formula :=
  .rel (.mem distinguishedTerm distinguishedTerm)

/-- The empty conjunction is represented by the valid atom `x = x`. -/
def trueFormula : Formula :=
  .rel (.eq distinguishedTerm distinguishedTerm)

def clauseToMLS : SAT.Clause → Formula
  | [] => falseFormula
  | l :: c => .or (literalToMLS l) (clauseToMLS c)

def toMLS : SAT.CNF → Formula
  | [] => trueFormula
  | c :: φ => .and (clauseToMLS c) (toMLS φ)

theorem evalLiteral_literalToMLS (env : Env) (l : SAT.Literal) :
    evalFormula env (literalToMLS l) ↔
      SAT.evalLiteral (fun i => ZFSet.mem (env 0) (env (Nat.succ i))) l := by
  cases l <;> rfl

@[simp] theorem eval_falseFormula (env : Env) :
    ¬ evalFormula env falseFormula := by
  simpa [falseFormula, distinguishedTerm, evalFormula, evalTerm] using
    MLS.ZFSet.regularity (env 0)

@[simp] theorem eval_trueFormula (env : Env) :
    evalFormula env trueFormula := by
  simp [trueFormula, distinguishedTerm, evalFormula, evalTerm]

theorem eval_clauseToMLS (env : Env) (c : SAT.Clause) :
    evalFormula env (clauseToMLS c) ↔
      SAT.evalClause (fun i => ZFSet.mem (env 0) (env (Nat.succ i))) c := by
  induction c with
  | nil => simp [clauseToMLS]
  | cons l c ih =>
      simp [clauseToMLS, evalFormula, evalLiteral_literalToMLS, ih]

theorem eval_toMLS (env : Env) (φ : SAT.CNF) :
    evalFormula env (toMLS φ) ↔
      SAT.evalCNF (fun i => ZFSet.mem (env 0) (env (Nat.succ i))) φ := by
  induction φ with
  | nil => simp [toMLS]
  | cons c φ ih =>
      simp [toMLS, evalFormula, eval_clauseToMLS, ih]

noncomputable def envOfAssignment (a : SAT.Assignment) : Env := fun n =>
  if n = 0 then MLS.ZFSet.empty
  else @ite MLS.ZFSet (a (n - 1)) (Classical.propDecidable _) {MLS.ZFSet.empty} MLS.ZFSet.empty

theorem envOfAssignment_mem (a : SAT.Assignment) (i : Nat) :
    ZFSet.mem (envOfAssignment a 0) (envOfAssignment a (Nat.succ i)) ↔ a i := by
  classical
  by_cases h : a i
  · simp [envOfAssignment, h, MLS.ZFSet.mem, MLS.ZFSet.empty]
  · simp [envOfAssignment, h, MLS.ZFSet.mem, MLS.ZFSet.empty]

def MLSSatisfiable (f : Formula) : Prop :=
  ∃ env, evalFormula env f

/-- Semantic correctness of the Theorem 5.1 substitution. -/
theorem satisfiable_iff (φ : SAT.CNF) :
    SAT.Satisfiable φ ↔ MLSSatisfiable (toMLS φ) := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨envOfAssignment a, ?_⟩
    rw [eval_toMLS]
    simpa only [envOfAssignment_mem] using ha
  · rintro ⟨env, henv⟩
    refine ⟨fun i => ZFSet.mem (env 0) (env (Nat.succ i)), ?_⟩
    exact (eval_toMLS env φ).mp henv

/-! ## A syntactic left inverse -/

def literalFromMLS : Formula → Option SAT.Literal
  | .rel (.mem (.var 0) (.var (i + 1))) => some (.pos i)
  | .rel (.not_mem (.var 0) (.var (i + 1))) => some (.neg i)
  | _ => none

def clauseFromMLS : Formula → Option SAT.Clause
  | .rel (.mem (.var 0) (.var 0)) => some []
  | .or f rest => do
      let l ← literalFromMLS f
      let c ← clauseFromMLS rest
      pure (l :: c)
  | _ => none

def fromMLS : Formula → Option SAT.CNF
  | .rel (.eq (.var 0) (.var 0)) => some []
  | .and f rest => do
      let c ← clauseFromMLS f
      let φ ← fromMLS rest
      pure (c :: φ)
  | _ => none

@[simp] theorem literalFromMLS_literalToMLS (l : SAT.Literal) :
    literalFromMLS (literalToMLS l) = some l := by
  cases l <;> simp [literalFromMLS, literalToMLS, distinguishedTerm, setTerm]

@[simp] theorem clauseFromMLS_clauseToMLS (c : SAT.Clause) :
    clauseFromMLS (clauseToMLS c) = some c := by
  induction c with
  | nil => simp [clauseFromMLS, clauseToMLS, falseFormula, distinguishedTerm]
  | cons l c ih =>
      simp [clauseFromMLS, clauseToMLS, ih]

@[simp] theorem fromMLS_toMLS (φ : SAT.CNF) :
    fromMLS (toMLS φ) = some φ := by
  induction φ with
  | nil => simp [fromMLS, toMLS, trueFormula, distinguishedTerm]
  | cons c φ ih =>
      simp [fromMLS, toMLS, ih]

theorem toMLS_injective : Function.Injective toMLS := by
  intro φ ψ h
  have := congrArg fromMLS h
  simpa using this

/-! ## Structural size -/

theorem formulaNodes_literalToMLS (l : SAT.Literal) :
    formulaNodes (literalToMLS l) = 4 := by
  cases l <;>
    simp [literalToMLS, distinguishedTerm, setTerm, formulaNodes, relationNodes, termNodes]

theorem formulaNodes_clauseToMLS (c : SAT.Clause) :
    formulaNodes (clauseToMLS c) + 1 = 5 * (c.length + 1) := by
  induction c with
  | nil =>
      simp [clauseToMLS, falseFormula, distinguishedTerm, formulaNodes, relationNodes, termNodes]
  | cons l c ih =>
      simp only [clauseToMLS, formulaNodes, formulaNodes_literalToMLS, List.length_cons]
      omega

/-- The translation has exactly five MLS AST nodes per CNF structural unit, minus one. -/
theorem formulaNodes_toMLS (φ : SAT.CNF) :
    formulaNodes (toMLS φ) + 1 = 5 * SAT.size φ := by
  induction φ with
  | nil =>
      simp [toMLS, trueFormula, distinguishedTerm, formulaNodes, relationNodes, termNodes,
        SAT.size]
  | cons c φ ih =>
      simp only [toMLS, formulaNodes]
      rw [SAT.size_cons]
      have hc := formulaNodes_clauseToMLS c
      omega

theorem formulaNodes_toMLS_le (φ : SAT.CNF) :
    formulaNodes (toMLS φ) ≤ 5 * SAT.size φ := by
  exact Nat.le_of_lt (by
    rw [← formulaNodes_toMLS]
    exact Nat.lt_succ_self _)

end MLSInReduction
