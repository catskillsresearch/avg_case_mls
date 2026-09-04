/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.SAT
import AvgCaseMls.Serialization
import AvgCaseMls.MLSCodec
import AvgCaseMls.Section4.CookLevin.SATCodec
import Mathlib

/-!
# The CNF-SAT substitution into MLS

This is the substitution used in Theorem 5.1 of TR1995-711.  MLS variable
`0` is the distinguished set variable `x`; propositional variable `vᵢ` is
represented by MLS variable `i + 1`.  Thus `vᵢ` becomes `x ∈ setVar i` and
`¬vᵢ` becomes `x ∉ setVar i`.  Disjunctions and conjunctions are retained.
-/

namespace MLSInReduction

open MLS

/-! ## The exact membership-only fragment -/

/-- `MLS_in` terms are variables; no set constant or Boolean set operation occurs. -/
def IsMLSInTerm : Term → Prop
  | .var _ => True
  | _ => False

/-- Atomic formulas of `MLS_in` are positive or negative membership atoms. -/
def IsMLSInRelation : Relation → Prop
  | .mem x y | .not_mem x y => IsMLSInTerm x ∧ IsMLSInTerm y
  | _ => False

/--
The exact `MLS_in` fragment over the project's full `Formula`: arbitrary
propositional combinations of membership atoms between variables.
-/
def IsMLSIn : Formula → Prop
  | .rel r => IsMLSInRelation r
  | .not f => IsMLSIn f
  | .and f g | .or f g | .imp f g | .iff f g => IsMLSIn f ∧ IsMLSIn g

def distinguishedTerm : Term := .var 0

def setTerm (i : Nat) : Term := .var (Nat.succ i)

/--
Written with `casesOn` rather than pattern matching so that no `match_1`
auxiliary is generated.  Lean reuses such auxiliaries only within a module, so
a pattern match here would bind to a different auxiliary than `Challenge.lean`'s
and Palomar's elaborated-term comparison would reject it.
-/
def literalToMLS (l : SAT.Literal) : Formula :=
  l.casesOn (motive := fun _ => Formula)
    (fun i => .rel (.mem distinguishedTerm (setTerm i)))
    (fun i => .rel (.not_mem distinguishedTerm (setTerm i)))

/-- The empty clause is represented by the foundation-false atom `x ∈ x`. -/
def falseFormula : Formula :=
  .rel (.mem distinguishedTerm distinguishedTerm)

/--
The empty conjunction is represented by the foundation-true atom `x ∉ x`.
Equality atoms are unavailable here: `IsMLSInRelation` admits only `∈` and `∉`,
so `x = x` would take the translation outside the `MLS_in` fragment.
-/
def trueFormula : Formula :=
  .rel (.not_mem distinguishedTerm distinguishedTerm)

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
  exact MLS.ZFSet.regularity (env 0)

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
  | .rel (.not_mem (.var 0) (.var 0)) => some []
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

theorem literalToMLS_isMLSIn (literal : SAT.Literal) :
    IsMLSIn (literalToMLS literal) := by
  cases literal <;>
    simp [literalToMLS, IsMLSIn, IsMLSInRelation, IsMLSInTerm,
      distinguishedTerm, setTerm]

theorem clauseToMLS_isMLSIn (clause : SAT.Clause) :
    IsMLSIn (clauseToMLS clause) := by
  induction clause with
  | nil =>
      simp [clauseToMLS, falseFormula, IsMLSIn, IsMLSInRelation,
        IsMLSInTerm, distinguishedTerm]
  | cons literal clause ih =>
      exact ⟨literalToMLS_isMLSIn literal, ih⟩

theorem toMLS_isMLSIn (formula : SAT.CNF) :
    IsMLSIn (toMLS formula) := by
  induction formula with
  | nil =>
      simp [toMLS, trueFormula, IsMLSIn, IsMLSInRelation,
        IsMLSInTerm, distinguishedTerm]
  | cons clause formula ih =>
      exact ⟨clauseToMLS_isMLSIn clause, ih⟩

/-! ## Standard binary encoded languages and reduction -/

abbrev Bitstring := AvgCaseMls.Foundation.Bitstring

/-- Well-formed binary encodings of satisfiable `MLS_in` formulas. -/
def EncodedMLSInSAT : Set Bitstring :=
  {bits | ∃ formula,
    AvgCaseMls.MLSCodec.decodeFormula? bits = some formula ∧
    IsMLSIn formula ∧ MLSSatisfiable formula}

/-- The full standard binary encoded MLS satisfiability language. -/
abbrev EncodedMLSSAT : Set Bitstring :=
  AvgCaseMls.MLSCodec.EncodedMLSSAT

def sourceBits (formula : SAT.CNF) : Bitstring :=
  AvgCaseMls.Section4.CookLevin.encodeSATCNF formula

def encodedReduction (formula : SAT.CNF) : Bitstring :=
  AvgCaseMls.MLSCodec.encodeFormula (toMLS formula)

def fromEncodedReduction (bits : Bitstring) : Option SAT.CNF := do
  let formula ← AvgCaseMls.MLSCodec.decodeFormula? bits
  fromMLS formula

@[simp] theorem fromEncodedReduction_encodedReduction (formula : SAT.CNF) :
    fromEncodedReduction (encodedReduction formula) = some formula := by
  simp [fromEncodedReduction, encodedReduction]

theorem encodedReduction_injective : Function.Injective encodedReduction := by
  intro first second h
  have := congrArg fromEncodedReduction h
  simpa using this

/-- Executable recognizer for the exact image of the encoded reduction. -/
def encodedInRange (bits : Bitstring) : Bool :=
  match fromEncodedReduction bits with
  | some formula => decide (encodedReduction formula = bits)
  | none => false

theorem encodedInRange_eq_true_iff (bits : Bitstring) :
    encodedInRange bits = true ↔ bits ∈ Set.range encodedReduction := by
  constructor
  · intro h
    simp only [encodedInRange] at h
    split at h
    · rename_i formula hformula
      exact ⟨formula, by simpa using h⟩
    · simp at h
  · rintro ⟨formula, rfl⟩
    simp [encodedInRange]

theorem encodedReduction_mem_iff (formula : SAT.CNF) :
    sourceBits formula ∈ AvgCaseMls.Section4.CookLevin.EncodedSAT ↔
      encodedReduction formula ∈ EncodedMLSInSAT := by
  constructor
  · intro h
    rcases h with ⟨decoded, hdecode, hsatisfiable⟩
    have : decoded = formula := by
      symm
      simpa [sourceBits] using hdecode
    subst decoded
    exact ⟨toMLS formula, by simp [encodedReduction],
      toMLS_isMLSIn formula, (satisfiable_iff formula).mp hsatisfiable⟩
  · rintro ⟨decoded, hdecode, _, hsatisfiable⟩
    have : decoded = toMLS formula := by
      symm
      simpa [encodedReduction] using hdecode
    subst decoded
    exact ⟨formula, by simp [sourceBits],
      (satisfiable_iff formula).mpr hsatisfiable⟩

theorem encodedReduction_mem_fullMLS_iff (formula : SAT.CNF) :
    sourceBits formula ∈ AvgCaseMls.Section4.CookLevin.EncodedSAT ↔
      encodedReduction formula ∈ EncodedMLSSAT := by
  constructor
  · rintro ⟨decoded, hdecode, hsatisfiable⟩
    have : decoded = formula := by
      symm
      simpa [sourceBits] using hdecode
    subst decoded
    exact ⟨toMLS formula, by simp [encodedReduction],
      (satisfiable_iff formula).mp hsatisfiable⟩
  · rintro ⟨decoded, hdecode, hsatisfiable⟩
    have : decoded = toMLS formula := by
      symm
      simpa [encodedReduction] using hdecode
    subst decoded
    exact ⟨formula, by simp [sourceBits],
      (satisfiable_iff formula).mpr hsatisfiable⟩

/-! ## Binary wire bounds and honesty -/

private theorem encodeNat_le_succ (n : Nat) :
    (AvgCaseMls.Foundation.encodeNat n).length ≤
      (AvgCaseMls.Foundation.encodeNat (n + 1)).length := by
  rw [AvgCaseMls.Foundation.length_encodeNat,
    AvgCaseMls.Foundation.length_encodeNat]
  simp only [Nat.size_eq_bits_len]
  have hs : Nat.size n ≤ Nat.size (n + 1) := by
    rw [Nat.size_le]
    exact (Nat.lt_succ_self n).trans (Nat.lt_size_self (n + 1))
  omega

private theorem encodeNat_succ_le (n : Nat) :
    (AvgCaseMls.Foundation.encodeNat (n + 1)).length ≤
      (AvgCaseMls.Foundation.encodeNat n).length + 2 := by
  rw [AvgCaseMls.Foundation.length_encodeNat,
    AvgCaseMls.Foundation.length_encodeNat]
  simp only [Nat.size_eq_bits_len]
  have hs : Nat.size (n + 1) ≤ Nat.size n + 1 := by
    rw [Nat.size_le]
    have hn : n + 1 ≤ 2 ^ Nat.size n :=
      Nat.succ_le_iff.mpr (Nat.lt_size_self n)
    have hp : 2 ^ Nat.size n < 2 ^ (Nat.size n + 1) := by
      rw [pow_succ]
      have : 0 < 2 ^ Nat.size n := pow_pos (by omega) _
      omega
    exact hn.trans_lt hp
  omega

private def sourceLiteralWire : SAT.Literal → Nat
  | .pos i | .neg i => 1 + (AvgCaseMls.Foundation.encodeNat i).length

private def targetLiteralWire : SAT.Literal → Nat
  | .pos i | .neg i =>
      12 + (AvgCaseMls.Foundation.encodeNat (i + 1)).length

private def sourceClauseBodyWire (clause : SAT.Clause) : Nat :=
  (clause.map sourceLiteralWire).sum

private def targetClauseIndexWire (clause : SAT.Clause) : Nat :=
  (clause.map fun literal => targetLiteralWire literal).sum

private theorem encodeSATLiteral_length (literal : SAT.Literal) :
    (AvgCaseMls.Section4.CookLevin.encodeSATLiteral literal).length =
      sourceLiteralWire literal := by
  cases literal <;>
    simp [AvgCaseMls.Section4.CookLevin.encodeSATLiteral, sourceLiteralWire] <;>
    omega

private theorem encodeSATLiterals_length (clause : SAT.Clause) :
    (AvgCaseMls.Section4.CookLevin.encodeSATLiterals clause).length =
      sourceClauseBodyWire clause := by
  induction clause with
  | nil => rfl
  | cons literal clause ih =>
      simp [AvgCaseMls.Section4.CookLevin.encodeSATLiterals,
        sourceClauseBodyWire, encodeSATLiteral_length, ih]

private theorem literalToMLS_wire (literal : SAT.Literal) :
    (AvgCaseMls.MLSCodec.encodeFormula (literalToMLS literal)).length =
      targetLiteralWire literal := by
  cases literal <;>
    simp [AvgCaseMls.MLSCodec.encodeFormula,
      AvgCaseMls.MLSCodec.encodeRelation, AvgCaseMls.MLSCodec.encodeTerm,
      literalToMLS, targetLiteralWire, distinguishedTerm, setTerm] <;>
    omega

private theorem clauseToMLS_wire (clause : SAT.Clause) :
    (AvgCaseMls.MLSCodec.encodeFormula (clauseToMLS clause)).length =
      3 * clause.length + targetClauseIndexWire clause + 13 := by
  induction clause with
  | nil =>
      simp [clauseToMLS, falseFormula, targetClauseIndexWire,
        AvgCaseMls.MLSCodec.encodeFormula,
        AvgCaseMls.MLSCodec.encodeRelation, AvgCaseMls.MLSCodec.encodeTerm,
        distinguishedTerm]
  | cons literal clause ih =>
      simp [clauseToMLS, targetClauseIndexWire,
        AvgCaseMls.MLSCodec.encodeFormula, literalToMLS_wire, ih]
      omega

private theorem sourceLiteralWire_le_target (literal : SAT.Literal) :
    sourceLiteralWire literal ≤ targetLiteralWire literal := by
  cases literal with
  | pos i | neg i =>
      simp only [sourceLiteralWire, targetLiteralWire]
      have h := encodeNat_le_succ i
      omega

private theorem targetLiteralWire_le_source (literal : SAT.Literal) :
    targetLiteralWire literal ≤ 14 * sourceLiteralWire literal := by
  cases literal with
  | pos i | neg i =>
      simp only [sourceLiteralWire, targetLiteralWire]
      have h := encodeNat_succ_le i
      have hpos : 0 < (AvgCaseMls.Foundation.encodeNat i).length := by
        rw [AvgCaseMls.Foundation.length_encodeNat]
        omega
      omega

private theorem sourceClauseBody_le_target (clause : SAT.Clause) :
    sourceClauseBodyWire clause ≤ targetClauseIndexWire clause := by
  induction clause with
  | nil => simp [sourceClauseBodyWire, targetClauseIndexWire]
  | cons literal clause ih =>
      simp only [sourceClauseBodyWire, targetClauseIndexWire,
        List.map_cons, List.sum_cons]
      exact Nat.add_le_add (sourceLiteralWire_le_target literal) ih

private theorem targetClauseIndex_le_source (clause : SAT.Clause) :
    targetClauseIndexWire clause ≤ 14 * sourceClauseBodyWire clause := by
  induction clause with
  | nil => simp [sourceClauseBodyWire, targetClauseIndexWire]
  | cons literal clause ih =>
      have hl := targetLiteralWire_le_source literal
      simp [sourceClauseBodyWire, targetClauseIndexWire] at ih ⊢
      omega

private theorem clause_length_le_sourceBody (clause : SAT.Clause) :
    clause.length ≤ sourceClauseBodyWire clause := by
  induction clause with
  | nil => simp [sourceClauseBodyWire]
  | cons literal clause ih =>
      change clause.length ≤ (clause.map sourceLiteralWire).sum at ih
      change clause.length + 1 ≤
        sourceLiteralWire literal + (clause.map sourceLiteralWire).sum
      have hpositive : 1 ≤ sourceLiteralWire literal := by
        cases literal <;> simp [sourceLiteralWire]
      omega

private theorem encodedClause_honest (clause : SAT.Clause) :
    (AvgCaseMls.Section4.CookLevin.encodeSATClause clause).length ≤
      (AvgCaseMls.MLSCodec.encodeFormula (clauseToMLS clause)).length := by
  rw [AvgCaseMls.Section4.CookLevin.encodeSATClause,
    List.length_append, encodeSATLiterals_length, clauseToMLS_wire]
  have hcount := AvgCaseMls.Foundation.length_encodeNat_le clause.length
  have hbody := sourceClauseBody_le_target clause
  omega

private theorem encodeSATClauses_honest (formula : SAT.CNF) :
    (AvgCaseMls.Section4.CookLevin.encodeSATClauses formula).length +
      3 * formula.length + 13 ≤
      (AvgCaseMls.MLSCodec.encodeFormula (toMLS formula)).length := by
  induction formula with
  | nil =>
      simp [AvgCaseMls.Section4.CookLevin.encodeSATClauses, toMLS,
        trueFormula, AvgCaseMls.MLSCodec.encodeFormula,
        AvgCaseMls.MLSCodec.encodeRelation, AvgCaseMls.MLSCodec.encodeTerm,
        distinguishedTerm]
  | cons clause formula ih =>
      have hc := encodedClause_honest clause
      simp only [AvgCaseMls.Section4.CookLevin.encodeSATClauses,
        List.length_append, List.length_cons, toMLS,
        AvgCaseMls.MLSCodec.encodeFormula, List.append_assoc]
      simp only [AvgCaseMls.MLSCodec.encodeFormula, List.length_append,
        List.length_cons, List.length_nil] at ih ⊢
      omega

/-- The binary reduction is honest on the exact standard SAT and MLS wires. -/
theorem encodedReduction_honest (formula : SAT.CNF) :
    (sourceBits formula).length ≤ (encodedReduction formula).length := by
  have hbody := encodeSATClauses_honest formula
  have hheader := AvgCaseMls.Foundation.length_encodeNat_le formula.length
  simp only [sourceBits, AvgCaseMls.Section4.CookLevin.encodeSATCNF,
    List.length_append, encodedReduction]
  omega

private theorem encodedClause_wire_le (clause : SAT.Clause) :
    (AvgCaseMls.MLSCodec.encodeFormula (clauseToMLS clause)).length ≤
      17 * (AvgCaseMls.Section4.CookLevin.encodeSATClause clause).length := by
  cases clause with
  | nil =>
      simp [clauseToMLS_wire, AvgCaseMls.Section4.CookLevin.encodeSATClause,
        AvgCaseMls.Section4.CookLevin.encodeSATLiterals,
        sourceClauseBodyWire, targetClauseIndexWire]
  | cons literal clause =>
      rw [clauseToMLS_wire, AvgCaseMls.Section4.CookLevin.encodeSATClause,
        List.length_append, encodeSATLiterals_length]
      have hindex := targetClauseIndex_le_source (literal :: clause)
      have hcount :
          (literal :: clause).length ≤ sourceClauseBodyWire (literal :: clause) := by
        exact clause_length_le_sourceBody _
      have hheader :
          0 < (AvgCaseMls.Foundation.encodeNat (literal :: clause).length).length := by
        rw [AvgCaseMls.Foundation.length_encodeNat]
        omega
      omega

def encodedWireBound (n : Nat) : Nat := 40 * n + 13

theorem encodedWireBound_polynomial :
    AvgCaseMls.Foundation.IsPolynomial encodedWireBound := by
  apply AvgCaseMls.Foundation.IsPolynomial.bounded 53 1
  intro n
  simp [encodedWireBound]
  omega

private theorem encodeSATClauses_wire_le (formula : SAT.CNF) :
    (AvgCaseMls.MLSCodec.encodeFormula (toMLS formula)).length ≤
      40 * (AvgCaseMls.Section4.CookLevin.encodeSATClauses formula).length +
        13 := by
  induction formula with
  | nil =>
      simp [AvgCaseMls.Section4.CookLevin.encodeSATClauses, toMLS,
        trueFormula, AvgCaseMls.MLSCodec.encodeFormula,
        AvgCaseMls.MLSCodec.encodeRelation, AvgCaseMls.MLSCodec.encodeTerm,
        distinguishedTerm]
  | cons clause formula ih =>
      have hc := encodedClause_wire_le clause
      have hcpos :
          0 < (AvgCaseMls.Section4.CookLevin.encodeSATClause clause).length := by
        simp [AvgCaseMls.Section4.CookLevin.encodeSATClause,
          AvgCaseMls.Foundation.length_encodeNat]
      simp only [AvgCaseMls.Section4.CookLevin.encodeSATClauses,
        List.length_append, toMLS, AvgCaseMls.MLSCodec.encodeFormula,
        List.append_assoc]
      simp only [AvgCaseMls.MLSCodec.encodeFormula, List.length_append,
        List.length_cons, List.length_nil] at ih ⊢
      omega

theorem encodedReduction_wire_le (formula : SAT.CNF) :
    (encodedReduction formula).length ≤
      encodedWireBound (sourceBits formula).length := by
  have h := encodeSATClauses_wire_le formula
  simp [encodedReduction, encodedWireBound, sourceBits,
    AvgCaseMls.Section4.CookLevin.encodeSATCNF] at h ⊢
  omega

end MLSInReduction
