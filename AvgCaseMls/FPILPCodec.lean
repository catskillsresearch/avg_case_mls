import AvgCaseMls.FPILP
import AvgCaseMls.Section4.CookLevin.SATCodec

/-!
# Encoded SAT to fixed-precision integer-linear feasibility

This file closes the representation obligations around TR1995, Theorem 5.3.
Natural variable names are canonically renumbered by their position in the
sorted list of variables that actually occur.  Thus sparse binary names never
cause a max-index expansion.  A provenance frame preserves the complete source
syntax while the feasibility constraints use only dense `Fin` indices.
-/

namespace TR1995.FPILPEncoded

open AvgCaseMls.Foundation
open AvgCaseMls.Section4.CookLevin
open TR1995.FPILPSource

/-! ## Canonical dense-variable normalization -/

def literalIndex : SAT.Literal → Nat
  | .pos index | .neg index => index

def occurringVariables (formula : SAT.CNF) : List Nat :=
  formula.flatMap fun clause => clause.map literalIndex

def vars (formula : SAT.CNF) : List Nat :=
  (occurringVariables formula).toFinset.sort (· ≤ ·)

def variableCount (formula : SAT.CNF) : Nat := (vars formula).length

theorem vars_nodup (formula : SAT.CNF) : (vars formula).Nodup :=
  Finset.sort_nodup _ _

theorem vars_sorted (formula : SAT.CNF) :
    (vars formula).Pairwise (· ≤ ·) := by
  simp [vars]

theorem literalIndex_mem_vars {formula : SAT.CNF}
    {clause : SAT.Clause} (hc : clause ∈ formula)
    {literal : SAT.Literal} (hl : literal ∈ clause) :
    literalIndex literal ∈ vars formula := by
  rw [vars, Finset.mem_sort]
  simp only [List.mem_toFinset, occurringVariables, List.mem_flatMap,
    List.mem_map]
  exact ⟨clause, hc, literal, hl, rfl⟩

def denseIndex (formula : SAT.CNF) (index : Nat)
    (h : index ∈ vars formula) : Fin (variableCount formula) :=
  ⟨(vars formula).idxOf index,
    (by simpa [variableCount] using List.idxOf_lt_length_iff.mpr h)⟩

@[simp] theorem vars_get_denseIndex (formula : SAT.CNF) (index : Nat)
    (h : index ∈ vars formula) :
    (vars formula).get (denseIndex formula index h) = index := by
  exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr h)

def normalizeLiteral (formula : SAT.CNF) (literal : SAT.Literal)
    (h : literalIndex literal ∈ vars formula) :
    Literal (variableCount formula) := by
  cases literal with
  | pos index =>
      exact .pos (denseIndex formula index (by simpa [literalIndex] using h))
  | neg index =>
      exact .neg (denseIndex formula index (by simpa [literalIndex] using h))

def normalizeClause (formula : SAT.CNF) (clause : SAT.Clause)
    (hc : clause ∈ formula) : Clause (variableCount formula) :=
  clause.attach.map fun literal =>
    normalizeLiteral formula literal.1
      (literalIndex_mem_vars hc literal.2)

def normalize (formula : SAT.CNF) : CNF (variableCount formula) :=
  formula.attach.map fun clause => normalizeClause formula clause.1 clause.2

private theorem normalizeLiteral_eval_forward (formula : SAT.CNF)
    (assignment : SAT.Assignment) (clause : SAT.Clause)
    (hc : clause ∈ formula) (literal : SAT.Literal) (hl : literal ∈ clause) :
    (normalizeLiteral formula literal (literalIndex_mem_vars hc hl)).eval
        (fun index => @decide (assignment ((vars formula).get index))
          (Classical.propDecidable _)) = true ↔
      SAT.evalLiteral assignment literal := by
  classical
  cases literal with
  | pos index =>
      have hm : index ∈ vars formula := by
        simpa [literalIndex] using literalIndex_mem_vars hc hl
      change decide (assignment ((vars formula).get
        (denseIndex formula index hm))) = true ↔ assignment index
      rw [vars_get_denseIndex]
      simp
  | neg index =>
      have hm : index ∈ vars formula := by
        simpa [literalIndex] using literalIndex_mem_vars hc hl
      change (!decide (assignment ((vars formula).get
        (denseIndex formula index hm)))) = true ↔ ¬ assignment index
      rw [vars_get_denseIndex]
      simp

theorem normalize_satisfiable_of_satisfiable (formula : SAT.CNF) :
    SAT.Satisfiable formula → (normalize formula).Satisfiable := by
  classical
  rintro ⟨assignment, hsatisfied⟩
  refine ⟨fun index => @decide (assignment ((vars formula).get index))
    (Classical.propDecidable _), ?_⟩
  intro clause hclause
  obtain ⟨⟨sourceClause, hsource⟩, -, rfl⟩ := List.mem_map.mp hclause
  obtain ⟨literal, hliteral, heval⟩ := hsatisfied sourceClause hsource
  refine ⟨normalizeLiteral formula literal
      (literalIndex_mem_vars hsource hliteral), ?_, ?_⟩
  · exact List.mem_map.mpr
      ⟨⟨literal, hliteral⟩, by simp, rfl⟩
  exact (normalizeLiteral_eval_forward formula assignment sourceClause
    hsource literal hliteral).2 heval

private theorem normalizeLiteral_eval_reverse (formula : SAT.CNF)
    (assignment : Assignment (variableCount formula))
    (clause : SAT.Clause) (hc : clause ∈ formula)
    (literal : SAT.Literal) (hl : literal ∈ clause) :
    SAT.evalLiteral
        (fun index =>
          if h : index ∈ vars formula
          then assignment (denseIndex formula index h) = true
          else False)
        literal ↔
      (normalizeLiteral formula literal
        (literalIndex_mem_vars hc hl)).eval assignment = true := by
  have hm := literalIndex_mem_vars hc hl
  cases literal <;> rename_i index
  · have hm' : index ∈ vars formula := by simpa [literalIndex] using hm
    simp [normalizeLiteral, Literal.eval, SAT.evalLiteral, hm']
  · have hm' : index ∈ vars formula := by simpa [literalIndex] using hm
    cases hvalue : assignment (denseIndex formula index hm') <;>
      simp [normalizeLiteral, Literal.eval, SAT.evalLiteral,
        hm', hvalue]

theorem satisfiable_of_normalize_satisfiable (formula : SAT.CNF) :
    (normalize formula).Satisfiable → SAT.Satisfiable formula := by
  rintro ⟨assignment, hsatisfied⟩
  refine ⟨fun index =>
    if h : index ∈ vars formula
    then assignment (denseIndex formula index h) = true
    else False, ?_⟩
  intro clause hclause
  have hnormalized :
      normalizeClause formula clause hclause ∈ normalize formula :=
    List.mem_map.mpr ⟨⟨clause, hclause⟩, by simp, rfl⟩
  obtain ⟨literal, hliteral, heval⟩ :=
    hsatisfied (normalizeClause formula clause hclause) hnormalized
  obtain ⟨⟨sourceLiteral, hsource⟩, -, rfl⟩ :=
    List.mem_map.mp hliteral
  refine ⟨sourceLiteral, hsource, ?_⟩
  exact (normalizeLiteral_eval_reverse formula assignment clause hclause
    sourceLiteral hsource).2 heval

theorem normalize_satisfiable_iff (formula : SAT.CNF) :
    (normalize formula).Satisfiable ↔ SAT.Satisfiable formula :=
  ⟨satisfiable_of_normalize_satisfiable formula,
    normalize_satisfiable_of_satisfiable formula⟩

/-! ## Canonical self-delimiting FPILP codec -/

def encodeInt : Int → Bitstring
  | .ofNat magnitude => false :: encodeNat magnitude
  | .negSucc predecessor => true :: encodeNat (predecessor + 1)

def decodeInt? : Bitstring → Option (Int × Bitstring)
  | [] => none
  | negative :: bits => do
      let (magnitude, rest) ← decodeNat? bits
      some (if negative then -(Int.ofNat magnitude) else Int.ofNat magnitude,
        rest)

@[simp] theorem decodeInt?_suffix (value : Int) (rest : Bitstring) :
    decodeInt? (encodeInt value ++ rest) = some (value, rest) := by
  cases value with
  | ofNat n => simp [encodeInt, decodeInt?, decodeNat?_suffix]
  | negSucc n =>
      simp [encodeInt, decodeInt?, decodeNat?_suffix, Int.negSucc_eq]

def encodeTerm {n : Nat} : Term n → Bitstring
  | .var index => false :: encodeNat index.val
  | .oneMinus index => true :: encodeNat index.val

def decodeTerm? (n : Nat) : Bitstring → Option (Term n × Bitstring)
  | [] => none
  | tag :: bits => do
      let (index, rest) ← decodeNat? bits
      if h : index < n then
        some (if tag then .oneMinus ⟨index, h⟩ else .var ⟨index, h⟩, rest)
      else none

@[simp] theorem decodeTerm?_suffix {n : Nat} (term : Term n)
    (rest : Bitstring) :
    decodeTerm? n (encodeTerm term ++ rest) = some (term, rest) := by
  cases term with
  | var index =>
      simp [encodeTerm, decodeTerm?, decodeNat?_suffix, index.isLt]
  | oneMinus index =>
      simp [encodeTerm, decodeTerm?, decodeNat?_suffix, index.isLt]

def encodeTerms {n : Nat} : List (Term n) → Bitstring
  | [] => []
  | term :: terms => encodeTerm term ++ encodeTerms terms

def decodeTerms? (n : Nat) : Nat → Bitstring →
    Option (List (Term n) × Bitstring)
  | 0, bits => some ([], bits)
  | count + 1, bits => do
      let (term, bits) ← decodeTerm? n bits
      let (terms, rest) ← decodeTerms? n count bits
      some (term :: terms, rest)

@[simp] theorem decodeTerms?_suffix {n : Nat} (terms : List (Term n))
    (rest : Bitstring) :
    decodeTerms? n terms.length (encodeTerms terms ++ rest) =
      some (terms, rest) := by
  induction terms with
  | nil => rfl
  | cons term terms ih =>
      simp [encodeTerms, decodeTerms?, decodeTerm?_suffix, ih]

def encodeInequality {n : Nat} (inequality : Inequality n) : Bitstring :=
  encodeNat inequality.lhs.length ++ encodeTerms inequality.lhs ++
    encodeInt inequality.rhs

def decodeInequality? (n : Nat) (bits : Bitstring) :
    Option (Inequality n × Bitstring) := do
  let (count, bits) ← decodeNat? bits
  let (terms, bits) ← decodeTerms? n count bits
  let (rhs, rest) ← decodeInt? bits
  some (⟨terms, rhs⟩, rest)

@[simp] theorem decodeInequality?_suffix {n : Nat}
    (inequality : Inequality n) (rest : Bitstring) :
    decodeInequality? n (encodeInequality inequality ++ rest) =
      some (inequality, rest) := by
  cases inequality
  simp [encodeInequality, decodeInequality?, decodeNat?_suffix,
    decodeTerms?_suffix, decodeInt?_suffix, List.append_assoc]

def encodeInequalities {n : Nat} : List (Inequality n) → Bitstring
  | [] => []
  | inequality :: inequalities =>
      encodeInequality inequality ++ encodeInequalities inequalities

def decodeInequalities? (n : Nat) : Nat → Bitstring →
    Option (List (Inequality n) × Bitstring)
  | 0, bits => some ([], bits)
  | count + 1, bits => do
      let (inequality, bits) ← decodeInequality? n bits
      let (inequalities, rest) ← decodeInequalities? n count bits
      some (inequality :: inequalities, rest)

@[simp] theorem decodeInequalities?_suffix {n : Nat}
    (inequalities : List (Inequality n)) (rest : Bitstring) :
    decodeInequalities? n inequalities.length
      (encodeInequalities inequalities ++ rest) =
      some (inequalities, rest) := by
  induction inequalities with
  | nil => rfl
  | cons inequality inequalities ih =>
      simp [encodeInequalities, decodeInequalities?,
        decodeInequality?_suffix, ih]

def encodeFPILP {n : Nat} (problem : FPILP n) : Bitstring :=
  encodeNat n ++ encodeNat problem.constraints.length ++
    encodeInequalities problem.constraints

abbrev DecodedFPILP := Σ n, FPILP n

def decodeFPILP? (bits : Bitstring) : Option DecodedFPILP := do
  let (n, bits) ← decodeNat? bits
  let (count, bits) ← decodeNat? bits
  let (constraints, rest) ← decodeInequalities? n count bits
  if rest = [] then some (Sigma.mk n ⟨constraints⟩) else none

@[simp] theorem decodeFPILP?_encode {n : Nat} (problem : FPILP n) :
    decodeFPILP? (encodeFPILP problem) = some (Sigma.mk n problem) := by
  cases problem with
  | mk constraints =>
      have hdecode :
          decodeInequalities? n constraints.length
            (encodeInequalities constraints) = some (constraints, []) := by
        simpa using decodeInequalities?_suffix constraints []
      simp [decodeFPILP?, encodeFPILP, decodeNat?_suffix, hdecode,
        List.append_assoc]

theorem encodeFPILP_injective_fixed {n : Nat} :
    Function.Injective (@encodeFPILP n) := by
  intro first second h
  have := congrArg decodeFPILP? h
  rw [decodeFPILP?_encode, decodeFPILP?_encode] at this
  cases this
  rfl

def EncodedFPILPFeasibility : Set Bitstring :=
  { bits | ∃ n problem,
      decodeFPILP? bits = some (Sigma.mk n problem) ∧ problem.Feasible }

@[simp] theorem encodeFPILP_mem_iff {n : Nat} (problem : FPILP n) :
    encodeFPILP problem ∈ EncodedFPILPFeasibility ↔ problem.Feasible := by
  constructor
  · rintro ⟨m, decoded, hdecode, hfeasible⟩
    rw [decodeFPILP?_encode] at hdecode
    cases hdecode
    exact hfeasible
  · intro hfeasible
    exact ⟨n, problem, decodeFPILP?_encode problem, hfeasible⟩

/-! ## Encoded reduction, inverse, and range recognition -/

def reduceFormula (formula : SAT.CNF) : FPILP (variableCount formula) :=
  satToFPILP (normalize formula)

/-- Provenance-framed reduction output: source syntax followed by dense FPILP. -/
def encodedReduction (formula : SAT.CNF) : Bitstring :=
  let source := encodeSATCNF formula
  encodeNat source.length ++ source ++ encodeFPILP (reduceFormula formula)

@[simp] theorem encodedReduction_length (formula : SAT.CNF) :
    (encodedReduction formula).length =
      (encodeNat (encodeSATCNF formula).length).length +
      (encodeSATCNF formula).length +
      (encodeFPILP (reduceFormula formula)).length := by
  simp [encodedReduction]
  omega

def decodeDenseReduction? (bits : Bitstring) : Option SAT.CNF := do
  let (sourceWidth, rest) ← decodeNat? bits
  if sourceWidth ≤ rest.length then
    let source := rest.take sourceWidth
    let target := rest.drop sourceWidth
    let formula ← decodeSATCNF? source
    if target = encodeFPILP (reduceFormula formula) then some formula else none
  else none

@[simp] theorem decodeDenseReduction?_encodedReduction (formula : SAT.CNF) :
    decodeDenseReduction? (encodedReduction formula) = some formula := by
  simp [decodeDenseReduction?, encodedReduction, decodeNat?_suffix]

def EncodedDenseFPILPFeasibility : Set Bitstring :=
  { bits | ∃ formula,
      decodeDenseReduction? bits = some formula ∧
      (reduceFormula formula).Feasible }

theorem encodedReduction_correct (formula : SAT.CNF) :
    encodeSATCNF formula ∈ EncodedSAT ↔
      encodedReduction formula ∈ EncodedDenseFPILPFeasibility := by
  rw [show encodeSATCNF formula ∈ EncodedSAT ↔
      SAT.Satisfiable formula by
    constructor
    · rintro ⟨decoded, hdecode, hsatisfiable⟩
      rw [decodeSATCNF?_encode] at hdecode
      cases hdecode
      exact hsatisfiable
    · intro hsatisfiable
      exact ⟨formula, decodeSATCNF?_encode formula, hsatisfiable⟩]
  simp [EncodedDenseFPILPFeasibility, reduceFormula,
    satToFPILP_feasible_iff,
    normalize_satisfiable_iff]

def inverseEncodedReduction (bits : Bitstring) : Bitstring :=
  match decodeDenseReduction? bits with
  | none => []
  | some formula => encodeSATCNF formula

@[simp] theorem inverseEncodedReduction_apply (formula : SAT.CNF) :
    inverseEncodedReduction (encodedReduction formula) =
      encodeSATCNF formula := by
  unfold inverseEncodedReduction
  rw [decodeDenseReduction?_encodedReduction]

theorem encodedReduction_injective :
    Function.Injective encodedReduction := by
  intro first second h
  have hinverse := congrArg inverseEncodedReduction h
  simp only [inverseEncodedReduction_apply] at hinverse
  exact encodeSATCNF_injective hinverse

theorem encodedReduction_honest (formula : SAT.CNF) :
    (encodeSATCNF formula).length ≤ (encodedReduction formula).length := by
  rw [encodedReduction_length]
  omega

def recognizesReductionRange (bits : Bitstring) : Bool :=
  match decodeDenseReduction? bits with
  | none => false
  | some formula => decide (encodedReduction formula = bits)

theorem recognizesReductionRange_spec (bits : Bitstring) :
    recognizesReductionRange bits = true ↔
      ∃ formula, encodedReduction formula = bits := by
  unfold recognizesReductionRange
  cases hdecode : decodeDenseReduction? bits with
  | none =>
      simp only [Bool.false_eq_true, false_iff, not_exists]
      intro formula heq
      subst bits
      simp at hdecode
  | some formula =>
      constructor
      · intro h
        exact ⟨formula, of_decide_eq_true h⟩
      · rintro ⟨source, rfl⟩
        simp at hdecode
        cases hdecode
        exact decide_eq_true rfl

/-! ## Exact wire accounting -/

def termWireSize {n : Nat} (term : Term n) : Nat :=
  1 + (encodeNat (match term with | .var i | .oneMinus i => i.val)).length

def inequalityWireSize {n : Nat} (inequality : Inequality n) : Nat :=
  (encodeNat inequality.lhs.length).length +
    (inequality.lhs.map termWireSize).sum +
    (encodeInt inequality.rhs).length

def fpilpWireSize {n : Nat} (problem : FPILP n) : Nat :=
  (encodeNat n).length + (encodeNat problem.constraints.length).length +
    (problem.constraints.map inequalityWireSize).sum

@[simp] theorem encodeTerm_length {n : Nat} (term : Term n) :
    (encodeTerm term).length = termWireSize term := by
  cases term <;> simp [encodeTerm, termWireSize] <;> omega

private theorem encodeTerms_length {n : Nat} (terms : List (Term n)) :
    (encodeTerms terms).length = (terms.map termWireSize).sum := by
  induction terms with
  | nil => rfl
  | cons term terms ih => simp [encodeTerms, encodeTerm_length, ih]

@[simp] theorem encodeInequality_length {n : Nat}
    (inequality : Inequality n) :
    (encodeInequality inequality).length = inequalityWireSize inequality := by
  simp [encodeInequality, inequalityWireSize, encodeTerms_length]
  omega

private theorem encodeInequalities_length {n : Nat}
    (inequalities : List (Inequality n)) :
    (encodeInequalities inequalities).length =
      (inequalities.map inequalityWireSize).sum := by
  induction inequalities with
  | nil => rfl
  | cons inequality inequalities ih =>
      simp [encodeInequalities, encodeInequality_length, ih]

@[simp] theorem encodeFPILP_length {n : Nat} (problem : FPILP n) :
    (encodeFPILP problem).length = fpilpWireSize problem := by
  simp [encodeFPILP, fpilpWireSize, encodeInequalities_length]
  omega

private theorem sum_map_le_mul {α : Type} (items : List α) (cost : α → Nat)
    (bound : Nat) (h : ∀ item ∈ items, cost item ≤ bound) :
    (items.map cost).sum ≤ items.length * bound := by
  induction items with
  | nil => simp
  | cons item items ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hhead := h item (by simp)
      have htail := ih (fun x hx => h x (by simp [hx]))
      simpa [Nat.succ_mul, Nat.add_comm] using Nat.add_le_add hhead htail

@[simp] theorem normalizeClause_length (formula : SAT.CNF)
    (clause : SAT.Clause) (hc : clause ∈ formula) :
    (normalizeClause formula clause hc).length = clause.length := by
  simp [normalizeClause]

@[simp] theorem normalize_length (formula : SAT.CNF) :
    (normalize formula).length = formula.length := by
  simp [normalize]

private theorem termWireSize_le {n : Nat} (term : Term n) :
    termWireSize term ≤ 2 * n + 2 := by
  cases term with
  | var index | oneMinus index =>
      simp only [termWireSize]
      have h := length_encodeNat_le index.val
      omega

private theorem inequalityWireSize_le {n : Nat} (q : Inequality n)
    (width : Nat) (hlhs : q.lhs.length ≤ width)
    (hrhs : (encodeInt q.rhs).length ≤ 4) :
    inequalityWireSize q ≤ (2 * n + 4) * width + 5 := by
  unfold inequalityWireSize
  have hheader := length_encodeNat_le q.lhs.length
  have hterms := sum_map_le_mul q.lhs termWireSize (2 * n + 2)
    (fun term _ => termWireSize_le term)
  have hprod : q.lhs.length * (2 * n + 4) ≤ width * (2 * n + 4) :=
    Nat.mul_le_mul_right (2 * n + 4) hlhs
  calc
    (encodeNat q.lhs.length).length +
          (q.lhs.map termWireSize).sum + (encodeInt q.rhs).length
        ≤ (2 * q.lhs.length + 1) +
          q.lhs.length * (2 * n + 2) + 4 := by omega
    _ = q.lhs.length * (2 * n + 4) + 5 := by ring
    _ ≤ width * (2 * n + 4) + 5 :=
      Nat.add_le_add_right hprod 5
    _ = (2 * n + 4) * width + 5 := by
      simp [Nat.mul_comm]

def coefficientCharge {n : Nat} (problem : FPILP n) : Nat :=
  (problem.constraints.map fun inequality =>
    inequality.rhs.natAbs + 1).sum

def indexCharge (formula : SAT.CNF) : Nat :=
  SATIndexCost formula

def sourceLiteralCount (formula : SAT.CNF) : Nat :=
  (formula.map List.length).sum

theorem variableCount_le_literalCount (formula : SAT.CNF) :
    variableCount formula ≤ sourceLiteralCount formula := by
  unfold variableCount vars
  rw [Finset.length_sort]
  apply (List.toFinset_card_le (occurringVariables formula)).trans_eq
  simp [occurringVariables, sourceLiteralCount, List.length_flatMap]

theorem literalCount_le_satSize (formula : SAT.CNF) :
    sourceLiteralCount formula ≤ SAT.size formula := by
  simp [sourceLiteralCount, SAT.size]

theorem variableCount_le_satWire (formula : SAT.CNF) :
    variableCount formula ≤ (encodeSATCNF formula).length :=
  (variableCount_le_literalCount formula).trans
    ((literalCount_le_satSize formula).trans (encodeSATCNF_size_ge formula))

private theorem clause_length_le_satWire (formula : SAT.CNF)
    (clause : SAT.Clause) (hc : clause ∈ formula) :
    clause.length ≤ (encodeSATCNF formula).length := by
  have hmem : clause.length ∈ formula.map List.length :=
    List.mem_map.mpr ⟨clause, hc, rfl⟩
  have hsum : clause.length ≤ (formula.map List.length).sum :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ hmem
  exact hsum.trans ((literalCount_le_satSize formula).trans
    (encodeSATCNF_size_ge formula))

private theorem reduced_constraint_shape (formula : SAT.CNF)
    (q : Inequality (variableCount formula))
    (hq : q ∈ (reduceFormula formula).constraints) :
    q.lhs.length ≤ (encodeSATCNF formula).length ∧
      (encodeInt q.rhs).length ≤ 4 := by
  simp only [reduceFormula, satToFPILP, List.mem_append, List.mem_map] at hq
  rcases hq with hbound | ⟨clause, hclause, rfl⟩
  · simp only [bounds, List.mem_flatMap] at hbound
    obtain ⟨index, -, hi⟩ := hbound
    simp only [List.mem_cons] at hi
    rcases hi with rfl | hi
    · constructor
      · have hs : 1 ≤ SAT.size formula := by
          unfold SAT.size
          omega
        exact hs.trans (encodeSATCNF_size_ge formula)
      · change (encodeInt 0).length ≤ 4
        decide
    · have heq : q = upperBound index := by simpa using hi
      subst q
      constructor
      · have hs : 1 ≤ SAT.size formula := by
          unfold SAT.size
          omega
        exact hs.trans (encodeSATCNF_size_ge formula)
      · change (encodeInt 0).length ≤ 4
        decide
  · constructor
    · simp only [clauseInequality, List.length_map]
      obtain ⟨⟨sourceClause, hc⟩, -, rfl⟩ :=
        List.mem_map.mp hclause
      simpa using clause_length_le_satWire formula sourceClause hc
    · simp [clauseInequality, encodeInt]

def sourceCharge (formula : SAT.CNF) : Nat :=
  (encodeSATCNF formula).length + sourceLiteralCount formula

def reductionWireBound (charge : Nat) : Nat :=
  32 * (charge + 1) ^ 3

theorem reductionWireBound_polynomial :
    IsPolynomial reductionWireBound := by
  let p : Nat → Nat := fun n => n + 1
  have hp : IsPolynomial p := IsPolynomial.add IsPolynomial.id
    (IsPolynomial.const 1)
  have hpoly :=
    IsPolynomial.mul (IsPolynomial.const 32) (hp.mul (hp.mul hp))
  convert hpoly using 1
  funext n
  simp [reductionWireBound, p, pow_three]

set_option maxHeartbeats 800000 in
private theorem encodeReducedFPILP_wire_le (formula : SAT.CNF) :
    (encodeFPILP (reduceFormula formula)).length ≤
      16 * ((encodeSATCNF formula).length + 1) ^ 3 := by
  let width := (encodeSATCNF formula).length
  let n := variableCount formula
  let constraints := (reduceFormula formula).constraints
  have hn : n ≤ width := variableCount_le_satWire formula
  have hformula : formula.length ≤ width := by
    have hs : formula.length ≤ SAT.size formula := by
      unfold SAT.size
      omega
    exact hs.trans (encodeSATCNF_size_ge formula)
  have hcount : constraints.length = 2 * n + formula.length := by
    simpa [constraints, n, reduceFormula, normalize_length] using
      satToFPILP_constraint_count (normalize formula)
  have hcountLe : constraints.length ≤ 3 * width := by omega
  have hsum :
      (constraints.map inequalityWireSize).sum ≤
        constraints.length * ((2 * n + 4) * width + 5) := by
    apply sum_map_le_mul
    intro q hq
    obtain ⟨hlhs, hrhs⟩ := reduced_constraint_shape formula q hq
    exact inequalityWireSize_le q width hlhs hrhs
  rw [encodeFPILP_length]
  unfold fpilpWireSize
  have hnHeader := length_encodeNat_le n
  have hcHeader := length_encodeNat_le constraints.length
  have hbodyBound :
      (2 * n + 4) * width + 5 ≤ (2 * width + 4) * width + 5 := by
    gcongr
  have hsum' :
      (constraints.map inequalityWireSize).sum ≤
        3 * width * ((2 * width + 4) * width + 5) :=
    hsum.trans (Nat.mul_le_mul hcountLe hbodyBound)
  change (encodeNat n).length + (encodeNat constraints.length).length +
    (constraints.map inequalityWireSize).sum ≤ _
  calc
    (encodeNat n).length + (encodeNat constraints.length).length +
        (constraints.map inequalityWireSize).sum
      ≤ (2 * width + 1) + (6 * width + 1) +
        3 * width * ((2 * width + 4) * width + 5) := by omega
    _ ≤ 16 * (width + 1) ^ 3 := by
      ring_nf
      omega

/--
The source charge is ordinary binary SAT wire length plus literal count.
Dense indices are bounded by the number of occurring literals, and all
coefficients emitted by the reduction are the constants zero and one.
-/
theorem encodedReduction_wire_le (formula : SAT.CNF) :
    (encodedReduction formula).length ≤
      reductionWireBound (sourceCharge formula) := by
  let width := (encodeSATCNF formula).length
  have htarget := encodeReducedFPILP_wire_le formula
  have hsourceHeader := length_encodeNat_le width
  rw [encodedReduction_length]
  unfold reductionWireBound sourceCharge
  change (encodeNat width).length + width +
      (encodeFPILP (reduceFormula formula)).length ≤
    32 * (width + sourceLiteralCount formula + 1) ^ 3
  have hsmall :
      (encodeNat width).length + width ≤ 16 * (width + 1) ^ 3 := by
    ring_nf
    omega
  have hmono :
      (width + 1) ^ 3 ≤
        (width + sourceLiteralCount formula + 1) ^ 3 := by
    apply Nat.pow_le_pow_left
    omega
  calc
    (encodeNat width).length + width +
        (encodeFPILP (reduceFormula formula)).length
      ≤ 16 * (width + 1) ^ 3 + 16 * (width + 1) ^ 3 :=
        Nat.add_le_add hsmall htarget
    _ = 32 * (width + 1) ^ 3 := by ring
    _ ≤ 32 * (width + sourceLiteralCount formula + 1) ^ 3 := by
      exact Nat.mul_le_mul_left 32 hmono

def binaryWireBound (width : Nat) : Nat := 256 * (width + 1) ^ 3

theorem binaryWireBound_polynomial : IsPolynomial binaryWireBound := by
  let p : Nat → Nat := fun n => n + 1
  have hp : IsPolynomial p := IsPolynomial.add IsPolynomial.id
    (IsPolynomial.const 1)
  have hpoly :=
    IsPolynomial.mul (IsPolynomial.const 256) (hp.mul (hp.mul hp))
  convert hpoly using 1
  funext n
  simp [binaryWireBound, p, pow_three]

/-- The dense reduction is polynomial in the canonical binary SAT wire alone. -/
theorem encodedReduction_binary_wire_le (formula : SAT.CNF) :
    (encodedReduction formula).length ≤
      binaryWireBound (encodeSATCNF formula).length := by
  let width := (encodeSATCNF formula).length
  have hlit : sourceLiteralCount formula ≤ width :=
    (literalCount_le_satSize formula).trans (encodeSATCNF_size_ge formula)
  have hbase : width + sourceLiteralCount formula + 1 ≤ 2 * (width + 1) := by
    omega
  have hpow := Nat.pow_le_pow_left hbase 3
  calc
    (encodedReduction formula).length
      ≤ reductionWireBound (sourceCharge formula) :=
        encodedReduction_wire_le formula
    _ ≤ 32 * (2 * (width + 1)) ^ 3 := by
      exact Nat.mul_le_mul_left 32 hpow
    _ = binaryWireBound width := by
      simp [binaryWireBound, pow_three]
      ring

theorem encodedReduction_left_inverse (formula : SAT.CNF) :
    inverseEncodedReduction (encodedReduction formula) = encodeSATCNF formula :=
  inverseEncodedReduction_apply formula

end TR1995.FPILPEncoded
