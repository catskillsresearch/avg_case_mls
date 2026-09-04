import AvgCaseMls.Section4.CookLevin.CNF
import AvgCaseMls.Section4.CookLevin.LocalCNF

/-!
# Serialization of the faithful SAT target

Clauses and formulas are length framed with the foundation natural codec.
The decoder consumes exactly one object and therefore supplies a
syntax-directed inverse for compiled bounded instances.
-/

namespace AvgCaseMls.Section4.CookLevin

open AvgCaseMls.Foundation

def encodeSATLiteral : SAT.Literal → Bitstring
  | .pos index => false :: encodeNat index
  | .neg index => true :: encodeNat index

def decodeSATLiteral? : Bitstring → Option (SAT.Literal × Bitstring)
  | false :: rest => do
      let (index, suffix) ← decodeNat? rest
      some (.pos index, suffix)
  | true :: rest => do
      let (index, suffix) ← decodeNat? rest
      some (.neg index, suffix)
  | [] => none

@[simp] theorem decodeSATLiteral?_suffix (literal : SAT.Literal)
    (rest : Bitstring) :
    decodeSATLiteral? (encodeSATLiteral literal ++ rest) =
      some (literal, rest) := by
  cases literal <;> simp [encodeSATLiteral, decodeSATLiteral?, decodeNat?_suffix]

def encodeSATLiterals : List SAT.Literal → Bitstring
  | [] => []
  | literal :: literals =>
      encodeSATLiteral literal ++ encodeSATLiterals literals

def decodeSATLiterals? : Nat → Bitstring →
    Option (List SAT.Literal × Bitstring)
  | 0, rest => some ([], rest)
  | count + 1, bits => do
      let (literal, rest) ← decodeSATLiteral? bits
      let (literals, suffix) ← decodeSATLiterals? count rest
      some (literal :: literals, suffix)

theorem decodeSATLiterals?_suffix (literals : List SAT.Literal)
    (rest : Bitstring) :
    decodeSATLiterals? literals.length
      (encodeSATLiterals literals ++ rest) = some (literals, rest) := by
  induction literals with
  | nil => rfl
  | cons literal literals ih =>
      simp [encodeSATLiterals, decodeSATLiterals?,
        decodeSATLiteral?_suffix, ih]

def encodeSATClause (clause : SAT.Clause) : Bitstring :=
  encodeNat clause.length ++ encodeSATLiterals clause

def decodeSATClause? (bits : Bitstring) :
    Option (SAT.Clause × Bitstring) := do
  let (count, rest) ← decodeNat? bits
  decodeSATLiterals? count rest

@[simp] theorem decodeSATClause?_suffix (clause : SAT.Clause)
    (rest : Bitstring) :
    decodeSATClause? (encodeSATClause clause ++ rest) =
      some (clause, rest) := by
  simp [encodeSATClause, decodeSATClause?, decodeNat?_suffix,
    decodeSATLiterals?_suffix]

def encodeSATClauses : SAT.CNF → Bitstring
  | [] => []
  | clause :: formula =>
      encodeSATClause clause ++ encodeSATClauses formula

def decodeSATClauses? : Nat → Bitstring → Option (SAT.CNF × Bitstring)
  | 0, rest => some ([], rest)
  | count + 1, bits => do
      let (clause, rest) ← decodeSATClause? bits
      let (formula, suffix) ← decodeSATClauses? count rest
      some (clause :: formula, suffix)

theorem decodeSATClauses?_suffix (formula : SAT.CNF) (rest : Bitstring) :
    decodeSATClauses? formula.length (encodeSATClauses formula ++ rest) =
      some (formula, rest) := by
  induction formula with
  | nil => rfl
  | cons clause formula ih =>
      simp [encodeSATClauses, decodeSATClauses?,
        decodeSATClause?_suffix, ih]

def encodeSATCNF (formula : SAT.CNF) : Bitstring :=
  encodeNat formula.length ++ encodeSATClauses formula

def decodeSATCNF? (bits : Bitstring) : Option SAT.CNF := do
  let (count, rest) ← decodeNat? bits
  let (formula, suffix) ← decodeSATClauses? count rest
  if suffix = [] then some formula else none

@[simp] theorem decodeSATCNF?_encode (formula : SAT.CNF) :
    decodeSATCNF? (encodeSATCNF formula) = some formula := by
  unfold encodeSATCNF decodeSATCNF?
  rw [decodeNat?_suffix]
  have hdecode :
      decodeSATClauses? formula.length (encodeSATClauses formula) =
        some (formula, []) := by
    simpa using decodeSATClauses?_suffix formula []
  simp [hdecode]

theorem encodeSATCNF_injective : Function.Injective encodeSATCNF := by
  intro first second h
  have := congrArg decodeSATCNF? h
  simpa using this

/-- The target is the standard language of serialized satisfiable CNFs. -/
def EncodedSAT : Set Bitstring :=
  { bits | ∃ formula,
      decodeSATCNF? bits = some formula ∧ SAT.Satisfiable formula }

def compileTraceDiagnosticSAT (inst : BoundedInstance) : Bitstring :=
  encodeSATCNF (traceDiagnosticCNF inst)

/-- Serialized output of the genuine local Cook--Levin compiler. -/
def compileLocalTableauSAT (inst : BoundedInstance) : Bitstring :=
  encodeSATCNF (localTableauCNF inst)

def malformedLocalCNF (source : Bitstring) : SAT.CNF :=
  sourceBlockBits source ++ [[]]

def compileEncodedLocalCNF (source : Bitstring) : SAT.CNF :=
  match decodeBoundedInstance? source with
  | some inst => localTableauCNFWithSource source inst
  | none => malformedLocalCNF source

def compileEncodedLocalSAT (source : Bitstring) : Bitstring :=
  encodeSATCNF (compileEncodedLocalCNF source)

def inverseEncodedLocalSAT (bits : Bitstring) : Bitstring :=
  match decodeSATCNF? bits with
  | some formula => recoverLocalSource formula
  | none => []

@[simp] theorem inverseEncodedLocalSAT_compile (source : Bitstring) :
    inverseEncodedLocalSAT (compileEncodedLocalSAT source) = source := by
  change (match decodeSATCNF? (encodeSATCNF (compileEncodedLocalCNF source)) with
    | some formula => recoverLocalSource formula
    | none => []) = source
  rw [decodeSATCNF?_encode]
  change recoverLocalSource (compileEncodedLocalCNF source) = source
  unfold compileEncodedLocalCNF
  split
  · simp
  · simp [malformedLocalCNF]

theorem compileEncodedLocalSAT_injective :
    Function.Injective compileEncodedLocalSAT := by
  intro first second heq
  have hinverse := congrArg inverseEncodedLocalSAT heq
  simpa using hinverse

theorem malformedLocalCNF_unsatisfiable (source : Bitstring) :
    ¬ SAT.Satisfiable (malformedLocalCNF source) := by
  rintro ⟨assignment, hsatisfies⟩
  have hempty := hsatisfies [] (by simp [malformedLocalCNF])
  exact SAT.evalClause_nil assignment hempty

theorem compileEncodedLocalSAT_mem_encodedSAT_iff (source : Bitstring) :
    compileEncodedLocalSAT source ∈ EncodedSAT ↔
      SAT.Satisfiable (compileEncodedLocalCNF source) := by
  simp [compileEncodedLocalSAT, EncodedSAT]

theorem compileEncodedLocalSAT_mem_iff (source : Bitstring) :
    compileEncodedLocalSAT source ∈ EncodedSAT ↔
      source ∈ EncodedBoundedAcceptance := by
  rw [compileEncodedLocalSAT_mem_encodedSAT_iff]
  unfold compileEncodedLocalCNF EncodedBoundedAcceptance
  split <;> rename_i hdecode
  · rename_i inst
    rw [localTableauCNFWithSource_satisfiable_iff_accepts]
    constructor
    · intro haccepts
      exact ⟨inst, hdecode, haccepts⟩
    · rintro ⟨other, hother, haccepts⟩
      rw [hdecode] at hother
      cases hother
      exact haccepts
  · constructor
    · intro hsatisfies
      exact (malformedLocalCNF_unsatisfiable source hsatisfies).elim
    · rintro ⟨inst, hinst, _⟩
      rw [hdecode] at hinst
      contradiction

theorem compileLocalTableauSAT_mem_iff (inst : BoundedInstance) :
    compileLocalTableauSAT inst ∈ EncodedSAT ↔
      AcceptsWithin inst.machine inst.input inst.time := by
  constructor
  · rintro ⟨formula, hdecode, hsatisfiable⟩
    rw [compileLocalTableauSAT, decodeSATCNF?_encode] at hdecode
    cases hdecode
    exact (localTableauCNF_satisfiable_iff_accepts inst).mp hsatisfiable
  · intro haccepts
    exact ⟨localTableauCNF inst, decodeSATCNF?_encode _,
      (localTableauCNF_satisfiable_iff_accepts inst).mpr haccepts⟩

def inverseLocalTableauSAT (bits : Bitstring) : Bitstring :=
  match decodeSATCNF? bits with
  | none => []
  | some formula => recoverLocalSource formula

@[simp] theorem inverseLocalTableauSAT_compile
    (inst : BoundedInstance) :
    inverseLocalTableauSAT (compileLocalTableauSAT inst) =
      encodeBoundedInstance inst := by
  simp [inverseLocalTableauSAT, compileLocalTableauSAT]

theorem compileLocalTableauSAT_injective :
    Function.Injective compileLocalTableauSAT := by
  intro first second h
  have hinverse := congrArg inverseLocalTableauSAT h
  simp only [inverseLocalTableauSAT_compile] at hinverse
  exact encodeBoundedInstance_injective hinverse

theorem compileTraceDiagnosticSAT_mem_iff (inst : BoundedInstance) :
    compileTraceDiagnosticSAT inst ∈ EncodedSAT ↔
      AcceptsWithin inst.machine inst.input inst.time := by
  constructor
  · rintro ⟨formula, hdecode, hsatisfiable⟩
    rw [compileTraceDiagnosticSAT, decodeSATCNF?_encode] at hdecode
    cases hdecode
    exact (traceDiagnosticCNF_satisfiable_iff inst).mp hsatisfiable
  · intro haccepts
    exact ⟨traceDiagnosticCNF inst, decodeSATCNF?_encode _,
      (traceDiagnosticCNF_satisfiable_iff inst).mpr haccepts⟩

/-- Decode the CNF, then read its first provenance clause. -/
def inverseSAT (bits : Bitstring) : Bitstring :=
  match decodeSATCNF? bits with
  | none => []
  | some formula => recoverCNFSource formula

@[simp] theorem inverseSAT_compileTraceDiagnosticSAT (inst : BoundedInstance) :
    inverseSAT (compileTraceDiagnosticSAT inst) = encodeBoundedInstance inst := by
  simp [inverseSAT, compileTraceDiagnosticSAT]

theorem compileTraceDiagnosticSAT_injective :
    Function.Injective compileTraceDiagnosticSAT := by
  intro first second h
  have hinverse := congrArg inverseSAT h
  simp only [inverseSAT_compileTraceDiagnosticSAT] at hinverse
  exact encodeBoundedInstance_injective hinverse

private theorem encodeSATLiteral_length_pos (literal : SAT.Literal) :
    1 ≤ (encodeSATLiteral literal).length := by
  cases literal <;> simp [encodeSATLiteral]

private theorem encodeSATLiterals_length_ge (literals : List SAT.Literal) :
    literals.length ≤ (encodeSATLiterals literals).length := by
  induction literals with
  | nil => simp [encodeSATLiterals]
  | cons literal literals ih =>
      simp [encodeSATLiterals]
      have hliteral := encodeSATLiteral_length_pos literal
      omega

private theorem encodeSATClause_length_ge (clause : SAT.Clause) :
    clause.length + 1 ≤ (encodeSATClause clause).length := by
  simp [encodeSATClause]
  have hliterals := encodeSATLiterals_length_ge clause
  have hheader : 1 ≤ (encodeNat clause.length).length := by
    simp [length_encodeNat]
  omega

private theorem encodeSATClauses_size_ge (formula : SAT.CNF) :
    formula.length + (formula.map List.length).sum ≤
      (encodeSATClauses formula).length := by
  induction formula with
  | nil => simp [encodeSATClauses]
  | cons clause formula ih =>
      simp [encodeSATClauses]
      have hclause := encodeSATClause_length_ge clause
      omega

theorem encodeSATCNF_size_ge (formula : SAT.CNF) :
    SAT.size formula ≤ (encodeSATCNF formula).length := by
  simp [SAT.size, encodeSATCNF]
  have hbody := encodeSATClauses_size_ge formula
  have hheader : 1 ≤ (encodeNat formula.length).length := by
    simp [length_encodeNat]
  omega

def literalIndex : SAT.Literal → Nat
  | .pos index | .neg index => index

def SATIndexCost (formula : SAT.CNF) : Nat :=
  ((formula.map fun clause =>
    (clause.map fun literal => literalIndex literal + 1).sum).sum)

@[simp] theorem SATIndexCost_nil : SATIndexCost [] = 0 := rfl

@[simp] theorem SATIndexCost_cons (clause : SAT.Clause) (formula : SAT.CNF) :
    SATIndexCost (clause :: formula) =
      (clause.map fun literal => literalIndex literal + 1).sum +
        SATIndexCost formula := by
  simp [SATIndexCost]

private theorem encodeSATLiteral_length_le (literal : SAT.Literal) :
    (encodeSATLiteral literal).length ≤
      2 * (literalIndex literal + 1) := by
  cases literal with
  | pos index =>
    simp only [encodeSATLiteral, literalIndex, List.length_cons]
    have h := length_encodeNat_le index
    omega
  | neg index =>
    simp only [encodeSATLiteral, literalIndex, List.length_cons]
    have h := length_encodeNat_le index
    omega

private theorem encodeSATLiterals_length_le (literals : List SAT.Literal) :
    (encodeSATLiterals literals).length ≤
      2 * (literals.map fun literal => literalIndex literal + 1).sum := by
  induction literals with
  | nil => simp [encodeSATLiterals]
  | cons literal literals ih =>
      rw [encodeSATLiterals, List.length_append, List.map_cons, List.sum_cons]
      have hliteral := encodeSATLiteral_length_le literal
      omega

private theorem encodeSATClause_length_le (clause : SAT.Clause) :
    (encodeSATClause clause).length ≤
      2 * clause.length + 1 +
      2 * (clause.map fun literal => literalIndex literal + 1).sum := by
  rw [encodeSATClause, List.length_append]
  have hheader := length_encodeNat_le clause.length
  have hbody := encodeSATLiterals_length_le clause
  omega

private theorem encodeSATClauses_length_le (formula : SAT.CNF) :
    (encodeSATClauses formula).length ≤
      2 * (formula.map List.length).sum + formula.length +
      2 * SATIndexCost formula := by
  induction formula with
  | nil => simp [encodeSATClauses, SATIndexCost]
  | cons clause formula ih =>
      rw [encodeSATClauses, List.length_append, List.map_cons,
        List.sum_cons, List.length_cons, SATIndexCost_cons]
      have hclause := encodeSATClause_length_le clause
      omega

/--
Serialization explicitly charges both syntax nodes and the binary natural
indices occurring in literals; no variable index is treated as unit cost.
-/
theorem encodeSATCNF_length_le (formula : SAT.CNF) :
    (encodeSATCNF formula).length ≤
      3 * SAT.size formula + 2 * SATIndexCost formula := by
  rw [encodeSATCNF, List.length_append]
  have hheader := length_encodeNat_le formula.length
  have hbody := encodeSATClauses_length_le formula
  simp only [SAT.size, SAT.foldr_add_eq_sum]
  omega

def localSATWireBound (structural indexCost : Nat) : Nat :=
  3 * localCNFSizeBound structural + 2 * indexCost

theorem localSATWireBound_polynomial_at_indexCost (indexCost : Nat) :
    IsPolynomial (fun n => localSATWireBound n indexCost) := by
  simpa [localSATWireBound] using
    IsPolynomial.add
      (IsPolynomial.mul (IsPolynomial.const 3)
        localCNFSizeBound_polynomial)
      (IsPolynomial.const (2 * indexCost))

/--
Concrete wire bound. `SATIndexCost` is the sum of the represented natural
indices plus one, so this theorem includes every variable-index bit emitted
by `encodeNat`, rather than charging literals as atomic symbols.
-/
theorem compileLocalTableauSAT_wire_le (inst : BoundedInstance) :
    (compileLocalTableauSAT inst).length ≤
      localSATWireBound (localCNFParameter inst)
        (SATIndexCost (localTableauCNF inst)) := by
  rw [compileLocalTableauSAT]
  exact (encodeSATCNF_length_le _).trans
    (Nat.add_le_add_right
      (Nat.mul_le_mul_left 3 (localTableauCNF_size_le inst)) _)

theorem compileLocalTableauSAT_honest (inst : BoundedInstance) :
    (encodeBoundedInstance inst).length ≤
      (compileLocalTableauSAT inst).length := by
  exact (localTableauCNF_honest inst).trans
    (by simpa [compileLocalTableauSAT] using
      encodeSATCNF_size_ge (localTableauCNF inst))

def encodedHonestyBound (n : Nat) : Nat := n

theorem encodedHonestyBound_polynomial :
    IsPolynomial encodedHonestyBound :=
  IsPolynomial.id

/-- The serialized SAT output is at least as long as its complete source. -/
theorem compileTraceDiagnosticSAT_honest (inst : BoundedInstance) :
    (encodeBoundedInstance inst).length ≤
      (compileTraceDiagnosticSAT inst).length := by
  exact (traceDiagnosticCNF_honest inst).trans
    (by simpa [compileTraceDiagnosticSAT] using
      encodeSATCNF_size_ge (traceDiagnosticCNF inst))

end AvgCaseMls.Section4.CookLevin
