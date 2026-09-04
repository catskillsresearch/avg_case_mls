import AvgCaseMls.MLSInReduction
import AvgCaseMls.Foundation.Codec

/-!
# COP90 bounded simple-prenex formulas

This is Definition 5 of Cantone--Omodeo--Policriti (1990).  A formula is a
conjunction of prefix clauses.  Each prefix is a list of bounded universal
quantifiers `∀ x ∈ y`; its matrix is a disjunction of equality or membership
literals.  Simplicity says that no bound variable of a prefix is also used as
one of that prefix's bounding variables.  `Bounded l` fixes the prefix length.
-/

namespace COP90

open AvgCaseMls.Foundation

inductive Atom where
  | eq : Nat → Nat → Atom
  | mem : Nat → Nat → Atom
  deriving DecidableEq, Repr

inductive Literal where
  | pos : Atom → Literal
  | neg : Atom → Literal
  deriving DecidableEq, Repr

structure PrefixClause where
  quantifiers : List (Nat × Nat)
  matrix : List Literal
  deriving DecidableEq, Repr

abbrev Formula := List PrefixClause

/-- COP90's maximum-nesting-level-one side condition. -/
def PrefixClause.Simple (clause : PrefixClause) : Prop :=
  ∀ bound domain, (bound, domain) ∈ clause.quantifiers →
    ∀ bound', (bound', bound) ∉ clause.quantifiers

def PrefixClause.Bounded (l : Nat) (clause : PrefixClause) : Prop :=
  clause.Simple ∧ clause.quantifiers.length ≤ l

def Bounded (l : Nat) (formula : Formula) : Prop :=
  ∀ clause ∈ formula, clause.Bounded l

def update (env : MLS.Env) (var : Nat) (value : MLS.ZFSet) : MLS.Env :=
  fun i => if i = var then value else env i

def Atom.Holds (env : MLS.Env) : Atom → Prop
  | .eq x y => env x = env y
  | .mem x y => MLS.ZFSet.mem (env x) (env y)

def Literal.Holds (env : MLS.Env) : Literal → Prop
  | .pos atom => atom.Holds env
  | .neg atom => ¬atom.Holds env

def Matrix.Holds (env : MLS.Env) (matrix : List Literal) : Prop :=
  ∃ literal ∈ matrix, literal.Holds env

def Prefix.Holds (env : MLS.Env) : List (Nat × Nat) → List Literal → Prop
  | [], matrix => Matrix.Holds env matrix
  | (bound, domain) :: qs, matrix =>
      ∀ value, MLS.ZFSet.mem value (env domain) →
        Prefix.Holds (update env bound value) qs matrix

def PrefixClause.Holds (env : MLS.Env) (clause : PrefixClause) : Prop :=
  Prefix.Holds env clause.quantifiers clause.matrix

def Holds (env : MLS.Env) (formula : Formula) : Prop :=
  ∀ clause ∈ formula, clause.Holds env

def Satisfiable (formula : Formula) : Prop :=
  ∃ env, Holds env formula

/-! ## Quantifier-free embedding of the Theorem 5.1 language -/

def ofSATLiteral : SAT.Literal → Literal
  | .pos i => .pos (.mem 0 (i + 1))
  | .neg i => .neg (.mem 0 (i + 1))

def ofSATClause (clause : SAT.Clause) : PrefixClause :=
  ⟨[], clause.map ofSATLiteral⟩

def ofSAT (formula : SAT.CNF) : Formula :=
  formula.map ofSATClause

@[simp] theorem ofSAT_bounded (l : Nat) (formula : SAT.CNF) :
    Bounded l (ofSAT formula) := by
  intro clause hclause
  obtain ⟨source, _, rfl⟩ := List.mem_map.mp hclause
  simp [PrefixClause.Bounded, PrefixClause.Simple, ofSATClause]

@[simp] theorem literal_holds_ofSATLiteral (env : MLS.Env)
    (literal : SAT.Literal) :
    Literal.Holds env (ofSATLiteral literal) ↔
      SAT.evalLiteral
        (fun i => MLS.ZFSet.mem (env 0) (env (i + 1))) literal := by
  cases literal <;> rfl

theorem clause_holds_ofSATClause (env : MLS.Env) (clause : SAT.Clause) :
    PrefixClause.Holds env (ofSATClause clause) ↔
      SAT.evalClause
        (fun i => MLS.ZFSet.mem (env 0) (env (i + 1))) clause := by
  simp [PrefixClause.Holds, Prefix.Holds, Matrix.Holds, ofSATClause,
    SAT.evalClause, literal_holds_ofSATLiteral]

theorem holds_ofSAT (env : MLS.Env) (formula : SAT.CNF) :
    Holds env (ofSAT formula) ↔
      SAT.evalCNF
        (fun i => MLS.ZFSet.mem (env 0) (env (i + 1))) formula := by
  constructor
  · intro h clause hclause
    exact (clause_holds_ofSATClause env clause).mp
      (h (ofSATClause clause) (List.mem_map.mpr ⟨clause, hclause, rfl⟩))
  · intro h clause hclause
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hclause
    exact (clause_holds_ofSATClause env source).mpr (h source hsource)

theorem ofSAT_satisfiable_iff (formula : SAT.CNF) :
    Satisfiable (ofSAT formula) ↔ SAT.Satisfiable formula := by
  constructor
  · rintro ⟨env, henv⟩
    exact ⟨fun i => MLS.ZFSet.mem (env 0) (env (i + 1)),
      (holds_ofSAT env formula).mp henv⟩
  · rintro ⟨assignment, hassignment⟩
    refine ⟨MLSInReduction.envOfAssignment assignment, ?_⟩
    rw [holds_ofSAT]
    simpa only [MLSInReduction.envOfAssignment_mem] using hassignment

/--
The quantifier-free COP90 embedding and the `MLS_in` substitution have exactly
the same satisfiability behavior.
-/
theorem ofSAT_satisfiable_iff_MLSIn (formula : SAT.CNF) :
    Satisfiable (ofSAT formula) ↔
      MLSInReduction.MLSSatisfiable (MLSInReduction.toMLS formula) := by
  rw [ofSAT_satisfiable_iff, MLSInReduction.satisfiable_iff]

/-! ## Binary codec -/

def encodeAtom : Atom → Bitstring
  | .eq x y => false :: encodeNat x ++ encodeNat y
  | .mem x y => true :: encodeNat x ++ encodeNat y

def decodeAtom? : Bitstring → Option (Atom × Bitstring)
  | false :: bits => do
      let (x, bits) ← decodeNat? bits
      let (y, rest) ← decodeNat? bits
      some (.eq x y, rest)
  | true :: bits => do
      let (x, bits) ← decodeNat? bits
      let (y, rest) ← decodeNat? bits
      some (.mem x y, rest)
  | [] => none

@[simp] theorem decodeAtom?_suffix (atom : Atom) (rest : Bitstring) :
    decodeAtom? (encodeAtom atom ++ rest) = some (atom, rest) := by
  cases atom <;> simp [encodeAtom, decodeAtom?, decodeNat?_suffix,
    List.append_assoc]

def encodeLiteral : Literal → Bitstring
  | .pos atom => false :: encodeAtom atom
  | .neg atom => true :: encodeAtom atom

def decodeLiteral? : Bitstring → Option (Literal × Bitstring)
  | false :: bits => do
      let (atom, rest) ← decodeAtom? bits
      some (.pos atom, rest)
  | true :: bits => do
      let (atom, rest) ← decodeAtom? bits
      some (.neg atom, rest)
  | [] => none

@[simp] theorem decodeLiteral?_suffix (literal : Literal) (rest : Bitstring) :
    decodeLiteral? (encodeLiteral literal ++ rest) = some (literal, rest) := by
  cases literal <;> simp [encodeLiteral, decodeLiteral?, decodeAtom?_suffix]

def encodeLiterals : List Literal → Bitstring
  | [] => []
  | literal :: literals => encodeLiteral literal ++ encodeLiterals literals

def decodeLiterals? : Nat → Bitstring → Option (List Literal × Bitstring)
  | 0, rest => some ([], rest)
  | count + 1, bits => do
      let (literal, bits) ← decodeLiteral? bits
      let (literals, rest) ← decodeLiterals? count bits
      some (literal :: literals, rest)

@[simp] theorem decodeLiterals?_suffix (literals : List Literal)
    (rest : Bitstring) :
    decodeLiterals? literals.length (encodeLiterals literals ++ rest) =
      some (literals, rest) := by
  induction literals with
  | nil => rfl
  | cons literal literals ih =>
      simp [encodeLiterals, decodeLiterals?, decodeLiteral?_suffix, ih]

def encodePrefix : List (Nat × Nat) → Bitstring
  | [] => []
  | (bound, domain) :: qs =>
      encodeNat bound ++ encodeNat domain ++ encodePrefix qs

def decodePrefix? : Nat → Bitstring → Option (List (Nat × Nat) × Bitstring)
  | 0, rest => some ([], rest)
  | count + 1, bits => do
      let (bound, bits) ← decodeNat? bits
      let (domain, bits) ← decodeNat? bits
      let (qs, rest) ← decodePrefix? count bits
      some ((bound, domain) :: qs, rest)

@[simp] theorem decodePrefix?_suffix (qs : List (Nat × Nat))
    (rest : Bitstring) :
    decodePrefix? qs.length (encodePrefix qs ++ rest) =
      some (qs, rest) := by
  induction qs with
  | nil => rfl
  | cons pair qs ih =>
      rcases pair with ⟨bound, domain⟩
      simp [encodePrefix, decodePrefix?, decodeNat?_suffix, ih,
        List.append_assoc]

def encodePrefixClause (clause : PrefixClause) : Bitstring :=
  encodeNat clause.quantifiers.length ++ encodePrefix clause.quantifiers ++
    encodeNat clause.matrix.length ++ encodeLiterals clause.matrix

def decodePrefixClause? (bits : Bitstring) :
    Option (PrefixClause × Bitstring) := do
  let (prefixCount, bits) ← decodeNat? bits
  let (qs, bits) ← decodePrefix? prefixCount bits
  let (matrixCount, bits) ← decodeNat? bits
  let (matrix, rest) ← decodeLiterals? matrixCount bits
  some (⟨qs, matrix⟩, rest)

@[simp] theorem decodePrefixClause?_suffix (clause : PrefixClause)
    (rest : Bitstring) :
    decodePrefixClause? (encodePrefixClause clause ++ rest) =
      some (clause, rest) := by
  cases clause with
  | mk qs matrix =>
      simp [encodePrefixClause, decodePrefixClause?, decodeNat?_suffix,
        decodePrefix?_suffix, decodeLiterals?_suffix, List.append_assoc]

def encodeClauses : Formula → Bitstring
  | [] => []
  | clause :: clauses => encodePrefixClause clause ++ encodeClauses clauses

def decodeClauses? : Nat → Bitstring → Option (Formula × Bitstring)
  | 0, rest => some ([], rest)
  | count + 1, bits => do
      let (clause, bits) ← decodePrefixClause? bits
      let (clauses, rest) ← decodeClauses? count bits
      some (clause :: clauses, rest)

@[simp] theorem decodeClauses?_suffix (formula : Formula) (rest : Bitstring) :
    decodeClauses? formula.length (encodeClauses formula ++ rest) =
      some (formula, rest) := by
  induction formula with
  | nil => rfl
  | cons clause formula ih =>
      simp [encodeClauses, decodeClauses?, decodePrefixClause?_suffix, ih]

def encodeFormula (formula : Formula) : Bitstring :=
  encodeNat formula.length ++ encodeClauses formula

def decodeFormula? (bits : Bitstring) : Option Formula := do
  let (count, bits) ← decodeNat? bits
  let (formula, rest) ← decodeClauses? count bits
  if rest = [] then some formula else none

@[simp] theorem decodeFormula?_encode (formula : Formula) :
    decodeFormula? (encodeFormula formula) = some formula := by
  have h := decodeClauses?_suffix formula []
  simp only [List.append_nil] at h
  simp [decodeFormula?, encodeFormula, decodeNat?_suffix, h]

theorem encodeFormula_injective : Function.Injective encodeFormula := by
  intro first second h
  have := congrArg decodeFormula? h
  simpa using this

def EncodedSatisfiability (l : Nat) : Set Bitstring :=
  {bits | ∃ formula, decodeFormula? bits = some formula ∧
    Bounded l formula ∧ Satisfiable formula}

@[simp] theorem encode_mem_encodedSatisfiability (l : Nat) (formula : Formula)
    (hbounded : Bounded l formula) :
    encodeFormula formula ∈ EncodedSatisfiability l ↔ Satisfiable formula := by
  constructor
  · rintro ⟨decoded, hdecode, _, hsatisfiable⟩
    rw [decodeFormula?_encode] at hdecode
    cases hdecode
    exact hsatisfiable
  · exact fun h => ⟨formula, decodeFormula?_encode formula, hbounded, h⟩

/-! ## Wire accounting for the quantifier-free embedding -/

private def satLiteralWire : SAT.Literal → Nat
  | .pos i | .neg i => 1 + (encodeNat i).length

private theorem encodeNat_le_succ (n : Nat) :
    (encodeNat n).length ≤ (encodeNat (n + 1)).length := by
  rw [length_encodeNat, length_encodeNat]
  simp only [Nat.size_eq_bits_len]
  have hs : Nat.size n ≤ Nat.size (n + 1) := by
    rw [Nat.size_le]
    exact (Nat.lt_succ_self n).trans (Nat.lt_size_self (n + 1))
  omega

private theorem encodeNat_succ_le (n : Nat) :
    (encodeNat (n + 1)).length ≤ (encodeNat n).length + 2 := by
  rw [length_encodeNat, length_encodeNat]
  simp only [Nat.size_eq_bits_len]
  have hs : Nat.size (n + 1) ≤ Nat.size n + 1 := by
    rw [Nat.size_le]
    have hn : n + 1 ≤ 2 ^ Nat.size n :=
      Nat.succ_le_iff.mpr (Nat.lt_size_self n)
    calc
      n + 1 ≤ 2 ^ Nat.size n := hn
      _ < 2 ^ (Nat.size n + 1) := by
        rw [pow_succ]
        have hp : 0 < 2 ^ Nat.size n := pow_pos (by omega) _
        omega
  omega

private theorem encodeSATLiteral_length (literal : SAT.Literal) :
    (AvgCaseMls.Section4.CookLevin.encodeSATLiteral literal).length =
      satLiteralWire literal := by
  cases literal <;>
    simp [AvgCaseMls.Section4.CookLevin.encodeSATLiteral, satLiteralWire] <;>
    omega

private theorem encodeSATLiterals_length (clause : SAT.Clause) :
    (AvgCaseMls.Section4.CookLevin.encodeSATLiterals clause).length =
      (clause.map satLiteralWire).sum := by
  induction clause with
  | nil => rfl
  | cons literal clause ih =>
      simp [AvgCaseMls.Section4.CookLevin.encodeSATLiterals,
        encodeSATLiteral_length, ih]

private theorem ofSATLiteral_wire_ge (literal : SAT.Literal) :
    satLiteralWire literal ≤ (encodeLiteral (ofSATLiteral literal)).length := by
  cases literal with
  | pos i | neg i =>
      have h := encodeNat_le_succ i
      simp [satLiteralWire, ofSATLiteral, encodeLiteral, encodeAtom] at h ⊢
      omega

private theorem ofSATLiteral_wire_le (literal : SAT.Literal) :
    (encodeLiteral (ofSATLiteral literal)).length ≤ 5 * satLiteralWire literal := by
  cases literal with
  | pos i | neg i =>
      have h := encodeNat_succ_le i
      have hp : 0 < (encodeNat i).length := by rw [length_encodeNat]; omega
      simp [satLiteralWire, ofSATLiteral, encodeLiteral, encodeAtom] at h hp ⊢
      omega

private theorem encodeLiterals_ofSAT_honest (clause : SAT.Clause) :
    (clause.map satLiteralWire).sum ≤
      (encodeLiterals (clause.map ofSATLiteral)).length := by
  induction clause with
  | nil => rfl
  | cons literal clause ih =>
      simp only [List.map_cons, List.sum_cons, encodeLiterals,
        List.length_append]
      exact Nat.add_le_add (ofSATLiteral_wire_ge literal) ih

private theorem encodeLiterals_ofSAT_le (clause : SAT.Clause) :
    (encodeLiterals (clause.map ofSATLiteral)).length ≤
      5 * (clause.map satLiteralWire).sum := by
  induction clause with
  | nil => simp [encodeLiterals]
  | cons literal clause ih =>
      simp only [List.map_cons, List.sum_cons, encodeLiterals,
        List.length_append]
      have hl := ofSATLiteral_wire_le literal
      omega

theorem encodePrefixClause_ofSAT_honest (clause : SAT.Clause) :
    (AvgCaseMls.Section4.CookLevin.encodeSATClause clause).length ≤
      (encodePrefixClause (ofSATClause clause)).length := by
  have hbody := encodeLiterals_ofSAT_honest clause
  simp [AvgCaseMls.Section4.CookLevin.encodeSATClause,
    encodeSATLiterals_length, encodePrefixClause, ofSATClause,
    encodePrefix, length_encodeNat] at hbody ⊢
  omega

theorem encodePrefixClause_ofSAT_le (clause : SAT.Clause) :
    (encodePrefixClause (ofSATClause clause)).length ≤
      6 * (AvgCaseMls.Section4.CookLevin.encodeSATClause clause).length := by
  have hbody := encodeLiterals_ofSAT_le clause
  have hheader : 0 < (encodeNat clause.length).length := by
    rw [length_encodeNat]
    omega
  simp [AvgCaseMls.Section4.CookLevin.encodeSATClause,
    encodeSATLiterals_length, encodePrefixClause, ofSATClause,
    encodePrefix, length_encodeNat] at hbody ⊢
  omega

private theorem encodeClauses_ofSAT_honest (formula : SAT.CNF) :
    (AvgCaseMls.Section4.CookLevin.encodeSATClauses formula).length ≤
      (encodeClauses (ofSAT formula)).length := by
  induction formula with
  | nil => rfl
  | cons clause formula ih =>
      have hc := encodePrefixClause_ofSAT_honest clause
      simp [AvgCaseMls.Section4.CookLevin.encodeSATClauses,
        encodeClauses, ofSAT] at ih ⊢
      omega

private theorem encodeClauses_ofSAT_le (formula : SAT.CNF) :
    (encodeClauses (ofSAT formula)).length ≤
      6 * (AvgCaseMls.Section4.CookLevin.encodeSATClauses formula).length := by
  induction formula with
  | nil => rfl
  | cons clause formula ih =>
      have hc := encodePrefixClause_ofSAT_le clause
      simp [AvgCaseMls.Section4.CookLevin.encodeSATClauses,
        encodeClauses, ofSAT] at ih ⊢
      omega

def encodedSATEmbedding (formula : SAT.CNF) : Bitstring :=
  encodeFormula (ofSAT formula)

theorem encodedSATEmbedding_honest (formula : SAT.CNF) :
    (AvgCaseMls.Section4.CookLevin.encodeSATCNF formula).length ≤
      (encodedSATEmbedding formula).length := by
  have hbody := encodeClauses_ofSAT_honest formula
  simpa [AvgCaseMls.Section4.CookLevin.encodeSATCNF,
    encodedSATEmbedding, encodeFormula, ofSAT] using
      Nat.add_le_add_left hbody (encodeNat formula.length).length

def embeddingWireBound (n : Nat) : Nat := 6 * n

theorem embeddingWireBound_polynomial :
    IsPolynomial embeddingWireBound := by
  apply IsPolynomial.bounded 6 1
  intro n
  simp [embeddingWireBound]

theorem encodedSATEmbedding_wire_le (formula : SAT.CNF) :
    (encodedSATEmbedding formula).length ≤
      embeddingWireBound
        (AvgCaseMls.Section4.CookLevin.encodeSATCNF formula).length := by
  have hbody := encodeClauses_ofSAT_le formula
  have hheader : (encodeNat formula.length).length ≤
      6 * (encodeNat formula.length).length := by omega
  simp [encodedSATEmbedding, encodeFormula, ofSAT,
    embeddingWireBound, AvgCaseMls.Section4.CookLevin.encodeSATCNF] at hbody ⊢
  omega

/-! ## Finite model-graph certificates

The checker below is fully executable.  A certificate names a finite node
set, gives one node for every syntactic variable occurrence (the first
occurrence is used), and stores the membership graph row-major.
-/

def Atom.varsOf : Atom → List Nat
  | .eq x y | .mem x y => [x, y]

def Literal.varsOf : Literal → List Nat
  | .pos atom | .neg atom => atom.varsOf

def PrefixClause.varsOf (clause : PrefixClause) : List Nat :=
  clause.quantifiers.flatMap (fun q => [q.1, q.2]) ++
    clause.matrix.flatMap Literal.varsOf

def varsOf (formula : Formula) : List Nat :=
  formula.flatMap PrefixClause.varsOf

structure Certificate where
  nodeCount : Nat
  assignment : List Nat
  edges : List Bool
  deriving DecidableEq, Repr

def Certificate.edge (certificate : Certificate) (source target : Nat) : Bool :=
  (certificate.edges[source * certificate.nodeCount + target]?).getD false

def lookupAligned? : List Nat → List Nat → Nat → Option Nat
  | name :: names, value :: values, sought =>
      if name = sought then some value
      else lookupAligned? names values sought
  | _, _, _ => none

def lookupLocal? (locals : List (Nat × Nat)) (name : Nat) : Option Nat :=
  match locals.find? (fun pair => pair.1 = name) with
  | some pair => some pair.2
  | none => none

def lookupNode? (formula : Formula) (certificate : Certificate)
    (locals : List (Nat × Nat)) (name : Nat) : Option Nat :=
  match lookupLocal? locals name with
  | some value => some value
  | none => lookupAligned? (varsOf formula) certificate.assignment name

def checkAtom (formula : Formula) (certificate : Certificate)
    (locals : List (Nat × Nat)) : Atom → Bool
  | .eq x y =>
      match lookupNode? formula certificate locals x,
          lookupNode? formula certificate locals y with
      | some x, some y => x == y
      | _, _ => false
  | .mem x y =>
      match lookupNode? formula certificate locals x,
          lookupNode? formula certificate locals y with
      | some x, some y => certificate.edge x y
      | _, _ => false

def checkLiteral (formula : Formula) (certificate : Certificate)
    (locals : List (Nat × Nat)) : Literal → Bool
  | .pos atom => checkAtom formula certificate locals atom
  | .neg atom => !(checkAtom formula certificate locals atom)

def checkMatrix (formula : Formula) (certificate : Certificate)
    (locals : List (Nat × Nat)) (matrix : List Literal) : Bool :=
  matrix.any (checkLiteral formula certificate locals)

def checkPrefix (formula : Formula) (certificate : Certificate) :
    List (Nat × Nat) → List (Nat × Nat) → List Literal → Bool
  | [], locals, matrix => checkMatrix formula certificate locals matrix
  | (bound, domain) :: qs, locals, matrix =>
      match lookupNode? formula certificate locals domain with
      | none => false
      | some domainNode =>
          (List.range certificate.nodeCount).all fun value =>
            !certificate.edge value domainNode ||
              checkPrefix formula certificate qs
                ((bound, value) :: locals) matrix

def checkPrefixClause (formula : Formula) (certificate : Certificate)
    (clause : PrefixClause) : Bool :=
  checkPrefix formula certificate clause.quantifiers [] clause.matrix

def checkFormula (formula : Formula) (certificate : Certificate) : Bool :=
  formula.all (checkPrefixClause formula certificate)

def simpleCheck (clause : PrefixClause) : Bool :=
  decide (∀ pair ∈ clause.quantifiers, ∀ other ∈ clause.quantifiers,
    other.2 ≠ pair.1)

def boundedCheck (l : Nat) (formula : Formula) : Bool :=
  formula.all fun clause =>
    simpleCheck clause && decide (clause.quantifiers.length ≤ l)

def Certificate.valid (formula : Formula) (certificate : Certificate) : Bool :=
  decide (certificate.assignment.length = (varsOf formula).length) &&
  decide (certificate.edges.length =
    certificate.nodeCount * certificate.nodeCount) &&
  certificate.assignment.all (· < certificate.nodeCount) &&
  (List.range certificate.nodeCount).all fun source =>
    (List.range certificate.nodeCount).all fun target =>
      !certificate.edge source target || decide (source < target)

/-- Executable certificate checker for the fixed-prefix fragment. -/
def checkCertificate (l : Nat) (formula : Formula)
    (certificate : Certificate) : Bool :=
  boundedCheck l formula && certificate.valid formula &&
    checkFormula formula certificate

def FiniteAtomHolds (formula : Formula) (certificate : Certificate)
    (locals : List (Nat × Nat)) : Atom → Prop
  | .eq x y => ∃ nx ny,
      lookupNode? formula certificate locals x = some nx ∧
      lookupNode? formula certificate locals y = some ny ∧ nx = ny
  | .mem x y => ∃ nx ny,
      lookupNode? formula certificate locals x = some nx ∧
      lookupNode? formula certificate locals y = some ny ∧
      certificate.edge nx ny = true

def FiniteLiteralHolds (formula : Formula) (certificate : Certificate)
    (locals : List (Nat × Nat)) : Literal → Prop
  | .pos atom => FiniteAtomHolds formula certificate locals atom
  | .neg atom => ¬FiniteAtomHolds formula certificate locals atom

def FiniteMatrixHolds (formula : Formula) (certificate : Certificate)
    (locals : List (Nat × Nat)) (matrix : List Literal) : Prop :=
  ∃ literal ∈ matrix,
    FiniteLiteralHolds formula certificate locals literal

def FinitePrefixHolds (formula : Formula) (certificate : Certificate) :
    List (Nat × Nat) → List (Nat × Nat) → List Literal → Prop
  | [], locals, matrix =>
      FiniteMatrixHolds formula certificate locals matrix
  | (bound, domain) :: qs, locals, matrix =>
      ∃ domainNode,
        lookupNode? formula certificate locals domain = some domainNode ∧
        ∀ value < certificate.nodeCount,
          certificate.edge value domainNode = true →
            FinitePrefixHolds formula certificate qs
              ((bound, value) :: locals) matrix

def FiniteHolds (formula : Formula) (certificate : Certificate) : Prop :=
  ∀ clause ∈ formula,
    FinitePrefixHolds formula certificate clause.quantifiers [] clause.matrix

theorem checkAtom_eq_true_iff (formula : Formula) (certificate : Certificate)
    (locals : List (Nat × Nat)) (atom : Atom) :
    checkAtom formula certificate locals atom = true ↔
      FiniteAtomHolds formula certificate locals atom := by
  cases atom with
  | eq x y =>
      simp only [checkAtom, FiniteAtomHolds]
      cases hx : lookupNode? formula certificate locals x <;>
        cases hy : lookupNode? formula certificate locals y <;>
        simp [hx, hy]
      constructor <;> exact Eq.symm
  | mem x y =>
      simp only [checkAtom, FiniteAtomHolds]
      cases hx : lookupNode? formula certificate locals x <;>
        cases hy : lookupNode? formula certificate locals y <;>
        simp [hx, hy]

theorem checkLiteral_eq_true_iff (formula : Formula)
    (certificate : Certificate) (locals : List (Nat × Nat))
    (literal : Literal) :
    checkLiteral formula certificate locals literal = true ↔
      FiniteLiteralHolds formula certificate locals literal := by
  cases literal with
  | pos atom =>
      exact checkAtom_eq_true_iff formula certificate locals atom
  | neg atom =>
      change (!checkAtom formula certificate locals atom) = true ↔
        ¬FiniteAtomHolds formula certificate locals atom
      rw [Bool.not_eq_true']
      constructor
      · intro hfalse hatom
        have htrue :=
          (checkAtom_eq_true_iff formula certificate locals atom).mpr hatom
        rw [htrue] at hfalse
        contradiction
      · intro hnot
        apply Bool.eq_false_iff.mpr
        intro htrue
        exact hnot
          ((checkAtom_eq_true_iff formula certificate locals atom).mp htrue)

theorem checkMatrix_eq_true_iff (formula : Formula)
    (certificate : Certificate) (locals : List (Nat × Nat))
    (matrix : List Literal) :
    checkMatrix formula certificate locals matrix = true ↔
      FiniteMatrixHolds formula certificate locals matrix := by
  simp [checkMatrix, FiniteMatrixHolds, List.any_eq_true,
    checkLiteral_eq_true_iff]

theorem checkPrefix_eq_true_iff (formula : Formula)
    (certificate : Certificate) (qs locals : List (Nat × Nat))
    (matrix : List Literal) :
    checkPrefix formula certificate qs locals matrix = true ↔
      FinitePrefixHolds formula certificate qs locals matrix := by
  induction qs generalizing locals with
  | nil => exact checkMatrix_eq_true_iff formula certificate locals matrix
  | cons pair qs ih =>
      rcases pair with ⟨bound, domain⟩
      cases hdomain :
          lookupNode? formula certificate locals domain with
      | none => simp [checkPrefix, FinitePrefixHolds, hdomain]
      | some domainNode =>
        simp only [checkPrefix, FinitePrefixHolds, hdomain, List.all_eq_true,
          List.mem_range]
        constructor
        · intro h
          refine ⟨domainNode, rfl, ?_⟩
          intro value hvalue hedge
          have hv := h value hvalue
          simp [hedge] at hv
          exact (ih ((bound, value) :: locals)).mp hv
        · rintro ⟨node, hnode, h⟩
          cases hnode
          intro value hvalue
          by_cases hedge : certificate.edge value domainNode = true
          · simp [hedge, (ih ((bound, value) :: locals)).mpr
              (h value hvalue hedge)]
          · have hedgeFalse :
                certificate.edge value domainNode = false :=
              Bool.eq_false_iff.mpr hedge
            simp [hedgeFalse]

theorem checkFormula_eq_true_iff (formula : Formula)
    (certificate : Certificate) :
    checkFormula formula certificate = true ↔ FiniteHolds formula certificate := by
  simp [checkFormula, FiniteHolds, List.all_eq_true,
    checkPrefixClause, checkPrefix_eq_true_iff]

theorem simpleCheck_eq_true_iff (clause : PrefixClause) :
    simpleCheck clause = true ↔ clause.Simple := by
  rw [simpleCheck, decide_eq_true_iff]
  constructor
  · intro h bound domain hpair bound' hother
    exact h (bound, domain) hpair (bound', bound) hother (by simp)
  · intro h pair hpair other hother heq
    rcases pair with ⟨bound, domain⟩
    rcases other with ⟨bound', otherDomain⟩
    change otherDomain = bound at heq
    subst otherDomain
    exact h bound domain hpair bound' hother

theorem boundedCheck_eq_true_iff (l : Nat) (formula : Formula) :
    boundedCheck l formula = true ↔ Bounded l formula := by
  simp [boundedCheck, Bounded, PrefixClause.Bounded, List.all_eq_true,
    Bool.and_eq_true, simpleCheck_eq_true_iff]

theorem checkCertificate_eq_true_iff (l : Nat) (formula : Formula)
    (certificate : Certificate) :
    checkCertificate l formula certificate = true ↔
      Bounded l formula ∧ certificate.valid formula = true ∧
        FiniteHolds formula certificate := by
  rw [checkCertificate, Bool.and_eq_true, Bool.and_eq_true,
    boundedCheck_eq_true_iff, checkFormula_eq_true_iff]
  tauto

def FiniteSatisfiable (l : Nat) (formula : Formula) : Prop :=
  Bounded l formula ∧ ∃ certificate,
    certificate.valid formula = true ∧ FiniteHolds formula certificate

/-- Exact finite certificate characterization accepted by the executable checker. -/
theorem finiteSatisfiable_iff_certificate (l : Nat) (formula : Formula) :
    FiniteSatisfiable l formula ↔
      ∃ certificate, checkCertificate l formula certificate = true := by
  simp [FiniteSatisfiable, checkCertificate_eq_true_iff]

/-! ### Certificate and checker cost counts -/

def Certificate.cellCount (certificate : Certificate) : Nat :=
  1 + certificate.assignment.length + certificate.edges.length

def encodeNats : List Nat → Bitstring
  | [] => []
  | value :: values => encodeNat value ++ encodeNats values

def decodeNats? : Nat → Bitstring → Option (List Nat × Bitstring)
  | 0, rest => some ([], rest)
  | count + 1, bits => do
      let (value, bits) ← decodeNat? bits
      let (values, rest) ← decodeNats? count bits
      some (value :: values, rest)

@[simp] theorem decodeNats?_suffix (values : List Nat) (rest : Bitstring) :
    decodeNats? values.length (encodeNats values ++ rest) =
      some (values, rest) := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp [encodeNats, decodeNats?, decodeNat?_suffix, ih]

def encodeCertificate (certificate : Certificate) : Bitstring :=
  encodeNat certificate.nodeCount ++
    encodeNat certificate.assignment.length ++
    encodeNats certificate.assignment ++
    encodeNat certificate.edges.length ++ certificate.edges

def decodeCertificate? (bits : Bitstring) : Option Certificate := do
  let (nodeCount, bits) ← decodeNat? bits
  let (assignmentCount, bits) ← decodeNat? bits
  let (assignment, bits) ← decodeNats? assignmentCount bits
  let (edgeCount, bits) ← decodeNat? bits
  if edgeCount ≤ bits.length then
    let edges := bits.take edgeCount
    let rest := bits.drop edgeCount
    if rest = [] then some ⟨nodeCount, assignment, edges⟩ else none
  else none

@[simp] theorem decodeCertificate?_encode (certificate : Certificate) :
    decodeCertificate? (encodeCertificate certificate) = some certificate := by
  unfold decodeCertificate? encodeCertificate
  simp [decodeNat?_suffix, decodeNats?_suffix]

theorem encodeCertificate_injective : Function.Injective encodeCertificate := by
  intro first second h
  have := congrArg decodeCertificate? h
  simpa using this

private theorem encodeNats_length (values : List Nat) :
    (encodeNats values).length =
      (values.map fun value => (encodeNat value).length).sum := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [encodeNats, ih]

def certificateWireBound (inputLength : Nat) : Nat :=
  20 * (inputLength + 1) ^ 4

theorem certificateWireBound_polynomial :
    IsPolynomial certificateWireBound := by
  apply IsPolynomial.bounded 320 4
  intro n
  unfold certificateWireBound
  cases n with
  | zero => norm_num
  | succ n =>
      have hn : 1 ≤ n + 1 := by omega
      nlinarith [sq_nonneg (n : ℤ), sq_nonneg ((n : ℤ) ^ 2)]

def certificateNodeBound (inputLength : Nat) : Nat :=
  (inputLength + 1) ^ 2

def certificateCellBound (inputLength : Nat) : Nat :=
  2 * (inputLength + 1) ^ 4 + inputLength + 1

theorem certificateCellBound_polynomial :
    IsPolynomial certificateCellBound := by
  apply IsPolynomial.bounded 100 4
  intro n
  unfold certificateCellBound
  cases n with
  | zero => norm_num
  | succ n =>
      have hn : 1 ≤ n + 1 := by omega
      nlinarith [sq_nonneg (n : ℤ), sq_nonneg ((n : ℤ) ^ 2)]

theorem certificate_cellCount_le (formula : Formula)
    (certificate : Certificate)
    (hnodes : certificate.nodeCount ≤
      certificateNodeBound (encodeFormula formula).length)
    (hassignment : certificate.assignment.length ≤
      (encodeFormula formula).length)
    (hedges : certificate.edges.length =
      certificate.nodeCount * certificate.nodeCount) :
    certificate.cellCount ≤
      certificateCellBound (encodeFormula formula).length := by
  let n := (encodeFormula formula).length
  have hsquare :
      certificate.nodeCount * certificate.nodeCount ≤ (n + 1) ^ 4 := by
    dsimp [certificateNodeBound] at hnodes
    nlinarith [sq_nonneg (certificate.nodeCount : ℤ),
      sq_nonneg (((n + 1) ^ 2 : Nat) : ℤ)]
  simp [Certificate.cellCount, certificateCellBound, hedges]
  dsimp [n] at hnodes hassignment hsquare ⊢
  omega

private theorem sum_map_le_length_mul {α : Type*} (values : List α)
    (weight : α → Nat) (bound : Nat)
    (h : ∀ value ∈ values, weight value ≤ bound) :
    (values.map weight).sum ≤ values.length * bound := by
  induction values with
  | nil => simp
  | cons value values ih =>
      have hhead := h value (by simp)
      have htail : ∀ other ∈ values, weight other ≤ bound := by
        intro other hother
        exact h other (by simp [hother])
      have hi := ih htail
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [Nat.succ_mul]
      omega

theorem certificate_wire_le (formula : Formula)
    (certificate : Certificate)
    (hnodes : certificate.nodeCount ≤
      certificateNodeBound (encodeFormula formula).length)
    (hassignment : certificate.assignment.length ≤
      (encodeFormula formula).length)
    (hvalues : ∀ value ∈ certificate.assignment,
      value < certificate.nodeCount)
    (hedges : certificate.edges.length =
      certificate.nodeCount * certificate.nodeCount) :
    (encodeCertificate certificate).length ≤
      certificateWireBound (encodeFormula formula).length := by
  let n := (encodeFormula formula).length
  have hnpos : 0 < n := by
    dsimp [n]
    simp [encodeFormula, length_encodeNat]
  have hncode := length_encodeNat_le certificate.nodeCount
  have hacode := length_encodeNat_le certificate.assignment.length
  have hecode := length_encodeNat_le certificate.edges.length
  have hvalueCode : ∀ value ∈ certificate.assignment,
      (encodeNat value).length ≤ 2 * certificate.nodeCount + 1 := by
    intro value hvalue
    exact (length_encodeNat_le value).trans (by
      have := hvalues value hvalue
      omega)
  have hsum :
      (certificate.assignment.map fun value => (encodeNat value).length).sum ≤
        certificate.assignment.length * (2 * certificate.nodeCount + 1) := by
    exact sum_map_le_length_mul certificate.assignment
      (fun value => (encodeNat value).length)
      (2 * certificate.nodeCount + 1) hvalueCode
  have hnodeSquare :
      certificate.nodeCount * certificate.nodeCount ≤ (n + 1) ^ 4 := by
    dsimp [certificateNodeBound] at hnodes
    nlinarith [sq_nonneg (certificate.nodeCount : ℤ),
      sq_nonneg (((n + 1) ^ 2 : Nat) : ℤ)]
  rw [encodeCertificate]
  simp only [List.length_append, encodeNats_length]
  unfold certificateWireBound
  dsimp [n] at hncode hacode hecode hnodes hassignment hnodeSquare hnpos ⊢
  rw [hedges] at hecode ⊢
  have hsumBound :
      certificate.assignment.length * (2 * certificate.nodeCount + 1) ≤
        3 * (n + 1) ^ 3 := by
    dsimp [certificateNodeBound] at hnodes
    nlinarith [sq_nonneg (n : ℤ),
      sq_nonneg (certificate.nodeCount : ℤ)]
  have hncodeBound :
      (encodeNat certificate.nodeCount).length ≤ 3 * (n + 1) ^ 2 := by
    dsimp [certificateNodeBound] at hnodes
    nlinarith [sq_nonneg (n : ℤ)]
  have hacodeBound :
      (encodeNat certificate.assignment.length).length ≤ 3 * (n + 1) := by
    nlinarith
  have hecodeBound :
      (encodeNat (certificate.nodeCount * certificate.nodeCount)).length ≤
        3 * (n + 1) ^ 4 := by
    dsimp [n] at hnodeSquare ⊢
    have hone : 1 ≤ (n + 1) ^ 4 :=
      Nat.one_le_pow 4 (n + 1) (by omega)
    dsimp [n] at hone
    omega
  have hp1 : (n + 1) ≤ (n + 1) ^ 4 := by
    simpa using
      (Nat.pow_le_pow_right (n := n + 1) (by omega) (by omega : 1 ≤ 4))
  have hp2 : (n + 1) ^ 2 ≤ (n + 1) ^ 4 :=
    Nat.pow_le_pow_right (n := n + 1) (by omega) (by omega : 2 ≤ 4)
  have hp3 : (n + 1) ^ 3 ≤ (n + 1) ^ 4 :=
    Nat.pow_le_pow_right (n := n + 1) (by omega) (by omega : 3 ≤ 4)
  dsimp [n] at hsumBound hncodeBound hacodeBound hecodeBound hp1 hp2 hp3 ⊢
  omega

def checkerCost (l inputLength certificateCells : Nat) : Nat :=
  (inputLength + 1) * (certificateCells + 1) ^ (l + 1)

/-- For fixed `l`, the explicit finite-checker operation count is polynomial. -/
theorem checkerCost_polynomial (l : Nat) :
    IsPolynomial (fun n => checkerCost l n (certificateCellBound n)) := by
  have hinput : IsPolynomial (fun n => n + 1) :=
    IsPolynomial.add IsPolynomial.id (IsPolynomial.const 1)
  have hcells : IsPolynomial (fun n => certificateCellBound n + 1) :=
    IsPolynomial.add certificateCellBound_polynomial (IsPolynomial.const 1)
  have hpow : IsPolynomial
      (fun n => (certificateCellBound n + 1) ^ (l + 1)) := by
    induction l + 1 with
    | zero => simpa using IsPolynomial.const 1
    | succ k ih =>
        simpa [pow_succ] using IsPolynomial.mul ih hcells
  simpa [checkerCost] using IsPolynomial.mul hinput hpow

end COP90
