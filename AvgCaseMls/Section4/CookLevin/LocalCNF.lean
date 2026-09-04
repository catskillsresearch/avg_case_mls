import AvgCaseMls.SAT
import AvgCaseMls.Section4.CookLevin.Encoding

/-!
# Local Cook--Levin CNF

This module is independent of `CookLevin.CNF`, which is only a diagnostic
compiler for concrete traces.  Here every clause is obtained syntactically
from the machine, input, and unary time bound.

Rows use `Fin (time + 1)`.  The represented tape interval has the initial
input, `time` cells to its left, and `time + 1` cells to its right.  A row has
one-hot control and head fields and a one-hot three-valued symbol field at
each tape position.  Transition clauses reject constant-size invalid local
views.  Accepting halts stutter, allowing a run which accepts early to fill
the remaining rows.
-/

namespace AvgCaseMls.Section4.CookLevin

open AvgCaseMls.Foundation

abbrev LocalTime (inst : BoundedInstance) := Fin (inst.time + 1)

def localWidth (inst : BoundedInstance) : Nat :=
  inst.input.length + 2 * inst.time + 1

theorem localWidth_pos (inst : BoundedInstance) : 0 < localWidth inst := by
  simp [localWidth]

abbrev LocalPos (inst : BoundedInstance) := Fin (localWidth inst)

def controlCount (M : Machine) : Nat := max 1 M.code.size

theorem controlCount_pos (M : Machine) : 0 < controlCount M := by
  simp [controlCount]

abbrev LocalControl (inst : BoundedInstance) :=
  Fin (controlCount inst.machine)

inductive SymbolCode
  | blank
  | zero
  | one
  deriving DecidableEq, Repr

def SymbolCode.toNat : SymbolCode → Nat
  | .blank => 0
  | .zero => 1
  | .one => 2

def SymbolCode.fromNat : Nat → SymbolCode
  | 0 => .blank
  | 1 => .zero
  | _ => .one

def SymbolCode.symbol : SymbolCode → TapeSymbol
  | .blank => none
  | .zero => some false
  | .one => some true

def allSymbols : List SymbolCode := [.blank, .zero, .one]

@[simp] theorem allSymbols_length : allSymbols.length = 3 := rfl

def rowStride (inst : BoundedInstance) : Nat :=
  controlCount inst.machine + 4 * localWidth inst

def pcVar (_inst : BoundedInstance) (time control : Nat) : Nat :=
  Nat.pair time (Nat.pair 0 control)

def headVar (_inst : BoundedInstance) (time position : Nat) : Nat :=
  Nat.pair time (Nat.pair 1 position)

def symbolVar (_inst : BoundedInstance)
    (time position : Nat) (symbol : SymbolCode) : Nat :=
  Nat.pair time (Nat.pair 2 (Nat.pair position symbol.toNat))

def positiveClause (vars : List Nat) : SAT.Clause :=
  vars.map SAT.Literal.pos

def negativeClause (vars : List Nat) : SAT.Clause :=
  vars.map SAT.Literal.neg

def pairwiseClauses (vars : List Nat) : SAT.CNF :=
  vars.flatMap fun i =>
    vars.filterMap fun j =>
      if i = j then none else some [.neg i, .neg j]

def oneHotClauses (vars : List Nat) : SAT.CNF :=
  positiveClause vars :: pairwiseClauses vars

def pcVars (inst : BoundedInstance) (time : Nat) : List Nat :=
  (List.range (controlCount inst.machine)).map (pcVar inst time)

def headVars (inst : BoundedInstance) (time : Nat) : List Nat :=
  (List.range (localWidth inst)).map (headVar inst time)

def symbolVars (inst : BoundedInstance) (time position : Nat) : List Nat :=
  allSymbols.map (symbolVar inst time position)

def rowOneHotClauses (inst : BoundedInstance) (time : Nat) : SAT.CNF :=
  oneHotClauses (pcVars inst time) ++
  oneHotClauses (headVars inst time) ++
  (List.range (localWidth inst)).flatMap fun position =>
    oneHotClauses (symbolVars inst time position)

def allOneHotClauses (inst : BoundedInstance) : SAT.CNF :=
  (List.range (inst.time + 1)).flatMap (rowOneHotClauses inst)

def initialSymbol (inst : BoundedInstance) (position : Nat) : TapeSymbol :=
  if position < inst.time then none
  else inst.input[position - inst.time]?

def symbolCodeOf : TapeSymbol → SymbolCode
  | none => .blank
  | some false => .zero
  | some true => .one

def initialClauses (inst : BoundedInstance) : SAT.CNF :=
  [[.pos (pcVar inst 0 0)],
   [.pos (headVar inst 0 inst.time)]] ++
  (List.range (localWidth inst)).map fun position =>
    [.pos (symbolVar inst 0 position
      (symbolCodeOf (initialSymbol inst position)))]

def acceptingControl (M : Machine) (control : Nat) : Bool :=
  match M.code[control]? with
  | some (.halt true) => true
  | _ => false

def nextControl (next : Nat) : Option Nat :=
  some next

def controlHeadLegal (inst : BoundedInstance)
    (control : Nat) (scanned : TapeSymbol)
    (nextControl nextHead head : Nat) : Prop :=
  match inst.machine.code[control]? with
  | none => False
  | some (.halt accept) =>
      accept = true ∧ nextControl = control ∧ nextHead = head
  | some (.jump next) =>
      next < controlCount inst.machine ∧
        nextControl = next ∧ nextHead = head
  | some (.branch blank onZero one) =>
      let next := match scanned with
        | none => blank
        | some false => onZero
        | some true => one
      next < controlCount inst.machine ∧
        nextControl = next ∧ nextHead = head
  | some (.write _ next) =>
      next < controlCount inst.machine ∧
        nextControl = next ∧ nextHead = head
  | some (.moveLeft next) =>
      next < controlCount inst.machine ∧ 0 < head ∧
        nextControl = next ∧ nextHead + 1 = head
  | some (.moveRight next) =>
      next < controlCount inst.machine ∧ head + 1 < localWidth inst ∧
        nextControl = next ∧ nextHead = head + 1

instance controlHeadLegalDecidable (inst : BoundedInstance)
    (control : Nat) (scanned : TapeSymbol)
    (nextControl nextHead head : Nat) :
    Decidable (controlHeadLegal inst control scanned
      nextControl nextHead head) := by
  unfold controlHeadLegal
  split <;> infer_instance

def tapeCellLegal (inst : BoundedInstance)
    (control head position : Nat) (old new : TapeSymbol) : Prop :=
  match inst.machine.code[control]? with
  | some (.write written _) =>
      new = if position = head then written else old
  | some (.halt true) => new = old
  | some (.halt false) | none => False
  | _ => new = old

instance tapeCellLegalDecidable (inst : BoundedInstance)
    (control head position : Nat) (old new : TapeSymbol) :
    Decidable (tapeCellLegal inst control head position old new) := by
  unfold tapeCellLegal
  split <;> infer_instance

def controlTransitionClausesAt
    (inst : BoundedInstance) (time : Nat) : SAT.CNF :=
  (List.range (controlCount inst.machine)).flatMap fun control =>
  (List.range (controlCount inst.machine)).flatMap fun nextControl =>
  (List.range (localWidth inst)).flatMap fun head =>
  (List.range (localWidth inst)).flatMap fun nextHead =>
  allSymbols.filterMap fun scanned =>
    if controlHeadLegal inst control scanned.symbol
        nextControl nextHead head then none
    else some (negativeClause
      [pcVar inst time control,
       pcVar inst (time + 1) nextControl,
       headVar inst time head,
       headVar inst (time + 1) nextHead,
       symbolVar inst time head scanned])

def tapeTransitionClausesAt
    (inst : BoundedInstance) (time : Nat) : SAT.CNF :=
  (List.range (controlCount inst.machine)).flatMap fun control =>
  (List.range (localWidth inst)).flatMap fun head =>
  (List.range (localWidth inst)).flatMap fun position =>
  allSymbols.flatMap fun old =>
  allSymbols.filterMap fun new =>
    if tapeCellLegal inst control head position old.symbol new.symbol then none
    else some (negativeClause
      [pcVar inst time control,
       headVar inst time head,
       symbolVar inst time position old,
       symbolVar inst (time + 1) position new])

def transitionClausesAt
    (inst : BoundedInstance) (time : Nat) : SAT.CNF :=
  controlTransitionClausesAt inst time ++
    tapeTransitionClausesAt inst time

def allTransitionClauses (inst : BoundedInstance) : SAT.CNF :=
  (List.range inst.time).flatMap (transitionClausesAt inst)

def finalClauses (inst : BoundedInstance) : SAT.CNF :=
  if inst.time = 0 then [[]]
  else
    [(List.range (controlCount inst.machine)).filterMap fun control =>
      if acceptingControl inst.machine control
      then some (.pos (pcVar inst (inst.time - 1) control))
      else none]

def sourceVar (index : Nat) : Nat :=
  Nat.pair 0 (Nat.pair 3 index)

def sourcePayloadLiteral (bit : Bool) : SAT.Literal :=
  if bit then .pos 0 else .neg 0

def sourceClause (entry : Nat × Bool) : SAT.Clause :=
  [.pos (sourceVar entry.1), .neg (sourceVar entry.1),
    sourcePayloadLiteral entry.2]

def sourceDelimiter : SAT.Clause := [.pos (sourceVar 0), .neg (sourceVar 0)]

def sourceBlockBits (bits : Bitstring) : SAT.CNF :=
  bits.zipIdx.map
    (fun entry => sourceClause (entry.2, entry.1)) ++ [sourceDelimiter]

def sourceBlock (inst : BoundedInstance) : SAT.CNF :=
  sourceBlockBits (encodeBoundedInstance inst)

/--
The genuine local Cook--Levin compiler. Its semantic clauses are generated
locally; the leading provenance block is linear in and charges every source
bit separately.
-/
def localTableauCNF (inst : BoundedInstance) : SAT.CNF :=
  sourceBlock inst ++
    (allOneHotClauses inst ++ initialClauses inst ++
      allTransitionClauses inst ++ finalClauses inst)

def localTableauCNFWithSource
    (source : Bitstring) (inst : BoundedInstance) : SAT.CNF :=
  sourceBlockBits source ++
    (allOneHotClauses inst ++ initialClauses inst ++
      allTransitionClauses inst ++ finalClauses inst)

theorem evalSourceClause (assignment : SAT.Assignment) (entry : Nat × Bool) :
    SAT.evalClause assignment (sourceClause entry) := by
  by_cases h : assignment (sourceVar entry.1)
  · exact ⟨.pos (sourceVar entry.1), by simp [sourceClause], h⟩
  · exact ⟨.neg (sourceVar entry.1), by simp [sourceClause], h⟩

theorem evalSourceBlock (assignment : SAT.Assignment) (inst : BoundedInstance) :
    SAT.evalCNF assignment (sourceBlock inst) := by
  intro clause hclause
  rcases List.mem_append.mp hclause with hclause | hclause
  · simp only [List.mem_map] at hclause
    rcases hclause with ⟨entry, _, rfl⟩
    exact evalSourceClause assignment _
  · simp only [List.mem_singleton] at hclause
    subst clause
    by_cases h : assignment (sourceVar 0)
    · exact ⟨.pos (sourceVar 0), by simp [sourceDelimiter], h⟩
    · exact ⟨.neg (sourceVar 0), by simp [sourceDelimiter], h⟩

theorem evalSourceBlockBits
    (assignment : SAT.Assignment) (bits : Bitstring) :
    SAT.evalCNF assignment (sourceBlockBits bits) := by
  intro clause hclause
  rcases List.mem_append.mp hclause with hclause | hclause
  · simp only [sourceBlockBits, List.mem_map] at hclause
    rcases hclause with ⟨entry, _, rfl⟩
    exact evalSourceClause assignment _
  · simp only [sourceBlockBits, List.mem_singleton] at hclause
    subst clause
    by_cases h : assignment (sourceVar 0)
    · exact ⟨.pos (sourceVar 0), by simp [sourceDelimiter], h⟩
    · exact ⟨.neg (sourceVar 0), by simp [sourceDelimiter], h⟩

def sourceBit? : SAT.Clause → Option Bool
  | _ :: _ :: .pos 0 :: [] => some true
  | _ :: _ :: .neg 0 :: [] => some false
  | _ => none

@[simp] theorem sourceBit?_sourceClause (entry : Nat × Bool) :
    sourceBit? (sourceClause entry) = some entry.2 := by
  rcases entry with ⟨index, bit⟩
  cases bit <;> rfl

def recoverLocalSource : SAT.CNF → Bitstring
  | [] => []
  | clause :: formula =>
      match sourceBit? clause with
      | some bit => bit :: recoverLocalSource formula
      | none => []

private theorem recoverSourceEntries
    (entries : List (Bool × Nat)) (rest : SAT.CNF) :
    recoverLocalSource
      (entries.map (fun entry => sourceClause (entry.2, entry.1)) ++
        sourceDelimiter :: rest) =
      entries.map Prod.fst := by
  induction entries with
  | nil => simp [recoverLocalSource, sourceDelimiter, sourceBit?]
  | cons entry entries ih =>
      cases entry with
      | mk bit index =>
          simp [recoverLocalSource, ih]

private theorem zipIdx_fst (bits : Bitstring) :
    bits.zipIdx.map Prod.fst = bits := by
  exact List.zipIdx_map_fst 0 bits

@[simp] theorem recoverLocalSource_localTableauCNF
    (inst : BoundedInstance) :
    recoverLocalSource (localTableauCNF inst) =
      encodeBoundedInstance inst := by
  rw [localTableauCNF, sourceBlock, sourceBlockBits]
  simpa [zipIdx_fst] using
    recoverSourceEntries (encodeBoundedInstance inst).zipIdx
      (allOneHotClauses inst ++ initialClauses inst ++
        allTransitionClauses inst ++ finalClauses inst)

@[simp] theorem recoverLocalSource_localTableauCNFWithSource
    (source : Bitstring) (inst : BoundedInstance) :
    recoverLocalSource (localTableauCNFWithSource source inst) = source := by
  rw [localTableauCNFWithSource, sourceBlockBits]
  simpa [zipIdx_fst] using
    recoverSourceEntries source.zipIdx
      (allOneHotClauses inst ++ initialClauses inst ++
        allTransitionClauses inst ++ finalClauses inst)

@[simp] theorem recoverLocalSource_sourceBlockBits_append
    (source : Bitstring) (rest : SAT.CNF) :
    recoverLocalSource (sourceBlockBits source ++ rest) = source := by
  rw [sourceBlockBits, List.append_assoc]
  simpa [zipIdx_fst] using recoverSourceEntries source.zipIdx rest

theorem localTableauCNF_injective :
    Function.Injective localTableauCNF := by
  intro first second heq
  have hrecover := congrArg recoverLocalSource heq
  simp only [recoverLocalSource_localTableauCNF] at hrecover
  exact encodeBoundedInstance_injective hrecover

def ExactlyOne (assignment : SAT.Assignment) (vars : List Nat) : Prop :=
  (∃ v ∈ vars, assignment v) ∧
  ∀ i ∈ vars, ∀ j ∈ vars, assignment i → assignment j → i = j

private theorem evalPositiveClause_iff
    (assignment : SAT.Assignment) (vars : List Nat) :
    SAT.evalClause assignment (positiveClause vars) ↔
      ∃ v ∈ vars, assignment v := by
  simp [SAT.evalClause, positiveClause, SAT.evalLiteral]

private theorem pairwiseClause_mem {vars : List Nat} {i j : Nat}
    (hi : i ∈ vars) (hj : j ∈ vars) (hne : i ≠ j) :
    [.neg i, .neg j] ∈ pairwiseClauses vars := by
  simp only [pairwiseClauses, List.mem_flatMap]
  refine ⟨i, hi, ?_⟩
  simp [hj, hne]

private theorem pairwiseClauses_sound
    (assignment : SAT.Assignment) (vars : List Nat)
    (h : SAT.evalCNF assignment (pairwiseClauses vars)) :
    ∀ i ∈ vars, ∀ j ∈ vars,
      assignment i → assignment j → i = j := by
  intro i hi j hj hai haj
  by_contra hne
  have hc := h [.neg i, .neg j] (pairwiseClause_mem hi hj hne)
  simp [SAT.evalClause, SAT.evalLiteral, hai, haj] at hc

private theorem pairwiseClauses_complete
    (assignment : SAT.Assignment) (vars : List Nat)
    (h : ∀ i ∈ vars, ∀ j ∈ vars,
      assignment i → assignment j → i = j) :
    SAT.evalCNF assignment (pairwiseClauses vars) := by
  intro clause hclause
  simp only [pairwiseClauses, List.mem_flatMap] at hclause
  rcases hclause with ⟨i, hi, hclause⟩
  simp only [List.mem_filterMap] at hclause
  rcases hclause with ⟨j, hj, hij⟩
  split at hij
  · contradiction
  · simp only [Option.some.injEq] at hij
    subst clause
    by_cases hai : assignment i
    · have haj : ¬ assignment j := by
        intro haj
        exact ‹i ≠ j› (h i hi j hj hai haj)
      exact ⟨.neg j, by simp, haj⟩
    · exact ⟨.neg i, by simp, hai⟩

theorem evalOneHotClauses_iff
    (assignment : SAT.Assignment) (vars : List Nat) :
    SAT.evalCNF assignment (oneHotClauses vars) ↔
      ExactlyOne assignment vars := by
  rw [oneHotClauses, SAT.evalCNF_cons]
  constructor
  · rintro ⟨hatleast, hatmost⟩
    exact ⟨(evalPositiveClause_iff assignment vars).mp hatleast,
      pairwiseClauses_sound assignment vars hatmost⟩
  · rintro ⟨hatleast, hatmost⟩
    exact ⟨(evalPositiveClause_iff assignment vars).mpr hatleast,
      pairwiseClauses_complete assignment vars hatmost⟩

def timeAt (inst : BoundedInstance) (k : Fin inst.time) :
    LocalTime inst :=
  ⟨k.1, Nat.lt_succ_of_lt k.2⟩

def timeNext (inst : BoundedInstance) (k : Fin inst.time) :
    LocalTime inst :=
  ⟨k.1 + 1, Nat.succ_lt_succ k.2⟩

def acceptingTime (inst : BoundedInstance) : LocalTime inst :=
  ⟨inst.time - 1, by omega⟩

/-- A bounded tableau represented by the fields carried by CNF variables. -/
structure LocalTableauData (inst : BoundedInstance) where
  control : LocalTime inst → LocalControl inst
  head : LocalTime inst → LocalPos inst
  tape : LocalTime inst → LocalPos inst → SymbolCode

/-- Semantic local validity, independently of propositional syntax. -/
structure BoundedLocalAcceptingTableau
    (inst : BoundedInstance) (tableau : LocalTableauData inst) : Prop where
  positiveTime : 0 < inst.time
  initialControl : (tableau.control ⟨0, Nat.zero_lt_succ _⟩).1 = 0
  initialHead : (tableau.head ⟨0, Nat.zero_lt_succ _⟩).1 = inst.time
  initialTape : ∀ position : LocalPos inst,
    (tableau.tape ⟨0, Nat.zero_lt_succ _⟩ position).symbol =
      initialSymbol inst position.1
  controlTransition : ∀ k : Fin inst.time,
    controlHeadLegal inst
      (tableau.control (timeAt inst k)).1
      (tableau.tape (timeAt inst k) (tableau.head (timeAt inst k))).symbol
      (tableau.control (timeNext inst k)).1
      (tableau.head (timeNext inst k)).1
      (tableau.head (timeAt inst k)).1
  tapeTransition : ∀ k : Fin inst.time, ∀ position : LocalPos inst,
    tapeCellLegal inst
      (tableau.control (timeAt inst k)).1
      (tableau.head (timeAt inst k)).1 position.1
      (tableau.tape (timeAt inst k) position).symbol
      (tableau.tape (timeNext inst k) position).symbol
  accepting : acceptingControl inst.machine
    (tableau.control (acceptingTime inst)).1 = true

/-- An assignment represents exactly the three one-hot fields of a tableau. -/
def AssignmentEncodes (inst : BoundedInstance)
    (assignment : SAT.Assignment) (tableau : LocalTableauData inst) : Prop :=
  (∀ time : LocalTime inst, ∀ control : LocalControl inst,
    assignment (pcVar inst time.1 control.1) ↔
      control = tableau.control time) ∧
  (∀ time : LocalTime inst, ∀ position : LocalPos inst,
    assignment (headVar inst time.1 position.1) ↔
      position = tableau.head time) ∧
  (∀ time : LocalTime inst, ∀ position : LocalPos inst,
      ∀ symbol : SymbolCode,
    assignment (symbolVar inst time.1 position.1 symbol) ↔
      symbol = tableau.tape time position)

private theorem pcExactlyOne
    (inst : BoundedInstance) (assignment : SAT.Assignment)
    (h : SAT.evalCNF assignment (allOneHotClauses inst))
    (time : LocalTime inst) :
    ExactlyOne assignment (pcVars inst time.1) := by
  apply (evalOneHotClauses_iff assignment _).mp
  intro clause hclause
  apply h clause
  simp only [allOneHotClauses, List.mem_flatMap]
  refine ⟨time.1, List.mem_range.mpr time.2, ?_⟩
  simp only [rowOneHotClauses]
  exact List.mem_append.mpr
    (Or.inl (List.mem_append.mpr (Or.inl hclause)))

private theorem headExactlyOne
    (inst : BoundedInstance) (assignment : SAT.Assignment)
    (h : SAT.evalCNF assignment (allOneHotClauses inst))
    (time : LocalTime inst) :
    ExactlyOne assignment (headVars inst time.1) := by
  apply (evalOneHotClauses_iff assignment _).mp
  intro clause hclause
  apply h clause
  simp only [allOneHotClauses, List.mem_flatMap]
  refine ⟨time.1, List.mem_range.mpr time.2, ?_⟩
  simp only [rowOneHotClauses]
  exact List.mem_append.mpr
    (Or.inl (List.mem_append.mpr (Or.inr hclause)))

private theorem symbolExactlyOne
    (inst : BoundedInstance) (assignment : SAT.Assignment)
    (h : SAT.evalCNF assignment (allOneHotClauses inst))
    (time : LocalTime inst) (position : LocalPos inst) :
    ExactlyOne assignment (symbolVars inst time.1 position.1) := by
  apply (evalOneHotClauses_iff assignment _).mp
  intro clause hclause
  apply h clause
  simp only [allOneHotClauses, List.mem_flatMap]
  refine ⟨time.1, List.mem_range.mpr time.2, ?_⟩
  simp only [rowOneHotClauses]
  apply List.mem_append.mpr
  right
  exact List.mem_flatMap.mpr
    ⟨position.1, List.mem_range.mpr position.2, hclause⟩

private theorem pcVars_mem_iff (inst : BoundedInstance)
    (time control : Nat) :
    pcVar inst time control ∈ pcVars inst time ↔
      control < controlCount inst.machine := by
  constructor
  · simp only [pcVars, List.mem_map, List.mem_range]
    rintro ⟨other, hother, heq⟩
    simp [pcVar] at heq
    omega
  · intro h
    simp only [pcVars, List.mem_map, List.mem_range]
    exact ⟨control, h, rfl⟩

private theorem headVars_mem_iff (inst : BoundedInstance)
    (time position : Nat) :
    headVar inst time position ∈ headVars inst time ↔
      position < localWidth inst := by
  constructor
  · simp only [headVars, List.mem_map, List.mem_range]
    rintro ⟨other, hother, heq⟩
    simp [headVar] at heq
    omega
  · intro h
    simp only [headVars, List.mem_map, List.mem_range]
    exact ⟨position, h, rfl⟩

private theorem symbolVars_mem (inst : BoundedInstance)
    (time position : Nat) (symbol : SymbolCode) :
    symbolVar inst time position symbol ∈ symbolVars inst time position := by
  cases symbol <;> simp [symbolVars, allSymbols]

private theorem pcIndexExists
    (inst : BoundedInstance) (assignment : SAT.Assignment)
    (h : SAT.evalCNF assignment (allOneHotClauses inst))
    (time : LocalTime inst) :
    ∃ control, control < controlCount inst.machine ∧
      assignment (pcVar inst time.1 control) := by
  rcases (pcExactlyOne inst assignment h time).1 with
    ⟨v, hvariable, ha⟩
  simp only [pcVars, List.mem_map, List.mem_range] at hvariable
  rcases hvariable with ⟨control, hcontrol, rfl⟩
  exact ⟨control, hcontrol, ha⟩

private theorem headIndexExists
    (inst : BoundedInstance) (assignment : SAT.Assignment)
    (h : SAT.evalCNF assignment (allOneHotClauses inst))
    (time : LocalTime inst) :
    ∃ position, position < localWidth inst ∧
      assignment (headVar inst time.1 position) := by
  rcases (headExactlyOne inst assignment h time).1 with
    ⟨v, hvariable, ha⟩
  simp only [headVars, List.mem_map, List.mem_range] at hvariable
  rcases hvariable with ⟨position, hposition, rfl⟩
  exact ⟨position, hposition, ha⟩

private theorem symbolIndexExists
    (inst : BoundedInstance) (assignment : SAT.Assignment)
    (h : SAT.evalCNF assignment (allOneHotClauses inst))
    (time : LocalTime inst) (position : LocalPos inst) :
    ∃ symbol, assignment
      (symbolVar inst time.1 position.1 symbol) := by
  rcases (symbolExactlyOne inst assignment h time position).1 with
    ⟨v, hvariable, ha⟩
  simp only [symbolVars, List.mem_map] at hvariable
  rcases hvariable with ⟨symbol, _, rfl⟩
  exact ⟨symbol, ha⟩

noncomputable def decodeLocalTableau
    (inst : BoundedInstance) (assignment : SAT.Assignment)
    (h : SAT.evalCNF assignment (allOneHotClauses inst)) :
    LocalTableauData inst where
  control := fun time =>
    ⟨Classical.choose (pcIndexExists inst assignment h time),
      (Classical.choose_spec
        (pcIndexExists inst assignment h time)).1⟩
  head := fun time =>
    ⟨Classical.choose (headIndexExists inst assignment h time),
      (Classical.choose_spec
        (headIndexExists inst assignment h time)).1⟩
  tape := fun time position =>
    Classical.choose (symbolIndexExists inst assignment h time position)

private theorem SymbolCode.toNat_injective :
    Function.Injective SymbolCode.toNat := by
  intro first second h
  cases first <;> cases second <;> simp [SymbolCode.toNat] at h ⊢

theorem assignmentEncodes_decode
    (inst : BoundedInstance) (assignment : SAT.Assignment)
    (h : SAT.evalCNF assignment (allOneHotClauses inst)) :
    AssignmentEncodes inst assignment
      (decodeLocalTableau inst assignment h) := by
  refine ⟨?_, ?_, ?_⟩
  · intro time control
    let chosen := Classical.choose (pcIndexExists inst assignment h time)
    have hchosen : assignment (pcVar inst time.1 chosen) :=
      (Classical.choose_spec
        (pcIndexExists inst assignment h time)).2
    constructor
    · intro hcontrol
      apply Fin.ext
      change control.1 = chosen
      have heq := (pcExactlyOne inst assignment h time).2
        (pcVar inst time.1 control.1)
        (by exact (pcVars_mem_iff inst time.1 control.1).mpr control.2)
        (pcVar inst time.1 chosen)
        (by
          apply (pcVars_mem_iff inst time.1 chosen).mpr
          exact (Classical.choose_spec
            (pcIndexExists inst assignment h time)).1)
        hcontrol hchosen
      simp [pcVar] at heq
      omega
    · intro heq
      subst control
      exact hchosen
  · intro time position
    let chosen := Classical.choose (headIndexExists inst assignment h time)
    have hchosen : assignment (headVar inst time.1 chosen) :=
      (Classical.choose_spec
        (headIndexExists inst assignment h time)).2
    constructor
    · intro hposition
      apply Fin.ext
      change position.1 = chosen
      have heq := (headExactlyOne inst assignment h time).2
        (headVar inst time.1 position.1)
        (by exact (headVars_mem_iff inst time.1 position.1).mpr position.2)
        (headVar inst time.1 chosen)
        (by
          apply (headVars_mem_iff inst time.1 chosen).mpr
          exact (Classical.choose_spec
            (headIndexExists inst assignment h time)).1)
        hposition hchosen
      simp [headVar] at heq
      omega
    · intro heq
      subst position
      exact hchosen
  · intro time position symbol
    let chosen :=
      Classical.choose (symbolIndexExists inst assignment h time position)
    have hchosen :
        assignment (symbolVar inst time.1 position.1 chosen) :=
      Classical.choose_spec
        (symbolIndexExists inst assignment h time position)
    constructor
    · intro hsymbol
      change symbol = chosen
      have heq := (symbolExactlyOne inst assignment h time position).2
        (symbolVar inst time.1 position.1 symbol)
        (symbolVars_mem inst time.1 position.1 symbol)
        (symbolVar inst time.1 position.1 chosen)
        (symbolVars_mem inst time.1 position.1 chosen)
        hsymbol hchosen
      apply SymbolCode.toNat_injective
      simp [symbolVar] at heq
      omega
    · intro heq
      subst symbol
      exact hchosen

/-- The assignment-level meaning of the four structural clause families. -/
structure ValidLocalTableau
    (inst : BoundedInstance) (assignment : SAT.Assignment) : Prop where
  oneHot : SAT.evalCNF assignment (allOneHotClauses inst)
  initial : SAT.evalCNF assignment (initialClauses inst)
  transition : SAT.evalCNF assignment (allTransitionClauses inst)
  final : SAT.evalCNF assignment (finalClauses inst)

private theorem evalUnitPos {assignment : SAT.Assignment} {v : Nat}
    (h : SAT.evalClause assignment [.pos v]) :
    assignment v := by
  simpa [SAT.evalClause, SAT.evalLiteral] using h

@[simp] theorem symbolCodeOf_symbol (symbol : TapeSymbol) :
    (symbolCodeOf symbol).symbol = symbol := by
  cases symbol with
  | none => rfl
  | some bit => cases bit <;> rfl

private theorem SymbolCode.symbol_injective :
    Function.Injective SymbolCode.symbol := by
  intro first second h
  cases first <;> cases second <;> simp [SymbolCode.symbol] at h ⊢

theorem decodeLocalTableau_valid
    (inst : BoundedInstance) (assignment : SAT.Assignment)
    (hclauses : ValidLocalTableau inst assignment) :
    BoundedLocalAcceptingTableau inst
      (decodeLocalTableau inst assignment hclauses.oneHot) := by
  let tableau :=
    decodeLocalTableau inst assignment hclauses.oneHot
  have hencode :
      AssignmentEncodes inst assignment tableau :=
    assignmentEncodes_decode inst assignment hclauses.oneHot
  have htime : inst.time ≠ 0 := by
    intro hz
    have hempty : [] ∈ finalClauses inst := by
      simp [finalClauses, hz]
    exact SAT.evalClause_nil assignment
      (hclauses.final [] hempty)
  refine
    { positiveTime := Nat.pos_of_ne_zero htime
      initialControl := ?_
      initialHead := ?_
      initialTape := ?_
      controlTransition := ?_
      tapeTransition := ?_
      accepting := ?_ }
  · have ha : assignment (pcVar inst 0 0) := by
      apply evalUnitPos
      apply hclauses.initial [.pos (pcVar inst 0 0)]
      simp [initialClauses]
    let control : LocalControl inst :=
      ⟨0, controlCount_pos inst.machine⟩
    have heq := (hencode.1
      ⟨0, Nat.zero_lt_succ _⟩ control).mp ha
    exact congrArg Fin.val heq.symm
  · have ha : assignment (headVar inst 0 inst.time) := by
      apply evalUnitPos
      apply hclauses.initial [.pos (headVar inst 0 inst.time)]
      simp [initialClauses]
    have hpos : inst.time < localWidth inst := by
      simp [localWidth]
      omega
    let position : LocalPos inst := ⟨inst.time, hpos⟩
    have heq := (hencode.2.1
      ⟨0, Nat.zero_lt_succ _⟩ position).mp ha
    exact congrArg Fin.val heq.symm
  · intro position
    let desired := symbolCodeOf (initialSymbol inst position.1)
    have ha : assignment (symbolVar inst 0 position.1 desired) := by
      apply evalUnitPos
      apply hclauses.initial
        [.pos (symbolVar inst 0 position.1 desired)]
      simp only [initialClauses, List.mem_append]
      right
      simp only [List.mem_map, List.mem_range]
      exact ⟨position.1, position.2, by simp [desired]⟩
    have heq := (hencode.2.2
      ⟨0, Nat.zero_lt_succ _⟩ position desired).mp ha
    rw [← heq]
    exact symbolCodeOf_symbol _
  · intro k
    let now := timeAt inst k
    let next := timeNext inst k
    let control := tableau.control now
    let nextControl := tableau.control next
    let head := tableau.head now
    let nextHead := tableau.head next
    let scanned := tableau.tape now head
    by_contra hillegal
    have hmember :
        negativeClause
          [pcVar inst k.1 control.1,
           pcVar inst (k.1 + 1) nextControl.1,
           headVar inst k.1 head.1,
           headVar inst (k.1 + 1) nextHead.1,
           symbolVar inst k.1 head.1 scanned] ∈
          allTransitionClauses inst := by
      simp only [allTransitionClauses, List.mem_flatMap]
      refine ⟨k.1, List.mem_range.mpr k.2, ?_⟩
      apply List.mem_append.mpr
      left
      simp only [controlTransitionClausesAt, List.mem_flatMap]
      refine ⟨control.1, List.mem_range.mpr control.2, ?_⟩
      refine ⟨nextControl.1, List.mem_range.mpr nextControl.2, ?_⟩
      refine ⟨head.1, List.mem_range.mpr head.2, ?_⟩
      refine ⟨nextHead.1, List.mem_range.mpr nextHead.2, ?_⟩
      simp only [List.mem_filterMap]
      refine ⟨scanned, ?_, ?_⟩
      · cases scanned <;> simp [allSymbols]
      · have hillegal' :
            ¬ controlHeadLegal inst control.1 scanned.symbol
              nextControl.1 nextHead.1 head.1 := by
          simpa [now, next, control, nextControl, head, nextHead,
            scanned] using hillegal
        rw [if_neg hillegal']
    have heval := hclauses.transition _ hmember
    have hc := (hencode.1 now control).2 rfl
    have hc' := (hencode.1 next nextControl).2 rfl
    have hh := (hencode.2.1 now head).2 rfl
    have hh' := (hencode.2.1 next nextHead).2 rfl
    have hs := (hencode.2.2 now head scanned).2 rfl
    have hc0 : assignment (pcVar inst k.1 control.1) := by
      simpa [now, timeAt] using hc
    have hc1 : assignment (pcVar inst (k.1 + 1) nextControl.1) := by
      simpa [next, timeNext] using hc'
    have hh0 : assignment (headVar inst k.1 head.1) := by
      simpa [now, timeAt] using hh
    have hh1 : assignment (headVar inst (k.1 + 1) nextHead.1) := by
      simpa [next, timeNext] using hh'
    have hs0 : assignment (symbolVar inst k.1 head.1 scanned) := by
      simpa [now, timeAt] using hs
    simp [negativeClause, SAT.evalClause, SAT.evalLiteral,
      hc0, hc1, hh0, hh1, hs0] at heval
  · intro k position
    let now := timeAt inst k
    let next := timeNext inst k
    let control := tableau.control now
    let head := tableau.head now
    let old := tableau.tape now position
    let new := tableau.tape next position
    by_contra hillegal
    have hmember :
        negativeClause
          [pcVar inst k.1 control.1,
           headVar inst k.1 head.1,
           symbolVar inst k.1 position.1 old,
           symbolVar inst (k.1 + 1) position.1 new] ∈
          allTransitionClauses inst := by
      simp only [allTransitionClauses, List.mem_flatMap]
      refine ⟨k.1, List.mem_range.mpr k.2, ?_⟩
      apply List.mem_append.mpr
      right
      simp only [tapeTransitionClausesAt, List.mem_flatMap]
      refine ⟨control.1, List.mem_range.mpr control.2, ?_⟩
      refine ⟨head.1, List.mem_range.mpr head.2, ?_⟩
      refine ⟨position.1, List.mem_range.mpr position.2, ?_⟩
      refine ⟨old, by cases old <;> simp [allSymbols], ?_⟩
      simp only [List.mem_filterMap]
      refine ⟨new, by cases new <;> simp [allSymbols], ?_⟩
      have hillegal' :
          ¬ tapeCellLegal inst control.1 head.1 position.1
            old.symbol new.symbol := by
        simpa [now, next, control, head, old, new] using hillegal
      rw [if_neg hillegal']
    have heval := hclauses.transition _ hmember
    have hc := (hencode.1 now control).2 rfl
    have hh := (hencode.2.1 now head).2 rfl
    have ho := (hencode.2.2 now position old).2 rfl
    have hn := (hencode.2.2 next position new).2 rfl
    have hc0 : assignment (pcVar inst k.1 control.1) := by
      simpa [now, timeAt] using hc
    have hh0 : assignment (headVar inst k.1 head.1) := by
      simpa [now, timeAt] using hh
    have ho0 : assignment (symbolVar inst k.1 position.1 old) := by
      simpa [now, timeAt] using ho
    have hn1 : assignment
        (symbolVar inst (k.1 + 1) position.1 new) := by
      simpa [next, timeNext] using hn
    simp [negativeClause, SAT.evalClause, SAT.evalLiteral,
      hc0, hh0, ho0, hn1] at heval
  · have hformula : inst.time ≠ 0 := htime
    have hfinalClause :
        ((List.range (controlCount inst.machine)).filterMap fun control =>
          if acceptingControl inst.machine control
          then some (.pos (pcVar inst (inst.time - 1) control))
          else none) ∈ finalClauses inst := by
      simp [finalClauses, hformula]
    have heval := hclauses.final _ hfinalClause
    rcases heval with ⟨literal, hliteral, hliteralTrue⟩
    simp only [List.mem_filterMap] at hliteral
    rcases hliteral with ⟨control, hcontrol, hliteral⟩
    split at hliteral
    · simp only [Option.some.injEq] at hliteral
      subst literal
      have hbound := List.mem_range.mp hcontrol
      let q : LocalControl inst := ⟨control, hbound⟩
      have ha : assignment (pcVar inst (inst.time - 1) control) := hliteralTrue
      have heq := (hencode.1
        (acceptingTime inst) q).mp ha
      rw [← congrArg Fin.val heq]
      exact ‹acceptingControl inst.machine control = true›
    · contradiction

private theorem evalCNF_append (assignment : SAT.Assignment)
    (first second : SAT.CNF) :
    SAT.evalCNF assignment (first ++ second) ↔
      SAT.evalCNF assignment first ∧ SAT.evalCNF assignment second := by
  constructor
  · intro h
    constructor
    · intro clause hclause
      exact h clause (List.mem_append_left second hclause)
    · intro clause hclause
      exact h clause (List.mem_append_right first hclause)
  · rintro ⟨hfirst, hsecond⟩ clause hclause
    rcases List.mem_append.mp hclause with hclause | hclause
    · exact hfirst clause hclause
    · exact hsecond clause hclause

/-- CNF satisfaction is exactly validity of its bounded local tableau. -/
theorem assignment_iff_validLocalTableau
    (inst : BoundedInstance) (assignment : SAT.Assignment) :
    SAT.evalCNF assignment (localTableauCNF inst) ↔
      ValidLocalTableau inst assignment := by
  simp only [localTableauCNF, evalCNF_append]
  constructor
  · rintro ⟨_, ⟨⟨⟨hone, hinitial⟩, htransition⟩, hfinal⟩⟩
    exact ⟨hone, hinitial, htransition, hfinal⟩
  · rintro ⟨hone, hinitial, htransition, hfinal⟩
    exact ⟨evalSourceBlock assignment inst,
      ⟨⟨⟨hone, hinitial⟩, htransition⟩, hfinal⟩⟩

theorem assignmentWithSource_iff_validLocalTableau
    (source : Bitstring) (inst : BoundedInstance)
    (assignment : SAT.Assignment) :
    SAT.evalCNF assignment (localTableauCNFWithSource source inst) ↔
      ValidLocalTableau inst assignment := by
  simp only [localTableauCNFWithSource, evalCNF_append]
  constructor
  · rintro ⟨_, ⟨⟨⟨hone, hinitial⟩, htransition⟩, hfinal⟩⟩
    exact ⟨hone, hinitial, htransition, hfinal⟩
  · rintro ⟨hone, hinitial, htransition, hfinal⟩
    exact ⟨evalSourceBlockBits assignment source,
      ⟨⟨⟨hone, hinitial⟩, htransition⟩, hfinal⟩⟩

theorem localTableauCNF_satisfiable_iff_valid (inst : BoundedInstance) :
    SAT.Satisfiable (localTableauCNF inst) ↔
      ∃ assignment, ValidLocalTableau inst assignment := by
  simp only [SAT.Satisfiable]
  constructor
  · rintro ⟨assignment, h⟩
    exact ⟨assignment, (assignment_iff_validLocalTableau inst assignment).mp h⟩
  · rintro ⟨assignment, h⟩
    exact ⟨assignment, (assignment_iff_validLocalTableau inst assignment).mpr h⟩

/-- Every satisfying assignment reconstructs a unique-field semantic tableau. -/
theorem satisfyingAssignment_reconstructs
    (inst : BoundedInstance) (assignment : SAT.Assignment)
    (h : SAT.evalCNF assignment (localTableauCNF inst)) :
    ∃ tableau : LocalTableauData inst,
      AssignmentEncodes inst assignment tableau ∧
      BoundedLocalAcceptingTableau inst tableau := by
  have hfamilies :=
    (assignment_iff_validLocalTableau inst assignment).mp h
  let tableau :=
    decodeLocalTableau inst assignment hfamilies.oneHot
  exact ⟨tableau,
    assignmentEncodes_decode inst assignment hfamilies.oneHot,
    decodeLocalTableau_valid inst assignment hfamilies⟩

def tableauAssignment (inst : BoundedInstance)
    (tableau : LocalTableauData inst) : SAT.Assignment :=
  fun v =>
    (∃ time : LocalTime inst,
      v = pcVar inst time.1 (tableau.control time).1) ∨
    (∃ time : LocalTime inst,
      v = headVar inst time.1 (tableau.head time).1) ∨
    (∃ time : LocalTime inst, ∃ position : LocalPos inst,
      v = symbolVar inst time.1 position.1
        (tableau.tape time position))

theorem tableauAssignment_encodes (inst : BoundedInstance)
    (tableau : LocalTableauData inst) :
    AssignmentEncodes inst (tableauAssignment inst tableau) tableau := by
  refine ⟨?_, ?_, ?_⟩
  · intro time control
    constructor
    · rintro (⟨other, heq⟩ | ⟨other, heq⟩ | ⟨other, position, heq⟩)
      · simp [pcVar] at heq
        have htime : time = other := Fin.ext heq.1
        subst other
        exact Fin.ext heq.2
      · simp [pcVar, headVar] at heq
      · simp [pcVar, symbolVar] at heq
    · intro heq
      subst control
      exact Or.inl ⟨time, rfl⟩
  · intro time position
    constructor
    · rintro (⟨other, heq⟩ | ⟨other, heq⟩ | ⟨other, cell, heq⟩)
      · simp [headVar, pcVar] at heq
      · simp [headVar] at heq
        have htime : time = other := Fin.ext heq.1
        subst other
        exact Fin.ext heq.2
      · simp [headVar, symbolVar] at heq
    · intro heq
      subst position
      exact Or.inr (Or.inl ⟨time, rfl⟩)
  · intro time position symbol
    constructor
    · rintro (⟨other, heq⟩ | ⟨other, heq⟩ |
        ⟨other, cell, heq⟩)
      · simp [symbolVar, pcVar] at heq
      · simp [symbolVar, headVar] at heq
      · simp [symbolVar] at heq
        have htime : time = other := Fin.ext heq.1
        subst other
        have hposition : position = cell := Fin.ext heq.2.1
        subst cell
        exact SymbolCode.toNat_injective heq.2.2
    · intro heq
      subst symbol
      exact Or.inr (Or.inr ⟨time, position, rfl⟩)

private theorem pcExactlyOne_of_encodes
    {inst : BoundedInstance} {assignment : SAT.Assignment}
    {tableau : LocalTableauData inst}
    (h : AssignmentEncodes inst assignment tableau)
    (time : LocalTime inst) :
    ExactlyOne assignment (pcVars inst time.1) := by
  constructor
  · refine ⟨pcVar inst time.1 (tableau.control time).1, ?_, ?_⟩
    · exact (pcVars_mem_iff inst _ _).mpr (tableau.control time).2
    · exact (h.1 time (tableau.control time)).2 rfl
  · intro i hi j hj hai haj
    simp only [pcVars, List.mem_map, List.mem_range] at hi hj
    rcases hi with ⟨qi, hqi, rfl⟩
    rcases hj with ⟨qj, hqj, rfl⟩
    let fi : LocalControl inst := ⟨qi, hqi⟩
    let fj : LocalControl inst := ⟨qj, hqj⟩
    have hei := (h.1 time fi).mp hai
    have hej := (h.1 time fj).mp haj
    have heq : qi = qj := congrArg Fin.val (hei.trans hej.symm)
    subst qj
    rfl

private theorem headExactlyOne_of_encodes
    {inst : BoundedInstance} {assignment : SAT.Assignment}
    {tableau : LocalTableauData inst}
    (h : AssignmentEncodes inst assignment tableau)
    (time : LocalTime inst) :
    ExactlyOne assignment (headVars inst time.1) := by
  constructor
  · refine ⟨headVar inst time.1 (tableau.head time).1, ?_, ?_⟩
    · exact (headVars_mem_iff inst _ _).mpr (tableau.head time).2
    · exact (h.2.1 time (tableau.head time)).2 rfl
  · intro i hi j hj hai haj
    simp only [headVars, List.mem_map, List.mem_range] at hi hj
    rcases hi with ⟨xi, hxi, rfl⟩
    rcases hj with ⟨xj, hxj, rfl⟩
    let fi : LocalPos inst := ⟨xi, hxi⟩
    let fj : LocalPos inst := ⟨xj, hxj⟩
    have hei := (h.2.1 time fi).mp hai
    have hej := (h.2.1 time fj).mp haj
    have heq : xi = xj := congrArg Fin.val (hei.trans hej.symm)
    subst xj
    rfl

private theorem symbolExactlyOne_of_encodes
    {inst : BoundedInstance} {assignment : SAT.Assignment}
    {tableau : LocalTableauData inst}
    (h : AssignmentEncodes inst assignment tableau)
    (time : LocalTime inst) (position : LocalPos inst) :
    ExactlyOne assignment (symbolVars inst time.1 position.1) := by
  constructor
  · refine ⟨symbolVar inst time.1 position.1
      (tableau.tape time position), ?_, ?_⟩
    · exact symbolVars_mem inst _ _ _
    · exact (h.2.2 time position (tableau.tape time position)).2 rfl
  · intro i hi j hj hai haj
    simp only [symbolVars, List.mem_map] at hi hj
    rcases hi with ⟨si, _, rfl⟩
    rcases hj with ⟨sj, _, rfl⟩
    have hei := (h.2.2 time position si).mp hai
    have hej := (h.2.2 time position sj).mp haj
    rw [hei, hej]

private theorem evalNegativeClause_iff
    (assignment : SAT.Assignment) (vars : List Nat) :
    SAT.evalClause assignment (negativeClause vars) ↔
      ∃ v ∈ vars, ¬ assignment v := by
  simp [SAT.evalClause, SAT.evalLiteral, negativeClause]

theorem canonicalAssignment_valid
    (inst : BoundedInstance) (tableau : LocalTableauData inst)
    (hvalid : BoundedLocalAcceptingTableau inst tableau) :
    ValidLocalTableau inst (tableauAssignment inst tableau) := by
  let assignment := tableauAssignment inst tableau
  have hencode : AssignmentEncodes inst assignment tableau :=
    tableauAssignment_encodes inst tableau
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro clause hclause
    simp only [allOneHotClauses, List.mem_flatMap] at hclause
    rcases hclause with ⟨time, htime, hclause⟩
    let ft : LocalTime inst := ⟨time, List.mem_range.mp htime⟩
    simp only [rowOneHotClauses, List.mem_append] at hclause
    rcases hclause with (hclause | hclause) | hclause
    · exact (evalOneHotClauses_iff assignment _).mpr
        (pcExactlyOne_of_encodes hencode ft) clause hclause
    · exact (evalOneHotClauses_iff assignment _).mpr
        (headExactlyOne_of_encodes hencode ft) clause hclause
    · simp only [List.mem_flatMap] at hclause
      rcases hclause with ⟨position, hposition, hclause⟩
      let fp : LocalPos inst := ⟨position, List.mem_range.mp hposition⟩
      exact (evalOneHotClauses_iff assignment _).mpr
        (symbolExactlyOne_of_encodes hencode ft fp) clause hclause
  · intro clause hclause
    simp only [initialClauses, List.mem_append] at hclause
    rcases hclause with hclause | hclause
    · simp at hclause
      rcases hclause with rfl | rfl
      · simp only [SAT.evalClause_cons, SAT.evalClause_nil, or_false,
          SAT.evalLiteral]
        let q : LocalControl inst := ⟨0, controlCount_pos inst.machine⟩
        apply (hencode.1 ⟨0, Nat.zero_lt_succ _⟩ q).2
        apply Fin.ext
        simpa using hvalid.initialControl.symm
      · simp only [SAT.evalClause_cons, SAT.evalClause_nil, or_false,
          SAT.evalLiteral]
        have hp : inst.time < localWidth inst := by
          simp [localWidth]
          omega
        let p : LocalPos inst := ⟨inst.time, hp⟩
        apply (hencode.2.1 ⟨0, Nat.zero_lt_succ _⟩ p).2
        apply Fin.ext
        simpa using hvalid.initialHead.symm
    · simp only [List.mem_map] at hclause
      rcases hclause with ⟨position, hposition, rfl⟩
      have hp := List.mem_range.mp hposition
      let p : LocalPos inst := ⟨position, hp⟩
      simp only [SAT.evalClause_cons, SAT.evalClause_nil, or_false,
        SAT.evalLiteral]
      apply (hencode.2.2 ⟨0, Nat.zero_lt_succ _⟩ p
        (symbolCodeOf (initialSymbol inst position))).2
      apply SymbolCode.symbol_injective
      have htape := hvalid.initialTape p
      exact (symbolCodeOf_symbol _).trans htape.symm
  · intro clause hclause
    simp only [allTransitionClauses, List.mem_flatMap] at hclause
    rcases hclause with ⟨time, htime, hclause⟩
    have ht := List.mem_range.mp htime
    let k : Fin inst.time := ⟨time, ht⟩
    simp only [transitionClausesAt, List.mem_append] at hclause
    rcases hclause with hcontrol | htape
    · simp only [controlTransitionClausesAt, List.mem_flatMap] at hcontrol
      rcases hcontrol with ⟨q, hq, q', hq', x, hx, x', hx', hview⟩
      simp only [List.mem_filterMap] at hview
      rcases hview with ⟨s, hs, hview⟩
      split at hview
      · contradiction
      · simp only [Option.some.injEq] at hview
        subst clause
        apply (evalNegativeClause_iff assignment _).2
        by_contra hall
        push Not at hall
        have aq := hall (pcVar inst time q) (by simp)
        have aq' := hall (pcVar inst (time + 1) q') (by simp)
        have ax := hall (headVar inst time x) (by simp)
        have ax' := hall (headVar inst (time + 1) x') (by simp)
        have as := hall (symbolVar inst time x s) (by simp)
        let fq : LocalControl inst := ⟨q, List.mem_range.mp hq⟩
        let fq' : LocalControl inst := ⟨q', List.mem_range.mp hq'⟩
        let fx : LocalPos inst := ⟨x, List.mem_range.mp hx⟩
        let fx' : LocalPos inst := ⟨x', List.mem_range.mp hx'⟩
        have eqq := (hencode.1 (timeAt inst k) fq).mp (by simpa [k, timeAt] using aq)
        have eqq' := (hencode.1 (timeNext inst k) fq').mp
          (by simpa [k, timeNext] using aq')
        have eqx := (hencode.2.1 (timeAt inst k) fx).mp
          (by simpa [k, timeAt] using ax)
        have eqx' := (hencode.2.1 (timeNext inst k) fx').mp
          (by simpa [k, timeNext] using ax')
        have eqs := (hencode.2.2 (timeAt inst k) fx s).mp
          (by simpa [k, timeAt] using as)
        have hqv : q = (tableau.control (timeAt inst k)).1 :=
          congrArg Fin.val eqq
        have hqv' : q' = (tableau.control (timeNext inst k)).1 :=
          congrArg Fin.val eqq'
        have hxv : x = (tableau.head (timeAt inst k)).1 :=
          congrArg Fin.val eqx
        have hxv' : x' = (tableau.head (timeNext inst k)).1 :=
          congrArg Fin.val eqx'
        apply ‹¬ controlHeadLegal inst q _ q' x' x›
        simpa [hqv, hqv', hxv, hxv', eqs, eqx] using
          hvalid.controlTransition k
    · simp only [tapeTransitionClausesAt, List.mem_flatMap] at htape
      rcases htape with ⟨q, hq, x, hx, position, hp, old, hold,
        hnew⟩
      simp only [List.mem_filterMap] at hnew
      rcases hnew with ⟨new, hn, hclause⟩
      split at hclause
      · contradiction
      · simp only [Option.some.injEq] at hclause
        subst clause
        apply (evalNegativeClause_iff assignment _).2
        by_contra hall
        push Not at hall
        have aq := hall (pcVar inst time q) (by simp)
        have ax := hall (headVar inst time x) (by simp)
        have ao := hall (symbolVar inst time position old) (by simp)
        have an := hall (symbolVar inst (time + 1) position new) (by simp)
        let fq : LocalControl inst := ⟨q, List.mem_range.mp hq⟩
        let fx : LocalPos inst := ⟨x, List.mem_range.mp hx⟩
        let fp : LocalPos inst := ⟨position, List.mem_range.mp hp⟩
        have eqq := (hencode.1 (timeAt inst k) fq).mp
          (by simpa [k, timeAt] using aq)
        have eqx := (hencode.2.1 (timeAt inst k) fx).mp
          (by simpa [k, timeAt] using ax)
        have eqo := (hencode.2.2 (timeAt inst k) fp old).mp
          (by simpa [k, timeAt] using ao)
        have eqn := (hencode.2.2 (timeNext inst k) fp new).mp
          (by simpa [k, timeNext] using an)
        have hqv : q = (tableau.control (timeAt inst k)).1 :=
          congrArg Fin.val eqq
        have hxv : x = (tableau.head (timeAt inst k)).1 :=
          congrArg Fin.val eqx
        apply ‹¬ tapeCellLegal inst q x position _ _›
        simpa [hqv, hxv, eqo, eqn, fp] using
          hvalid.tapeTransition k fp
  · have htime : inst.time ≠ 0 := Nat.ne_of_gt hvalid.positiveTime
    rw [finalClauses, if_neg htime]
    simp only [SAT.evalCNF_cons, SAT.evalCNF_nil, and_true]
    refine ⟨.pos (pcVar inst (inst.time - 1)
      (tableau.control (acceptingTime inst)).1), ?_, ?_⟩
    · simp only [List.mem_filterMap]
      refine ⟨(tableau.control (acceptingTime inst)).1,
        List.mem_range.mpr
          (tableau.control (acceptingTime inst)).2, ?_⟩
      rw [if_pos hvalid.accepting]
    · simp only [SAT.evalLiteral]
      change assignment (pcVar inst (inst.time - 1)
        (tableau.control (acceptingTime inst)).1)
      exact (hencode.1 (acceptingTime inst) _).2 rfl

theorem localTableauCNF_satisfiable_iff_tableau
    (inst : BoundedInstance) :
    SAT.Satisfiable (localTableauCNF inst) ↔
      ∃ tableau : LocalTableauData inst,
        BoundedLocalAcceptingTableau inst tableau := by
  constructor
  · rintro ⟨assignment, hsatisfied⟩
    rcases satisfyingAssignment_reconstructs inst assignment hsatisfied with
      ⟨tableau, _, htableau⟩
    exact ⟨tableau, htableau⟩
  · rintro ⟨tableau, htableau⟩
    refine ⟨tableauAssignment inst tableau, ?_⟩
    apply (assignment_iff_validLocalTableau inst _).mpr
    exact canonicalAssignment_valid inst tableau htableau

/-- Tape contents at an absolute bounded-window coordinate. -/
def configCell (config : Config) (head position : Nat) : TapeSymbol :=
  if position < head then
    config.left[head - position - 1]?.getD none
  else if position = head then config.head
  else config.right[position - head - 1]?.getD none

@[simp] theorem configCell_head (config : Config) (head : Nat) :
    configCell config head head = config.head := by
  simp [configCell]

theorem configCell_write (config : Config) (next head position : Nat)
    (written : TapeSymbol) :
    configCell { config with pc := next, head := written } head position =
      if position = head then written else configCell config head position := by
  by_cases hp : position < head
  · simp [configCell, hp, ne_of_lt hp]
  · by_cases heq : position = head
    · subst position
      simp [configCell]
    · have hgt : head < position := by omega
      simp [configCell, hp, heq, hgt.ne']

theorem configCell_pc (config : Config) (next head position : Nat) :
    configCell { config with pc := next } head position =
      configCell config head position := by
  simp [configCell]

theorem configCell_moveRight (config : Config) (next head position : Nat) :
    configCell (moveRight config next) (head + 1) position =
      configCell config head position := by
  cases hright : config.right with
  | nil =>
      by_cases hlt : position < head
      · have hlt' : position < head + 1 := by omega
        have hindex : head + 1 - position - 1 =
            (head - position - 1) + 1 := by omega
        simp [moveRight, hright, configCell, hlt, hlt',
          hindex]
      · by_cases heq : position = head
        · subst position
          simp [moveRight, hright, configCell]
        · have hgt : head < position := by omega
          by_cases hnext : position = head + 1
          · subst position
            simp [moveRight, hright, configCell]
          · have hfar : head + 1 < position := by omega
            simp [moveRight, hright, configCell, hlt, heq,
              hgt, hnext, hfar]
  | cons symbol right =>
      by_cases hlt : position < head
      · have hlt' : position < head + 1 := by omega
        have hindex : head + 1 - position - 1 =
            (head - position - 1) + 1 := by omega
        simp [moveRight, hright, configCell, hlt, hlt',
          hindex]
      · by_cases heq : position = head
        · subst position
          simp [moveRight, hright, configCell]
        · have hgt : head < position := by omega
          by_cases hnext : position = head + 1
          · subst position
            simp [moveRight, hright, configCell]
          · have hfar : head + 1 < position := by omega
            have hindex : position - head - 1 =
                (position - (head + 1) - 1) + 1 := by omega
            simp [moveRight, hright, configCell, hlt, heq,
              hgt, hnext, hfar, hindex]

theorem configCell_moveLeft (config : Config) (next head position : Nat)
    (hhead : 0 < head) :
    configCell (moveLeft config next) (head - 1) position =
      configCell config head position := by
  cases hleft : config.left with
  | nil =>
      by_cases hbefore : position < head - 1
      · have hlt : position < head := by omega
        simp [moveLeft, hleft, configCell, hbefore, hlt]
      · by_cases hat : position = head - 1
        · subst position
          simp [moveLeft, hleft, configCell, hhead]
        · have hafter : head - 1 < position := by omega
          by_cases hold : position = head
          · subst position
            have hzero : head - (head - 1) - 1 = 0 := by omega
            have hnotlt : ¬ head < head - 1 := by omega
            have hneq : head ≠ head - 1 := by omega
            simp [moveLeft, hleft, configCell, hzero, hnotlt, hneq]
          · have hindex : position - (head - 1) - 1 =
                (position - head - 1) + 1 := by omega
            have hge : head < position := by omega
            have hnotlt : ¬ position < head := by omega
            simp [moveLeft, hleft, configCell, hbefore, hat,
              hafter, hold, hindex, hge, hnotlt]

  | cons symbol left =>
      by_cases hbefore : position < head - 1
      · have hlt : position < head := by omega
        have hindex : head - position - 1 =
            (head - 1 - position - 1) + 1 := by omega
        simp [moveLeft, hleft, configCell, hbefore, hlt, hindex]
      · by_cases hat : position = head - 1
        · subst position
          have hzero : head - (head - 1) - 1 = 0 := by omega
          simp [moveLeft, hleft, configCell, hhead, hzero]
        · have hafter : head - 1 < position := by omega
          by_cases hold : position = head
          · subst position
            have hzero : head - (head - 1) - 1 = 0 := by omega
            have hnotlt : ¬ head < head - 1 := by omega
            have hneq : head ≠ head - 1 := by omega
            simp [moveLeft, hleft, configCell, hzero, hnotlt, hneq]
          · have hindex : position - (head - 1) - 1 =
                (position - head - 1) + 1 := by omega
            have hge : head < position := by omega
            have hnotlt : ¬ position < head := by omega
            simp [moveLeft, hleft, configCell, hbefore, hat,
              hafter, hold, hindex, hge, hnotlt]

@[simp] theorem moveLeft_pc (config : Config) (next : Nat) :
    (moveLeft config next).pc = next := by
  unfold moveLeft
  split <;> rfl

@[simp] theorem moveRight_pc (config : Config) (next : Nat) :
    (moveRight config next).pc = next := by
  unfold moveRight
  split <;> rfl

def RowRepresents {inst : BoundedInstance} (tableau : LocalTableauData inst)
    (time : LocalTime inst) (config : Config) : Prop :=
  config.pc = (tableau.control time).1 ∧
  ∀ position : LocalPos inst,
    configCell config (tableau.head time).1 position.1 =
      (tableau.tape time position).symbol

theorem configCell_initial (input : Bitstring) (time position : Nat) :
    configCell (initial input) time position =
      (if position < time then none else input[position - time]?) := by
  cases input with
  | nil =>
      simp [initial, configCell]
  | cons bit rest =>
      by_cases hlt : position < time
      · simp [initial, configCell, hlt]
      · by_cases heq : position = time
        · subst position
          simp [initial, configCell]
        · have hgt : time < position := by omega
          have hindex : position - time = (position - time - 1) + 1 := by
            omega
          simp only [initial, configCell, hlt, if_false, heq]
          rw [hindex]
          simp only [List.getElem?_cons_succ, List.getElem?_map]
          cases hget : rest[position - time - 1]? <;> simp [hget]

theorem initialRow_represents
    (inst : BoundedInstance) (tableau : LocalTableauData inst)
    (hvalid : BoundedLocalAcceptingTableau inst tableau) :
    RowRepresents tableau ⟨0, Nat.zero_lt_succ _⟩
      (initial inst.input) := by
  constructor
  · cases inst.input <;> simpa [initial] using hvalid.initialControl.symm
  · intro position
    rw [show (tableau.head ⟨0, Nat.zero_lt_succ _⟩).1 = inst.time
      from hvalid.initialHead]
    rw [configCell_initial]
    exact (hvalid.initialTape position).symm

theorem localStep_simulates
    (inst : BoundedInstance) (tableau : LocalTableauData inst)
    (hvalid : BoundedLocalAcceptingTableau inst tableau)
    (k : Fin inst.time) (config : Config)
    (hrep : RowRepresents tableau (timeAt inst k) config) :
    (∃ result, step inst.machine config = .error result ∧
        result.accept = true) ∨
      ∃ nextConfig, step inst.machine config = .ok nextConfig ∧
        RowRepresents tableau (timeNext inst k) nextConfig := by
  let now := timeAt inst k
  let next := timeNext inst k
  let oldHead := tableau.head now
  let newHead := tableau.head next
  have hpc : config.pc = (tableau.control now).1 := hrep.1
  have hscan : config.head = (tableau.tape now oldHead).symbol := by
    have hcell := hrep.2 oldHead
    change configCell config oldHead.1 oldHead.1 =
      (tableau.tape now oldHead).symbol at hcell
    simpa using hcell
  have hcontrol := hvalid.controlTransition k
  have htape := hvalid.tapeTransition k
  rw [← hpc, ← hscan] at hcontrol
  cases hcode : inst.machine.code[config.pc]? with
  | none =>
      simp [controlHeadLegal, hcode] at hcontrol
  | some instruction =>
      cases instruction with
      | halt accept =>
          cases accept
          · simp [controlHeadLegal, hcode] at hcontrol
          · left
            refine ⟨⟨true, tapeOutput config, 0⟩, ?_, rfl⟩
            simp [step, hcode]
      | jump target =>
          simp [controlHeadLegal, hcode] at hcontrol
          rcases hcontrol with ⟨_, hnextControl, hnextHead⟩
          right
          refine ⟨{ config with pc := target }, by simp [step, hcode], ?_⟩
          constructor
          · simpa [hnextControl]
          · intro position
            have hcell := htape position
            rw [← hpc] at hcell
            simp [tapeCellLegal, hcode] at hcell
            simpa [hnextHead, configCell_pc] using
              (hrep.2 position).trans hcell.symm
      | branch blank zero one =>
          cases hheadSymbol : config.head with
          | none =>
            simp [controlHeadLegal, hcode, hheadSymbol] at hcontrol
            rcases hcontrol with ⟨_, hnextControl, hnextHead⟩
            right
            refine ⟨{ config with pc := blank },
              by simp [step, hcode, hheadSymbol], ?_⟩
            constructor
            · simpa [hnextControl]
            · intro position
              have hcell := htape position
              rw [← hpc] at hcell
              simp [tapeCellLegal, hcode] at hcell
              simpa [hnextHead, configCell_pc] using
                (hrep.2 position).trans hcell.symm
          | some bit =>
            cases bit
            · simp [controlHeadLegal, hcode, hheadSymbol] at hcontrol
              rcases hcontrol with ⟨_, hnextControl, hnextHead⟩
              right
              refine ⟨{ config with pc := zero },
                by simp [step, hcode, hheadSymbol], ?_⟩
              constructor
              · simpa [hnextControl]
              · intro position
                have hcell := htape position
                rw [← hpc] at hcell
                simp [tapeCellLegal, hcode] at hcell
                simpa [hnextHead, configCell_pc] using
                  (hrep.2 position).trans hcell.symm
            · simp [controlHeadLegal, hcode, hheadSymbol] at hcontrol
              rcases hcontrol with ⟨_, hnextControl, hnextHead⟩
              right
              refine ⟨{ config with pc := one },
                by simp [step, hcode, hheadSymbol], ?_⟩
              constructor
              · simpa [hnextControl]
              · intro position
                have hcell := htape position
                rw [← hpc] at hcell
                simp [tapeCellLegal, hcode] at hcell
                simpa [hnextHead, configCell_pc] using
                  (hrep.2 position).trans hcell.symm
      | write written target =>
          simp [controlHeadLegal, hcode] at hcontrol
          rcases hcontrol with ⟨_, hnextControl, hnextHead⟩
          right
          refine ⟨{ config with pc := target, head := written },
            by simp [step, hcode], ?_⟩
          constructor
          · simpa [hnextControl]
          · intro position
            have hcell := htape position
            rw [← hpc] at hcell
            simp [tapeCellLegal, hcode] at hcell
            rw [hnextHead, configCell_write]
            split
            · simp_all
            · have hne : ¬ position.1 =
                  (tableau.head (timeAt inst k)).1 := by assumption
              simp [hne] at hcell
              rw [hcell]
              simpa [now] using hrep.2 position
      | moveLeft target =>
          simp [controlHeadLegal, hcode] at hcontrol
          rcases hcontrol with
            ⟨_, hhead, hnextControl, hnextHead⟩
          right
          refine ⟨moveLeft config target, by simp [step, hcode], ?_⟩
          constructor
          · simpa [next] using hnextControl.symm
          · intro position
            have hcell := htape position
            rw [← hpc] at hcell
            simp [tapeCellLegal, hcode] at hcell
            have hheads : newHead.1 = oldHead.1 - 1 := by
              dsimp [newHead, oldHead, next, now]
              omega
            rw [hheads,
              configCell_moveLeft _ _ _ _ hhead]
            exact (hrep.2 position).trans hcell.symm
      | moveRight target =>
          simp [controlHeadLegal, hcode] at hcontrol
          rcases hcontrol with
            ⟨_, _, hnextControl, hnextHead⟩
          right
          refine ⟨moveRight config target, by simp [step, hcode], ?_⟩
          constructor
          · simpa [next] using hnextControl.symm
          · intro position
            have hcell := htape position
            rw [← hpc] at hcell
            simp [tapeCellLegal, hcode] at hcell
            rw [hnextHead, configCell_moveRight]
            exact (hrep.2 position).trans hcell.symm

theorem acceptingRow_halts
    (inst : BoundedInstance) (tableau : LocalTableauData inst)
    (time : LocalTime inst) (config : Config)
    (hrep : RowRepresents tableau time config)
    (haccept : acceptingControl inst.machine
      (tableau.control time).1 = true) :
    ∃ result, step inst.machine config = .error result ∧
      result.accept = true := by
  rw [← hrep.1] at haccept
  unfold acceptingControl at haccept
  cases hcode : inst.machine.code[config.pc]? with
  | none => simp [hcode] at haccept
  | some instruction =>
      cases instruction <;> simp [hcode] at haccept
      rename_i accept
      cases accept
      · contradiction
      · exact ⟨⟨true, tapeOutput config, 0⟩,
          by simp [step, hcode], rfl⟩

private theorem localTableau_acceptFromFuel
    (inst : BoundedInstance) (tableau : LocalTableauData inst)
    (hvalid : BoundedLocalAcceptingTableau inst tableau) :
    ∀ fuel : Nat, 0 < fuel → fuel ≤ inst.time →
      ∀ (config : Config) (elapsed : Nat),
        RowRepresents tableau
          ⟨inst.time - fuel, by omega⟩ config →
        ∃ result, evalFrom inst.machine fuel config elapsed = some result ∧
          result.accept = true := by
  intro fuel
  induction fuel with
  | zero => omega
  | succ remaining ih =>
      intro _ hle config elapsed hrep
      cases remaining with
      | zero =>
          have htime : (⟨inst.time - 1, by omega⟩ : LocalTime inst) =
              acceptingTime inst := by
            apply Fin.ext
            rfl
          have hhalt := acceptingRow_halts inst tableau
            ⟨inst.time - 1, by omega⟩ config hrep
            (by simpa [htime] using hvalid.accepting)
          rcases hhalt with ⟨halted, hstep, haccept⟩
          refine ⟨{ halted with steps := elapsed + 1 }, ?_, haccept⟩
          simp [evalFrom, hstep]
      | succ rest =>
          have hklt : inst.time - (rest + 2) < inst.time := by omega
          let k : Fin inst.time := ⟨inst.time - (rest + 2), hklt⟩
          have hcurrent :
              (⟨inst.time - (Nat.succ (Nat.succ rest)), by omega⟩ :
                LocalTime inst) = timeAt inst k := by
            apply Fin.ext
            simp [k, timeAt]
          have hrep' : RowRepresents tableau (timeAt inst k) config := by
            simpa [hcurrent] using hrep
          rcases localStep_simulates inst tableau hvalid k config hrep' with
            hhalt | ⟨nextConfig, hstep, hnextRep⟩
          · rcases hhalt with ⟨halted, hstep, haccept⟩
            refine ⟨{ halted with steps := elapsed + 1 }, ?_, haccept⟩
            simp [evalFrom, hstep]
          · have hnextTime :
                timeNext inst k =
                  (⟨inst.time - (rest + 1), by omega⟩ :
                    LocalTime inst) := by
              apply Fin.ext
              simp [k, timeNext]
              omega
            have hrecursive := ih (by omega) (by omega) nextConfig
              (elapsed + 1) (by simpa [hnextTime] using hnextRep)
            rcases hrecursive with ⟨result, hresult, haccept⟩
            refine ⟨result, ?_, haccept⟩
            rw [evalFrom, hstep]
            exact hresult

theorem localTableau_implies_accepts
    (inst : BoundedInstance) (tableau : LocalTableauData inst)
    (hvalid : BoundedLocalAcceptingTableau inst tableau) :
    AcceptsWithin inst.machine inst.input inst.time := by
  have hrep := initialRow_represents inst tableau hvalid
  have htime0 :
      (⟨inst.time - inst.time, by omega⟩ : LocalTime inst) =
        ⟨0, Nat.zero_lt_succ _⟩ := by
    apply Fin.ext
    simp
  obtain ⟨result, hresult, haccept⟩ :=
    localTableau_acceptFromFuel inst tableau hvalid inst.time
      hvalid.positiveTime (Nat.le_refl _) (initial inst.input) 0
      (by simpa [htime0] using hrep)
  exact ⟨result, by simpa [eval] using hresult, haccept⟩

theorem localTableauCNF_satisfiable_implies_accepts
    (inst : BoundedInstance) :
    SAT.Satisfiable (localTableauCNF inst) →
      AcceptsWithin inst.machine inst.input inst.time := by
  intro hsatisfiable
  obtain ⟨tableau, htableau⟩ :=
    (localTableauCNF_satisfiable_iff_tableau inst).mp hsatisfiable
  exact localTableau_implies_accepts inst tableau htableau

structure WindowState where
  config : Config
  head : Nat

def advanceState (M : Machine) (state : WindowState) : WindowState :=
  match step M state.config with
  | .error _ => state
  | .ok config =>
      let head :=
        match M.code[state.config.pc]? with
        | some (.moveLeft _) => state.head - 1
        | some (.moveRight _) => state.head + 1
        | _ => state.head
      ⟨config, head⟩

def traceState (M : Machine) : Nat → WindowState → WindowState
  | 0, state => state
  | n + 1, state => traceState M n (advanceState M state)

theorem traceState_succ (M : Machine) (n : Nat) (state : WindowState) :
    traceState M (n + 1) state = advanceState M (traceState M n state) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      rw [traceState, ih, traceState]

theorem traceState_head_bounds (M : Machine) (n start : Nat)
    (state : WindowState) (hstart : state.head = start) :
    start - n ≤ (traceState M n state).head ∧
      (traceState M n state).head ≤ start + n := by
  induction n generalizing state start with
  | zero => simp [traceState, hstart]
  | succ n ih =>
      subst start
      rw [traceState]
      have hsub : state.head ≤ state.head - 1 + 1 := by
        omega
      have hadd : state.head ≤ state.head + 1 := Nat.le_succ _
      have hstep : (advanceState M state).head + 1 ≥ state.head ∧
          (advanceState M state).head ≤ state.head + 1 := by
        cases hs : step M state.config with
        | error halted =>
            simp [advanceState, hs]
        | ok config =>
            cases hc : M.code[state.config.pc]? with
            | none =>
                simp [advanceState, hs, hc]
            | some instruction =>
                cases instruction with
                | moveLeft target =>
                    simp only [advanceState, hs, hc]
                    exact ⟨hsub, (Nat.sub_le _ _).trans hadd⟩
                | moveRight target =>
                    simp only [advanceState, hs, hc]
                    exact ⟨hadd.trans (Nat.le_succ _), le_rfl⟩
                | halt accept => simp [advanceState, hs, hc]
                | jump target => simp [advanceState, hs, hc]
                | branch blank zero one => simp [advanceState, hs, hc]
                | write symbol target => simp [advanceState, hs, hc]
      have htail := ih (advanceState M state).head
        (advanceState M state) rfl
      constructor
      · have hminus :
            state.head - 1 ≤ (advanceState M state).head := by omega
        calc
          state.head - (n + 1) = (state.head - 1) - n := by
            simp [Nat.sub_sub, Nat.add_comm]
          _ ≤ (advanceState M state).head - n :=
            Nat.sub_le_sub_right hminus n
          _ ≤ (traceState M n (advanceState M state)).head :=
            htail.1
      · omega

private theorem traceState_stutter (M : Machine) (state : WindowState)
    (h : advanceState M state = state) (n : Nat) :
    traceState M n state = state := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [traceState, h]
      exact ih

private theorem code_valid_of_accepting_evalFrom
    (M : Machine) (fuel : Nat) (config : Config) (elapsed : Nat)
    (result : Result)
    (heval : evalFrom M fuel config elapsed = some result)
    (haccept : result.accept = true) (n head : Nat) (hn : n < fuel) :
    (traceState M n ⟨config, head⟩).config.pc < M.code.size := by
  induction n generalizing fuel config elapsed head with
  | zero =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [evalFrom] at heval
          cases hstep : step M config with
          | error halted =>
              simp [hstep] at heval
              subst result
              unfold step at hstep
              cases hcode : M.code[config.pc]? with
              | none =>
                  simp [hcode] at hstep
                  cases hstep
                  contradiction
              | some instruction =>
                  have := Array.getElem?_eq_some_iff.mp hcode
                  exact this.1
          | ok next =>
              unfold step at hstep
              cases hcode : M.code[config.pc]? with
              | none => simp [hcode] at hstep
              | some instruction =>
                  exact (Array.getElem?_eq_some_iff.mp hcode).1
  | succ n ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [evalFrom] at heval
          cases hstep : step M config with
          | error halted =>
              have hadvance : advanceState M ⟨config, head⟩ =
                  ⟨config, head⟩ := by simp [advanceState, hstep]
              have hsame := traceState_stutter M ⟨config, head⟩
                hadvance n
              rw [traceState]
              rw [hadvance]
              rw [hsame]
              simp [hstep] at heval
              subst result
              have ha : halted.accept = true := haccept
              unfold step at hstep
              cases hcode : M.code[config.pc]? with
              | none =>
                  simp [hcode] at hstep
                  cases hstep
                  contradiction
              | some instruction =>
                  exact (Array.getElem?_eq_some_iff.mp hcode).1
          | ok next =>
              simp only [hstep] at heval
              have htrace :
                  (traceState M (n + 1) ⟨config, head⟩).config =
                    (traceState M n
                      (advanceState M ⟨config, head⟩)).config := rfl
              rw [htrace]
              have hadvance :
                  (advanceState M ⟨config, head⟩).config = next := by
                simp [advanceState, hstep]
              have hih := ih fuel next (elapsed + 1) heval
                (advanceState M ⟨config, head⟩).head (by omega)
              simpa [advanceState, hstep] using hih

private theorem finalTrace_halts_of_accepting_evalFrom
    (M : Machine) (fuel : Nat) (config : Config) (head elapsed : Nat)
    (result : Result)
    (heval : evalFrom M fuel config elapsed = some result)
    (haccept : result.accept = true) :
    ∃ halted,
      step M (traceState M (fuel - 1) ⟨config, head⟩).config =
        .error halted ∧ halted.accept = true := by
  induction fuel generalizing config head elapsed with
  | zero => simp [evalFrom] at heval
  | succ fuel ih =>
      simp only [evalFrom] at heval
      cases hstep : step M config with
      | error halted =>
          simp [hstep] at heval
          subst result
          refine ⟨halted, ?_, haccept⟩
          have hadvance : advanceState M ⟨config, head⟩ =
              ⟨config, head⟩ := by simp [advanceState, hstep]
          have hsame := traceState_stutter M ⟨config, head⟩
            hadvance fuel
          simpa [hsame] using hstep
      | ok next =>
          simp only [hstep] at heval
          cases fuel with
          | zero => simp [evalFrom] at heval
          | succ remaining =>
              have htail := ih next
                (advanceState M ⟨config, head⟩).head (elapsed + 1)
                heval
              simpa [traceState, advanceState, hstep] using htail

private theorem advanceState_localLegal
    (inst : BoundedInstance) (state : WindowState)
    (hpc : state.config.pc < inst.machine.code.size)
    (hnextpc : (advanceState inst.machine state).config.pc <
      inst.machine.code.size)
    (hleft : 0 < state.head)
    (hright : state.head + 1 < localWidth inst)
    (herror : ∀ result, step inst.machine state.config = .error result →
      result.accept = true) :
    controlHeadLegal inst state.config.pc state.config.head
        (advanceState inst.machine state).config.pc
        (advanceState inst.machine state).head state.head ∧
      ∀ position : Nat,
        tapeCellLegal inst state.config.pc state.head position
          (configCell state.config state.head position)
          (configCell (advanceState inst.machine state).config
            (advanceState inst.machine state).head position) := by
  have hpc' : state.config.pc < controlCount inst.machine :=
    hpc.trans_le (Nat.le_max_right _ _)
  have hnextpc' : (advanceState inst.machine state).config.pc <
      controlCount inst.machine :=
    hnextpc.trans_le (Nat.le_max_right _ _)
  cases hstep : step inst.machine state.config with
  | error halted =>
      have hstep0 := hstep
      have ha := herror halted hstep
      unfold step at hstep
      cases hcode : inst.machine.code[state.config.pc]? with
      | none =>
          simp [hcode] at hstep
          cases hstep
          contradiction
      | some instruction =>
          cases instruction with
          | halt accept =>
              cases accept
              · simp [hcode] at hstep
                cases hstep
                contradiction
              · constructor
                · simp [advanceState, hstep0, controlHeadLegal, hcode, hpc']
                · intro position
                  simp [advanceState, hstep0, tapeCellLegal, hcode]
          | jump target => simp [hcode] at hstep
          | branch blank zero one =>
              cases hs : state.config.head with
              | none => simp [hcode, hs] at hstep
              | some bit =>
                  cases bit <;> simp [hcode, hs] at hstep
          | write symbol target => simp [hcode] at hstep
          | moveLeft target => simp [hcode] at hstep
          | moveRight target => simp [hcode] at hstep
  | ok next =>
      have hstep0 := hstep
      unfold step at hstep
      cases hcode : inst.machine.code[state.config.pc]? with
      | none => simp [hcode] at hstep
      | some instruction =>
          cases instruction with
          | halt accept => simp [hcode] at hstep
          | jump target =>
              simp [hcode] at hstep
              subst next
              have htarget : target < controlCount inst.machine := by
                simpa [advanceState, hstep0] using hnextpc'
              constructor
              · simp [advanceState, hstep0, hcode, controlHeadLegal,
                  htarget]
              · intro position
                simp [advanceState, hstep0, hcode, tapeCellLegal]
                exact configCell_pc state.config target state.head position
          | branch blank zero one =>
              cases hs : state.config.head with
              | none =>
                  simp [hcode, hs] at hstep
                  subst next
                  have htarget : blank < controlCount inst.machine := by
                    simpa [advanceState, hstep0] using hnextpc'
                  constructor
                  · simp [advanceState, hstep0, hcode, hs,
                      controlHeadLegal, htarget]
                  · intro position
                    simp [advanceState, hstep0, hcode, hs, tapeCellLegal]
                    simpa [hs] using
                      configCell_pc state.config blank state.head position
              | some bit =>
                  cases bit <;>
                    simp [hcode, hs] at hstep <;>
                    subst next <;>
                    constructor
                  · have htarget : zero < controlCount inst.machine := by
                      simpa [advanceState, hstep0] using hnextpc'
                    simp [advanceState, hstep0, hcode, hs,
                      controlHeadLegal, htarget]
                  · intro position
                    simp [advanceState, hstep0, hcode, hs, tapeCellLegal]
                    simpa [hs] using
                      configCell_pc state.config zero state.head position
                  · have htarget : one < controlCount inst.machine := by
                      simpa [advanceState, hstep0] using hnextpc'
                    simp [advanceState, hstep0, hcode, hs,
                      controlHeadLegal, htarget]
                  · intro position
                    simp [advanceState, hstep0, hcode, hs, tapeCellLegal]
                    simpa [hs] using
                      configCell_pc state.config one state.head position
          | write written target =>
              simp [hcode] at hstep
              subst next
              have htarget : target < controlCount inst.machine := by
                simpa [advanceState, hstep0] using hnextpc'
              constructor
              · simp [advanceState, hstep0, hcode, controlHeadLegal,
                  htarget]
              · intro position
                simp [advanceState, hstep0, hcode, tapeCellLegal,
                  configCell_write]
          | moveLeft target =>
              simp [hcode] at hstep
              subst next
              have htarget : target < controlCount inst.machine := by
                simpa [advanceState, hstep0] using hnextpc'
              constructor
              · have hback : state.head - 1 + 1 = state.head :=
                  Nat.sub_add_cancel (by omega)
                simp [advanceState, hstep0, hcode, controlHeadLegal,
                  htarget, hleft, hback]
              · intro position
                simp [advanceState, hstep0, hcode, tapeCellLegal,
                  configCell_moveLeft, hleft]
          | moveRight target =>
              simp [hcode] at hstep
              subst next
              have htarget : target < controlCount inst.machine := by
                simpa [advanceState, hstep0] using hnextpc'
              constructor
              · simp [advanceState, hstep0, hcode, controlHeadLegal,
                  htarget, hright]
              · intro position
                simp [advanceState, hstep0, hcode, tapeCellLegal,
                  configCell_moveRight]

private theorem trace_error_accept_of_evalFrom
    (M : Machine) (fuel : Nat) (config : Config) (head elapsed : Nat)
    (result : Result)
    (heval : evalFrom M fuel config elapsed = some result)
    (haccept : result.accept = true) (n : Nat) (hn : n < fuel)
    (halted : Result)
    (hhalt : step M (traceState M n ⟨config, head⟩).config =
      .error halted) : halted.accept = true := by
  induction n generalizing fuel config head elapsed with
  | zero =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [evalFrom] at heval
          simp [traceState] at hhalt
          rw [hhalt] at heval
          simp only [Option.some.injEq] at heval
          subst result
          exact haccept
  | succ n ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [evalFrom] at heval
          cases hstep : step M config with
          | error first =>
              have hadvance : advanceState M ⟨config, head⟩ =
                  ⟨config, head⟩ := by simp [advanceState, hstep]
              have hsame := traceState_stutter M ⟨config, head⟩
                hadvance (n + 1)
              rw [hsame] at hhalt
              rw [hstep] at hhalt
              cases hhalt
              rw [hstep] at heval
              simp only [Option.some.injEq] at heval
              subst result
              exact haccept
          | ok next =>
              simp only [hstep] at heval
              rw [traceState] at hhalt
              have hconfig :
                  (advanceState M ⟨config, head⟩).config = next := by
                simp [advanceState, hstep]
              apply ih fuel next (advanceState M ⟨config, head⟩).head
                (elapsed + 1) heval (by omega)
              have hstate : advanceState M ⟨config, head⟩ =
                  { config := next,
                    head := (advanceState M ⟨config, head⟩).head } := by
                cases hs : advanceState M ⟨config, head⟩ with
                | mk c h =>
                    simp only [hs] at hconfig ⊢
                    subst c
                    rfl
              rw [← hstate]
              exact hhalt

private theorem acceptingControl_of_halt
    (M : Machine) (config : Config) (result : Result)
    (hstep : step M config = .error result)
    (haccept : result.accept = true) :
    acceptingControl M config.pc = true := by
  unfold step at hstep
  unfold acceptingControl
  cases hcode : M.code[config.pc]? with
  | none =>
      simp [hcode] at hstep
      cases hstep
      contradiction
  | some instruction =>
      cases instruction with
      | halt accept =>
          cases accept
          · simp [hcode] at hstep
            cases hstep
            contradiction
          · rfl
      | jump target => simp [hcode] at hstep
      | branch blank zero one =>
          cases hs : config.head with
          | none => simp [hcode, hs] at hstep
          | some bit => cases bit <;> simp [hcode, hs] at hstep
      | write symbol target => simp [hcode] at hstep
      | moveLeft target => simp [hcode] at hstep
      | moveRight target => simp [hcode] at hstep

private theorem positive_time_of_eval
    (M : Machine) (time : Nat) (input : Bitstring) (result : Result)
    (heval : eval M time input = some result) : 0 < time := by
  cases time with
  | zero => simp [eval, evalFrom] at heval
  | succ time => omega

def traceIndex (time row : Nat) : Nat := min row (time - 1)

def acceptingTraceState (inst : BoundedInstance) (row : Nat) : WindowState :=
  traceState inst.machine (traceIndex inst.time row)
    ⟨initial inst.input, inst.time⟩

def tableauOfEval (inst : BoundedInstance) (result : Result)
    (heval : eval inst.machine inst.time inst.input = some result)
    (haccept : result.accept = true) : LocalTableauData inst where
  control := fun time =>
    ⟨(acceptingTraceState inst time.1).config.pc,
      (code_valid_of_accepting_evalFrom inst.machine inst.time
        (initial inst.input) 0 result heval haccept
        (traceIndex inst.time time.1) inst.time
        (by
          have ht := positive_time_of_eval _ _ _ _ heval
          simp [traceIndex]
          omega)).trans_le (Nat.le_max_right _ _)⟩
  head := fun time =>
    ⟨(acceptingTraceState inst time.1).head, by
      have hb := traceState_head_bounds inst.machine
        (traceIndex inst.time time.1) inst.time
        ⟨initial inst.input, inst.time⟩ rfl
      simp only [acceptingTraceState]
      have hi : traceIndex inst.time time.1 ≤ inst.time := by
        simp [traceIndex]
      simp [localWidth]
      omega⟩
  tape := fun time position =>
    symbolCodeOf (configCell
      (acceptingTraceState inst time.1).config
      (acceptingTraceState inst time.1).head position.1)

private theorem acceptingTraceState_next
    (inst : BoundedInstance) (result : Result)
    (heval : eval inst.machine inst.time inst.input = some result)
    (haccept : result.accept = true) (k : Fin inst.time) :
    acceptingTraceState inst (k.1 + 1) =
      advanceState inst.machine (acceptingTraceState inst k.1) := by
  have htime := positive_time_of_eval _ _ _ _ heval
  by_cases hnext : k.1 + 1 < inst.time
  · simp only [acceptingTraceState]
    have hk : traceIndex inst.time k.1 = k.1 := by
      simp [traceIndex]
      omega
    have hk' : traceIndex inst.time (k.1 + 1) = k.1 + 1 := by
      simp [traceIndex]
      omega
    rw [hk, hk', traceState_succ]
  · have hk : k.1 = inst.time - 1 := by omega
    have hindex : traceIndex inst.time k.1 = inst.time - 1 := by
      simp [traceIndex, hk]
    have hindex' : traceIndex inst.time (k.1 + 1) =
        inst.time - 1 := by
      simp [traceIndex, hk]
    obtain ⟨halted, hhalt, _⟩ :=
      finalTrace_halts_of_accepting_evalFrom inst.machine inst.time
        (initial inst.input) inst.time 0 result heval haccept
    simp only [acceptingTraceState, hindex, hindex']
    simp [advanceState, hhalt]

theorem tableauOfEval_valid (inst : BoundedInstance) (result : Result)
    (heval : eval inst.machine inst.time inst.input = some result)
    (haccept : result.accept = true) :
    BoundedLocalAcceptingTableau inst
      (tableauOfEval inst result heval haccept) := by
  have htime := positive_time_of_eval _ _ _ _ heval
  let tableau := tableauOfEval inst result heval haccept
  refine
    { positiveTime := htime
      initialControl := ?_
      initialHead := ?_
      initialTape := ?_
      controlTransition := ?_
      tapeTransition := ?_
      accepting := ?_ }
  · simp [tableau, tableauOfEval, acceptingTraceState,
      traceIndex, traceState]
    cases inst.input <;> rfl
  · simp [tableau, tableauOfEval, acceptingTraceState,
      traceIndex, traceState]
  · intro position
    simp [tableau, tableauOfEval, acceptingTraceState,
      traceIndex, traceState, configCell_initial, initialSymbol]
  · intro k
    have hk : traceIndex inst.time k.1 = k.1 := by
      simp [traceIndex]
      omega
    let state := acceptingTraceState inst k.1
    have hnext := acceptingTraceState_next inst result heval haccept k
    have hpc : state.config.pc < inst.machine.code.size := by
      simpa [state, acceptingTraceState, hk] using
        code_valid_of_accepting_evalFrom inst.machine inst.time
        (initial inst.input) 0 result heval haccept k.1 inst.time k.2
    have hnextpc :
        (advanceState inst.machine state).config.pc <
          inst.machine.code.size := by
      rw [← hnext]
      exact code_valid_of_accepting_evalFrom inst.machine inst.time
        (initial inst.input) 0 result heval haccept
        (traceIndex inst.time (k.1 + 1)) inst.time (by
          simp [traceIndex]
          omega)
    have hb := traceState_head_bounds inst.machine k.1 inst.time
      ⟨initial inst.input, inst.time⟩ rfl
    have hleft : 0 < state.head := by
      simp only [state, acceptingTraceState, hk]
      omega
    have hright : state.head + 1 < localWidth inst := by
      simp only [state, acceptingTraceState, hk]
      simp [localWidth]
      omega
    have herror : ∀ halted,
        step inst.machine state.config = .error halted →
          halted.accept = true := by
      intro halted hhalt
      exact trace_error_accept_of_evalFrom inst.machine inst.time
        (initial inst.input) inst.time 0 result heval haccept k.1 k.2
        halted (by simpa [state, acceptingTraceState, hk] using hhalt)
    have hlegal := advanceState_localLegal inst state hpc hnextpc
      hleft hright herror
    simp only [tableauOfEval, symbolCodeOf_symbol, timeAt, timeNext,
      configCell_head]
    change controlHeadLegal inst state.config.pc state.config.head
      (acceptingTraceState inst (k.1 + 1)).config.pc
      (acceptingTraceState inst (k.1 + 1)).head state.head
    rw [hnext]
    exact hlegal.1
  · intro k position
    have hk : traceIndex inst.time k.1 = k.1 := by
      simp [traceIndex]
      omega
    let state := acceptingTraceState inst k.1
    have hnext := acceptingTraceState_next inst result heval haccept k
    have hpc : state.config.pc < inst.machine.code.size := by
      simpa [state, acceptingTraceState, hk] using
        code_valid_of_accepting_evalFrom inst.machine inst.time
        (initial inst.input) 0 result heval haccept k.1 inst.time k.2
    have hnextpc :
        (advanceState inst.machine state).config.pc <
          inst.machine.code.size := by
      rw [← hnext]
      exact code_valid_of_accepting_evalFrom inst.machine inst.time
        (initial inst.input) 0 result heval haccept
        (traceIndex inst.time (k.1 + 1)) inst.time (by
          simp [traceIndex]
          omega)
    have hb := traceState_head_bounds inst.machine k.1 inst.time
      ⟨initial inst.input, inst.time⟩ rfl
    have hleft : 0 < state.head := by
      simp only [state, acceptingTraceState, hk]
      omega
    have hright : state.head + 1 < localWidth inst := by
      simp only [state, acceptingTraceState, hk]
      simp [localWidth]
      omega
    have herror : ∀ halted,
        step inst.machine state.config = .error halted →
          halted.accept = true := by
      intro halted hhalt
      exact trace_error_accept_of_evalFrom inst.machine inst.time
        (initial inst.input) inst.time 0 result heval haccept k.1 k.2
        halted (by simpa [state, acceptingTraceState, hk] using hhalt)
    have hlegal := advanceState_localLegal inst state hpc hnextpc
      hleft hright herror
    simp only [tableauOfEval, symbolCodeOf_symbol, timeAt, timeNext]
    change tapeCellLegal inst state.config.pc state.head position.1
      (configCell state.config state.head position.1)
      (configCell (acceptingTraceState inst (k.1 + 1)).config
        (acceptingTraceState inst (k.1 + 1)).head position.1)
    rw [hnext]
    exact hlegal.2 position.1
  · obtain ⟨halted, hhalt, hhaltAccept⟩ :=
      finalTrace_halts_of_accepting_evalFrom inst.machine inst.time
        (initial inst.input) inst.time 0 result heval haccept
    have hac := acceptingControl_of_halt inst.machine
      (traceState inst.machine (inst.time - 1)
        ⟨initial inst.input, inst.time⟩).config halted hhalt hhaltAccept
    simpa [tableau, tableauOfEval, acceptingTime,
      acceptingTraceState, traceIndex] using hac

theorem accepts_implies_localTableauCNF_satisfiable
    (inst : BoundedInstance) :
    AcceptsWithin inst.machine inst.input inst.time →
      SAT.Satisfiable (localTableauCNF inst) := by
  rintro ⟨result, heval, haccept⟩
  apply (localTableauCNF_satisfiable_iff_tableau inst).mpr
  exact ⟨tableauOfEval inst result heval haccept,
    tableauOfEval_valid inst result heval haccept⟩

theorem localTableauCNF_satisfiable_iff_accepts
    (inst : BoundedInstance) :
    SAT.Satisfiable (localTableauCNF inst) ↔
      AcceptsWithin inst.machine inst.input inst.time :=
  ⟨localTableauCNF_satisfiable_implies_accepts inst,
    accepts_implies_localTableauCNF_satisfiable inst⟩

theorem localTableauCNFWithSource_satisfiable_iff_accepts
    (source : Bitstring) (inst : BoundedInstance) :
    SAT.Satisfiable (localTableauCNFWithSource source inst) ↔
      AcceptsWithin inst.machine inst.input inst.time := by
  rw [← localTableauCNF_satisfiable_iff_accepts inst]
  constructor
  · rintro ⟨assignment, hsatisfies⟩
    exact ⟨assignment,
      (assignment_iff_validLocalTableau inst assignment).mpr
        ((assignmentWithSource_iff_validLocalTableau
          source inst assignment).mp hsatisfies)⟩
  · rintro ⟨assignment, hsatisfies⟩
    exact ⟨assignment,
      (assignmentWithSource_iff_validLocalTableau
        source inst assignment).mpr
        ((assignment_iff_validLocalTableau inst assignment).mp hsatisfies)⟩

def localCNFSizeBound (n : Nat) : Nat :=
  200 * n ^ 5 + 200

theorem localCNFSizeBound_polynomial :
    IsPolynomial localCNFSizeBound := by
  refine .bounded 200 5 (fun n => ?_)
  simp [localCNFSizeBound]

private def cnfCost (formula : SAT.CNF) : Nat :=
  (formula.map (fun clause => clause.length + 1)).sum

@[simp] private theorem cnfCost_nil : cnfCost [] = 0 := rfl

@[simp] private theorem cnfCost_cons (clause : SAT.Clause) (formula : SAT.CNF) :
    cnfCost (clause :: formula) = clause.length + 1 + cnfCost formula := by
  simp [cnfCost]

private theorem cnfCost_map_singleton (xs : List α) (f : α → SAT.Literal) :
    cnfCost (xs.map fun x => [f x]) = 2 * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, cnfCost_cons]
      simp [ih]
      omega

private theorem satSize_eq_cost (formula : SAT.CNF) :
    SAT.size formula = 1 + cnfCost formula := by
  induction formula with
  | nil => simp [SAT.size, cnfCost]
  | cons clause formula ih =>
      simp [SAT.size_cons, cnfCost, ih]
      omega

private theorem cnfCost_append (first second : SAT.CNF) :
    cnfCost (first ++ second) = cnfCost first + cnfCost second := by
  simp [cnfCost]

private theorem cnfCost_flatMap_le
    (xs : List α) (f : α → SAT.CNF) (bound : Nat)
    (h : ∀ x ∈ xs, cnfCost (f x) ≤ bound) :
    cnfCost (xs.flatMap f) ≤ xs.length * bound := by
  induction xs with
  | nil => simp [cnfCost]
  | cons x xs ih =>
      simp only [List.flatMap_cons, cnfCost_append, List.length_cons]
      have hx := h x (by simp)
      have htail : ∀ y ∈ xs, cnfCost (f y) ≤ bound := by
        intro y hy
        exact h y (by simp [hy])
      have hi := ih htail
      calc
        cnfCost (f x) + cnfCost (List.flatMap f xs) ≤
            bound + xs.length * bound := Nat.add_le_add hx hi
        _ = (xs.length + 1) * bound := by
          simp [Nat.add_mul, Nat.add_comm]

private theorem cnfCost_filterMap_le
    (xs : List α) (f : α → Option SAT.Clause) (bound : Nat)
    (h : ∀ x ∈ xs, ∀ clause, f x = some clause →
      clause.length + 1 ≤ bound) :
    cnfCost (xs.filterMap f) ≤ xs.length * bound := by
  induction xs with
  | nil => simp [cnfCost]
  | cons x xs ih =>
      have htail : ∀ y ∈ xs, ∀ clause, f y = some clause →
          clause.length + 1 ≤ bound := by
        intro y hy
        exact h y (by simp [hy])
      have hi := ih htail
      cases hx : f x with
      | none =>
          simp only [List.filterMap_cons, hx, List.length_cons]
          calc
            cnfCost (List.filterMap f xs) ≤ xs.length * bound := hi
            _ ≤ (xs.length + 1) * bound := by
              simp [Nat.add_mul]
      | some clause =>
          have hc := h x (by simp) clause hx
          simp only [List.filterMap_cons, hx, cnfCost_cons, List.length_cons]
          calc
            clause.length + 1 + cnfCost (List.filterMap f xs) ≤
                bound + xs.length * bound := Nat.add_le_add hc hi
            _ = (xs.length + 1) * bound := by
              simp [Nat.add_mul, Nat.add_comm]

private theorem pairwiseClauses_cost_le (vars : List Nat) :
    cnfCost (pairwiseClauses vars) ≤ 3 * vars.length ^ 2 := by
  unfold pairwiseClauses
  have hinner : ∀ i ∈ vars,
      cnfCost (vars.filterMap fun j =>
        if i = j then none else some [.neg i, .neg j]) ≤
        3 * vars.length := by
    intro i _
    simpa [Nat.mul_comm] using cnfCost_filterMap_le vars
      (fun j => if i = j then none else
        some [.neg i, .neg j]) 3 (by
        intro j _ clause hclause
        split at hclause
        · contradiction
        · cases hclause
          simp)
  have h := cnfCost_flatMap_le vars
    (fun i => vars.filterMap fun j =>
      if i = j then none else some [.neg i, .neg j])
    (3 * vars.length) hinner
  simpa [Nat.pow_two, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

private theorem oneHotClauses_cost_le (vars : List Nat) :
    cnfCost (oneHotClauses vars) ≤
      vars.length + 1 + 3 * vars.length ^ 2 := by
  simp only [oneHotClauses, cnfCost, positiveClause,
    List.map_cons, List.sum_cons]
  have h := pairwiseClauses_cost_le vars
  simp [cnfCost] at h ⊢
  omega

private theorem rowOneHotClauses_cost_le
    (inst : BoundedInstance) (time : Nat) :
    cnfCost (rowOneHotClauses inst time) ≤
      controlCount inst.machine + 1 +
      3 * controlCount inst.machine ^ 2 +
      localWidth inst + 1 + 3 * localWidth inst ^ 2 +
      localWidth inst * 31 := by
  rw [rowOneHotClauses, cnfCost_append, cnfCost_append]
  have hpc := oneHotClauses_cost_le (pcVars inst time)
  have hhead := oneHotClauses_cost_le (headVars inst time)
  have hsymbols := cnfCost_flatMap_le
    (List.range (localWidth inst))
    (fun position => oneHotClauses (symbolVars inst time position)) 31
    (by
      intro position hposition
      have h := oneHotClauses_cost_le (symbolVars inst time position)
      simpa [symbolVars, allSymbols] using h)
  have hpc' : cnfCost (oneHotClauses (pcVars inst time)) ≤
      controlCount inst.machine + 1 +
        3 * controlCount inst.machine ^ 2 := by
    simpa [pcVars] using hpc
  have hhead' : cnfCost (oneHotClauses (headVars inst time)) ≤
      localWidth inst + 1 + 3 * localWidth inst ^ 2 := by
    simpa [headVars] using hhead
  simp only [List.length_range] at hsymbols
  omega

private theorem allOneHotClauses_cost_le (inst : BoundedInstance) :
    cnfCost (allOneHotClauses inst) ≤
      (inst.time + 1) *
        (controlCount inst.machine + 1 +
        3 * controlCount inst.machine ^ 2 +
        localWidth inst + 1 + 3 * localWidth inst ^ 2 +
        localWidth inst * 31) := by
  unfold allOneHotClauses
  simpa using cnfCost_flatMap_le (List.range (inst.time + 1))
    (rowOneHotClauses inst) _
    (fun time _ => rowOneHotClauses_cost_le inst time)

private theorem controlTransitionClausesAt_cost_le
    (inst : BoundedInstance) (time : Nat) :
    cnfCost (controlTransitionClausesAt inst time) ≤
      18 * controlCount inst.machine ^ 2 * localWidth inst ^ 2 := by
  unfold controlTransitionClausesAt
  have hout := cnfCost_flatMap_le
    (List.range (controlCount inst.machine)) _ _
    (by
      intro control _
      have hnext := cnfCost_flatMap_le
        (List.range (controlCount inst.machine)) _ _
        (by
          intro nextControl _
          have hhead := cnfCost_flatMap_le
            (List.range (localWidth inst)) _ _
            (by
              intro head _
              have hlast := cnfCost_flatMap_le
                (List.range (localWidth inst))
                (fun nextHead =>
                  allSymbols.filterMap fun scanned =>
                    if controlHeadLegal inst control scanned.symbol
                        nextControl nextHead head then none
                    else some (negativeClause
                      [pcVar inst time control,
                       pcVar inst (time + 1) nextControl,
                       headVar inst time head,
                       headVar inst (time + 1) nextHead,
                       symbolVar inst time head scanned])) 18
                (by
                  intro nextHead _
                  apply cnfCost_filterMap_le allSymbols _ 6
                  intro scanned _ clause hclause
                  split at hclause
                  · contradiction
                  · cases hclause
                    simp [negativeClause])
              simpa [Nat.mul_comm] using hlast)
          simpa [Nat.pow_two, Nat.mul_assoc] using hhead)
      simpa [Nat.pow_two, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm] using hnext)
  simpa [Nat.pow_two, Nat.mul_assoc, Nat.mul_comm,
    Nat.mul_left_comm] using hout

private theorem tapeTransitionClausesAt_cost_le
    (inst : BoundedInstance) (time : Nat) :
    cnfCost (tapeTransitionClausesAt inst time) ≤
      45 * controlCount inst.machine * localWidth inst ^ 2 := by
  unfold tapeTransitionClausesAt
  have hout := cnfCost_flatMap_le
    (List.range (controlCount inst.machine)) _ _
    (by
      intro control _
      have hhead := cnfCost_flatMap_le
        (List.range (localWidth inst)) _ _
        (by
          intro head _
          have hposition := cnfCost_flatMap_le
            (List.range (localWidth inst))
            (fun position =>
              allSymbols.flatMap fun old =>
              allSymbols.filterMap fun new =>
                if tapeCellLegal inst control head position
                    old.symbol new.symbol then none
                else some (negativeClause
                  [pcVar inst time control,
                   headVar inst time head,
                   symbolVar inst time position old,
                   symbolVar inst (time + 1) position new])) 45
            (by
              intro position _
              have hold := cnfCost_flatMap_le allSymbols
                (fun old =>
                  allSymbols.filterMap fun new =>
                    if tapeCellLegal inst control head position
                        old.symbol new.symbol then none
                    else some (negativeClause
                      [pcVar inst time control,
                       headVar inst time head,
                       symbolVar inst time position old,
                       symbolVar inst (time + 1) position new])) 15
                (by
                  intro old _
                  apply cnfCost_filterMap_le allSymbols _ 5
                  intro new _ clause hclause
                  split at hclause
                  · contradiction
                  · cases hclause
                    simp [negativeClause])
              simpa [allSymbols] using hold)
          simpa [Nat.mul_comm] using hposition)
      simpa [Nat.pow_two, Nat.mul_assoc] using hhead)
  simpa [Nat.pow_two, Nat.mul_assoc, Nat.mul_comm,
    Nat.mul_left_comm] using hout

private theorem allTransitionClauses_cost_le (inst : BoundedInstance) :
    cnfCost (allTransitionClauses inst) ≤
      inst.time * (18 * controlCount inst.machine ^ 2 *
        localWidth inst ^ 2 +
        45 * controlCount inst.machine * localWidth inst ^ 2) := by
  unfold allTransitionClauses transitionClausesAt
  simpa using cnfCost_flatMap_le (List.range inst.time) _ _
    (by
      intro time _
      rw [cnfCost_append]
      exact Nat.add_le_add
        (controlTransitionClausesAt_cost_le inst time)
        (tapeTransitionClausesAt_cost_le inst time))

def localCNFParameter (inst : BoundedInstance) : Nat :=
  (encodeBoundedInstance inst).length + inst.time +
    controlCount inst.machine + localWidth inst + 1

def localInputSize (inst : BoundedInstance) : Nat :=
  machineWireSize inst.machine + inst.machine.code.size +
    4 * inst.input.length + 4 * inst.time + 6

theorem localCNFParameter_le_inputSize (inst : BoundedInstance) :
    localCNFParameter inst ≤ localInputSize inst := by
  have hsource := encodeBoundedInstance_length_le inst
  simp [localCNFParameter, localInputSize, localWidth, controlCount] at *
  omega

/-- Concrete structural bound in machine/source bits, unary time, and window width. -/
theorem localTableauCNF_size_le (inst : BoundedInstance) :
    SAT.size (localTableauCNF inst) ≤
      localCNFSizeBound (localCNFParameter inst) := by
  have hhot := allOneHotClauses_cost_le inst
  have htrans := allTransitionClauses_cost_le inst
  have hsource :
      cnfCost (sourceBlock inst) ≤
        4 * (encodeBoundedInstance inst).length + 3 := by
    rw [sourceBlock, sourceBlockBits, cnfCost_append]
    have hmap : cnfCost
        ((encodeBoundedInstance inst).zipIdx.map
          (fun entry => sourceClause (entry.2, entry.1))) ≤
        (encodeBoundedInstance inst).zipIdx.length * 4 := by
      induction (encodeBoundedInstance inst).zipIdx with
      | nil => simp [cnfCost]
      | cons entry entries ih =>
          rw [List.map_cons, cnfCost_cons]
          simp only [sourceClause, List.length_cons, List.length_nil]
          calc
            3 + 1 + cnfCost
                (List.map (fun entry => sourceClause (entry.2, entry.1)) entries) ≤
                4 + entries.length * 4 := Nat.add_le_add_left ih 4
            _ = (entries.length + 1) * 4 := by
              simp [Nat.add_mul, Nat.add_comm]
    rw [cnfCost_cons, cnfCost_nil]
    simpa [sourceDelimiter, Nat.mul_comm] using
      Nat.add_le_add_right hmap 3
  have hinitial :
      cnfCost (initialClauses inst) ≤ 2 * localWidth inst + 4 := by
    rw [initialClauses, cnfCost_append]
    rw [cnfCost_map_singleton]
    simp [cnfCost]
    omega
  have hfinal :
      cnfCost (finalClauses inst) ≤ controlCount inst.machine + 1 := by
    unfold finalClauses
    split
    · simp [cnfCost]
    · simp [cnfCost]
      simpa using List.length_filterMap_le
        (fun control =>
          if acceptingControl inst.machine control then
            some (SAT.Literal.pos (pcVar inst (inst.time - 1) control))
          else none)
        (List.range (controlCount inst.machine))
  rw [satSize_eq_cost, localTableauCNF, cnfCost_append,
    cnfCost_append, cnfCost_append, cnfCost_append]
  let N := localCNFParameter inst
  have hN : 1 ≤ N := by
    simp [N, localCNFParameter]
  have hs : (encodeBoundedInstance inst).length ≤ N := by
    simp [N, localCNFParameter]
    omega
  have ht : inst.time ≤ N := by
    simp [N, localCNFParameter]
    omega
  have hc : controlCount inst.machine ≤ N := by
    simp [N, localCNFParameter]
    omega
  have hw : localWidth inst ≤ N := by
    simp [N, localCNFParameter]
    omega
  have hc2 := Nat.pow_le_pow_left hc 2
  have hw2 := Nat.pow_le_pow_left hw 2
  have hinside :
      controlCount inst.machine + 1 +
        3 * controlCount inst.machine ^ 2 +
        localWidth inst + 1 + 3 * localWidth inst ^ 2 +
        localWidth inst * 31 ≤ 41 * N ^ 2 := by
    nlinarith
  have htime : inst.time + 1 ≤ 2 * N := by omega
  have hhot' : cnfCost (allOneHotClauses inst) ≤ 82 * N ^ 3 := by
    calc
      cnfCost (allOneHotClauses inst) ≤ _ := hhot
      _ ≤ 82 * N ^ 3 := by
        have := Nat.mul_le_mul htime hinside
        nlinarith
  have htrans' : cnfCost (allTransitionClauses inst) ≤ 63 * N ^ 5 := by
    calc
      cnfCost (allTransitionClauses inst) ≤ _ := htrans
      _ ≤ 63 * N ^ 5 := by
        have hfirst := Nat.mul_le_mul
          (Nat.mul_le_mul hc2 hw2) (by omega : 18 ≤ 18)
        have hsecond := Nat.mul_le_mul
          (Nat.mul_le_mul hc hw2) (by omega : 45 ≤ 45)
        nlinarith
  change 1 +
      (cnfCost (sourceBlock inst) +
        (cnfCost (allOneHotClauses inst) +
          cnfCost (initialClauses inst) +
          cnfCost (allTransitionClauses inst) +
          cnfCost (finalClauses inst))) ≤ localCNFSizeBound N
  simp only [localCNFSizeBound]
  have hN5 := Nat.pow_le_pow_right (by omega : 0 < N)
    (by omega : 1 ≤ 5)
  have hN3 := Nat.pow_le_pow_right (by omega : 0 < N)
    (by omega : 3 ≤ 5)
  nlinarith [hsource, hinitial, hfinal, hhot', htrans', hN5, hN3]

/-- Every source bit is charged by its own constant-size provenance clause. -/
theorem localTableauCNF_honest (inst : BoundedInstance) :
    (encodeBoundedInstance inst).length ≤ SAT.size (localTableauCNF inst) := by
  have hlength :
      (encodeBoundedInstance inst).length ≤
        (localTableauCNF inst).length := by
    simp [localTableauCNF, sourceBlock, sourceBlockBits]
  simp [SAT.size]
  omega

/--
The structural bound expressed only through machine wire/code length, input
length, and the unary time value.
-/
theorem localTableauCNF_size_le_inputSize (inst : BoundedInstance) :
    SAT.size (localTableauCNF inst) ≤
      localCNFSizeBound (localInputSize inst) := by
  exact (localTableauCNF_size_le inst).trans (by
    unfold localCNFSizeBound
    have h := Nat.pow_le_pow_left (localCNFParameter_le_inputSize inst) 5
    nlinarith)

end AvgCaseMls.Section4.CookLevin
