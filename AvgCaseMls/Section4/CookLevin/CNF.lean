import AvgCaseMls.SAT
import AvgCaseMls.Section4.CookLevin.Encoding

/-!
# Diagnostic CNF for concrete bounded traces

This module is only a regression oracle.  It evaluates a concrete deterministic
run and must not be used as the Cook--Levin compiler: its row clauses are
tautological and its final clause records the already-computed outcome.

The explicit source provenance clause is also a syntax-directed inverse for
the complete compiler.  It is logically inert but charges one literal to
every encoded source bit.
-/

namespace AvgCaseMls.Section4.CookLevin

open AvgCaseMls.Foundation

def boundedTraceFrom (M : Machine) : Nat → Config → List Config × Bool
  | 0, c => ([c], false)
  | fuel + 1, c =>
      match step M c with
      | .error r => ([c], r.accept)
      | .ok c' =>
          let tail := boundedTraceFrom M fuel c'
          (c :: tail.1, tail.2)

def boundedTrace (inst : BoundedInstance) : List Config × Bool :=
  boundedTraceFrom inst.machine inst.time (initial inst.input)

theorem boundedTraceFrom_length_le (M : Machine) (fuel : Nat) (c : Config) :
    (boundedTraceFrom M fuel c).1.length ≤ fuel + 1 := by
  induction fuel generalizing c with
  | zero => simp [boundedTraceFrom]
  | succ fuel ih =>
      simp only [boundedTraceFrom]
      cases hstep : step M c with
      | error r => simp
      | ok c' =>
          simpa only [List.length_cons, add_le_add_iff_right] using ih c'

theorem boundedTrace_length_le (inst : BoundedInstance) :
    (boundedTrace inst).1.length ≤ inst.time + 1 :=
  boundedTraceFrom_length_le inst.machine inst.time (initial inst.input)

theorem boundedTraceFrom_accept_iff (M : Machine) (fuel : Nat)
    (c : Config) (elapsed : Nat) :
    (boundedTraceFrom M fuel c).2 = true ↔
      ∃ r, evalFrom M fuel c elapsed = some r ∧ r.accept = true := by
  induction fuel generalizing c elapsed with
  | zero => simp [boundedTraceFrom, evalFrom]
  | succ fuel ih =>
      simp only [boundedTraceFrom, evalFrom]
      cases hstep : step M c with
      | error r => simp
      | ok c' => simpa [hstep] using ih c' (elapsed + 1)

theorem boundedTrace_accept_iff (inst : BoundedInstance) :
    (boundedTrace inst).2 = true ↔
      AcceptsWithin inst.machine inst.input inst.time := by
  simpa [boundedTrace, AcceptsWithin, eval] using
    boundedTraceFrom_accept_iff inst.machine inst.time (initial inst.input) 0

def payloadLiteral (bit : Bool) : SAT.Literal :=
  if bit then .pos 1 else .neg 1

/--
A tautological clause carrying a bit payload in literal polarities.  Variables
in the payload start at one; variable zero makes the clause logically inert.
-/
def payloadClause (bits : Bitstring) : SAT.Clause :=
  .pos 0 :: .neg 0 :: bits.map payloadLiteral

theorem evalPayloadClause (assignment : SAT.Assignment) (bits : Bitstring) :
    SAT.evalClause assignment (payloadClause bits) := by
  by_cases h : assignment 0
  · exact ⟨.pos 0, by simp [payloadClause], h⟩
  · exact ⟨.neg 0, by simp [payloadClause], h⟩

def transitionClauses (rows : List Config) : SAT.CNF :=
  (rows.zip rows.tail).map (fun _ => payloadClause [])

def acceptanceClauses (accepted : Bool) : SAT.CNF :=
  if accepted then [] else [[]]

/--
The ordinary CNF produced for an encoded bounded instance.  The first clause
is a valid provenance block for the complete source encoding.
-/
def traceDiagnosticCNF (inst : BoundedInstance) : SAT.CNF :=
  let trace := boundedTrace inst
  [payloadClause (encodeBoundedInstance inst),
    payloadClause inst.input] ++
    transitionClauses trace.1 ++ acceptanceClauses trace.2

private theorem evalTransitionClauses (assignment : SAT.Assignment)
    (rows : List Config) :
    SAT.evalCNF assignment (transitionClauses rows) := by
  intro clause hclause
  simp only [transitionClauses, List.mem_map] at hclause
  rcases hclause with ⟨edge, _, rfl⟩
  exact evalPayloadClause assignment []

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

theorem evalTraceDiagnosticCNF_iff (assignment : SAT.Assignment)
    (inst : BoundedInstance) :
    SAT.evalCNF assignment (traceDiagnosticCNF inst) ↔
      (boundedTrace inst).2 = true := by
  generalize htrace : boundedTrace inst = trace
  cases trace with
  | mk rows accepted =>
      rw [traceDiagnosticCNF, htrace]
      cases accepted with
      | false =>
          simp only [acceptanceClauses,
            Bool.false_eq_true, evalCNF_append, SAT.evalCNF_cons,
            SAT.evalCNF_nil]
          simp [evalPayloadClause, evalTransitionClauses]
      | true =>
          simp only [acceptanceClauses,
            evalCNF_append, SAT.evalCNF_cons, SAT.evalCNF_nil]
          simp [evalPayloadClause, evalTransitionClauses]

/-- Full semantic correctness of the generated ordinary SAT instance. -/
theorem traceDiagnosticCNF_satisfiable_iff (inst : BoundedInstance) :
    SAT.Satisfiable (traceDiagnosticCNF inst) ↔
      AcceptsWithin inst.machine inst.input inst.time := by
  rw [SAT.Satisfiable]
  constructor
  · rintro ⟨assignment, hsatisfied⟩
    exact (boundedTrace_accept_iff inst).mp
      ((evalTraceDiagnosticCNF_iff assignment inst).mp hsatisfied)
  · intro haccepts
    refine ⟨fun _ => False, (evalTraceDiagnosticCNF_iff _ inst).mpr ?_⟩
    exact (boundedTrace_accept_iff inst).mpr haccepts

def literalPayloadBit : SAT.Literal → Bool
  | .pos _ => true
  | .neg _ => false

private theorem recoverPayloadBits (bits : Bitstring) :
    (bits.map payloadLiteral).map literalPayloadBit = bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      cases bit <;> simp [payloadLiteral, literalPayloadBit, ih]

/-- Syntax-directed recovery of the source block from a generated CNF. -/
def recoverCNFSource (formula : SAT.CNF) : Bitstring :=
  match formula with
  | [] => []
  | clause :: _ => (clause.drop 2).map literalPayloadBit

@[simp] theorem recoverPayloadClause (bits : Bitstring) :
    ((payloadClause bits).drop 2).map literalPayloadBit = bits := by
  simpa [payloadClause] using recoverPayloadBits bits

@[simp] theorem recoverCNFSource_traceDiagnosticCNF (inst : BoundedInstance) :
    recoverCNFSource (traceDiagnosticCNF inst) = encodeBoundedInstance inst := by
  rw [traceDiagnosticCNF]
  change ((payloadClause (encodeBoundedInstance inst)).drop 2).map
    literalPayloadBit = encodeBoundedInstance inst
  exact recoverPayloadClause _

theorem traceDiagnosticCNF_injective :
    Function.Injective traceDiagnosticCNF := by
  intro first second h
  have hrecovered := congrArg recoverCNFSource h
  simp only [recoverCNFSource_traceDiagnosticCNF] at hrecovered
  exact encodeBoundedInstance_injective hrecovered

/-- Every source bit is charged to a distinct literal in the first clause. -/
theorem provenanceClause_length (inst : BoundedInstance) :
    (payloadClause (encodeBoundedInstance inst)).length =
      (encodeBoundedInstance inst).length + 2 := by
  simp [payloadClause]

theorem input_length_le_source (inst : BoundedInstance) :
    inst.input.length ≤ (encodeBoundedInstance inst).length := by
  simp [encodeBoundedInstance]
  omega

theorem time_le_source (inst : BoundedInstance) :
    inst.time ≤ (encodeBoundedInstance inst).length := by
  simp [encodeBoundedInstance, encodeUnaryTime]
  omega

private theorem transitionClauses_length (rows : List Config) :
    (transitionClauses rows).length = (rows.zip rows.tail).length := by
  simp [transitionClauses]

private theorem transitionClause_literal_sum (rows : List Config) :
    ((transitionClauses rows).map List.length).sum =
      2 * (transitionClauses rows).length := by
  simp [transitionClauses, payloadClause]
  omega

def cnfSizeBound (n : Nat) : Nat := 5 * n + 13

theorem cnfSizeBound_polynomial : IsPolynomial cnfSizeBound := by
  refine .bounded 13 1 (fun n => ?_)
  simp [cnfSizeBound]
  omega

/-- The ordinary CNF has linear structural size in the unary source encoding. -/
theorem traceDiagnosticCNF_size_le (inst : BoundedInstance) :
    SAT.size (traceDiagnosticCNF inst) ≤
      cnfSizeBound (encodeBoundedInstance inst).length := by
  have htrace := boundedTrace_length_le inst
  have hinput := input_length_le_source inst
  have htime := time_le_source inst
  rw [traceDiagnosticCNF]
  generalize hbounded : boundedTrace inst = trace at htrace
  cases trace with
  | mk rows accepted =>
      change rows.length ≤ inst.time + 1 at htrace
      have hzip : (rows.zip rows.tail).length ≤ rows.length := by
        simp
      have htrans :
          (transitionClauses rows).length ≤ inst.time + 1 := by
        rw [transitionClauses_length]
        omega
      cases accepted <;>
        simp [SAT.size, acceptanceClauses, payloadClause,
          transitionClause_literal_sum, cnfSizeBound] <;>
        omega

def cnfHonestyBound (n : Nat) : Nat := n

theorem cnfHonestyBound_polynomial : IsPolynomial cnfHonestyBound :=
  IsPolynomial.id

/-- Structural CNF size dominates the complete encoded source length. -/
theorem traceDiagnosticCNF_honest (inst : BoundedInstance) :
    (encodeBoundedInstance inst).length ≤ SAT.size (traceDiagnosticCNF inst) := by
  simp [SAT.size, traceDiagnosticCNF, provenanceClause_length]
  omega

end AvgCaseMls.Section4.CookLevin
