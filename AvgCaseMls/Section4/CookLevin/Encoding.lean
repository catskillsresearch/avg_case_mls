import AvgCaseMls.Foundation.Serialization
import AvgCaseMls.Section4.CookLevin.Tableau

/-!
# Encoded bounded machine instances

The source of the Cook--Levin map is a serialized machine, input, and unary
time-bound parameter.  The decoder is syntax directed and proves injectivity
of the complete source encoding, rather than relying on a custom image
language.
-/

namespace AvgCaseMls.Section4.CookLevin

open AvgCaseMls.Foundation

structure BoundedInstance where
  machine : Machine
  input : Bitstring
  time : Nat
  deriving DecidableEq, Repr

def encodeUnaryTime (time : Nat) : Bitstring :=
  List.replicate time false ++ [true]

private def decodeUnaryTimeFrom : Bitstring → Nat → Option (Nat × Bitstring)
  | [], _ => none
  | false :: rest, count => decodeUnaryTimeFrom rest (count + 1)
  | true :: rest, count => some (count, rest)

def decodeUnaryTime? (bits : Bitstring) : Option (Nat × Bitstring) :=
  decodeUnaryTimeFrom bits 0

private theorem decodeUnaryTimeFrom_replicate (time count : Nat)
    (rest : Bitstring) :
    decodeUnaryTimeFrom
      (List.replicate time false ++ true :: rest) count =
      some (count + time, rest) := by
  induction time generalizing count with
  | zero => simp [decodeUnaryTimeFrom]
  | succ time ih =>
      simp only [List.replicate_succ, List.cons_append, decodeUnaryTimeFrom]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (count + 1)

@[simp] theorem decodeUnaryTime?_encode (time : Nat) :
    decodeUnaryTime? (encodeUnaryTime time) = some (time, []) := by
  simp [decodeUnaryTime?, encodeUnaryTime, decodeUnaryTimeFrom_replicate]

@[simp] theorem encodeUnaryTime_length (time : Nat) :
    (encodeUnaryTime time).length = time + 1 := by
  simp [encodeUnaryTime]

def encodeBoundedInstance (inst : BoundedInstance) : Bitstring :=
  encodeMachine inst.machine ++
    encodeNat inst.input.length ++ inst.input ++
    encodeUnaryTime inst.time

def decodeBoundedInstance? (bits : Bitstring) : Option BoundedInstance := do
  let (machine, rest) ← decodeMachine? bits
  let (width, payload) ← decodeNat? rest
  if _hwidth : width ≤ payload.length then
    let input := payload.take width
    let trailer := payload.drop width
    let (time, remainder) ← decodeUnaryTime? trailer
    if remainder = [] then
      some ⟨machine, input, time⟩
    else
      none
  else
    none

@[simp] theorem decodeBoundedInstance?_encode (inst : BoundedInstance) :
    decodeBoundedInstance? (encodeBoundedInstance inst) = some inst := by
  cases inst with
  | mk machine input time =>
      simp [encodeBoundedInstance, decodeBoundedInstance?,
        decodeMachine?_suffix, decodeNat?_suffix]

theorem encodeBoundedInstance_injective :
    Function.Injective encodeBoundedInstance := by
  intro first second h
  have := congrArg decodeBoundedInstance? h
  simpa using this

/-- The actual language represented by encoded bounded machine instances. -/
def EncodedBoundedAcceptance : Set Bitstring :=
  { bits | ∃ inst,
      decodeBoundedInstance? bits = some inst ∧
      AcceptsWithin inst.machine inst.input inst.time }

@[simp] theorem encode_mem_encodedBoundedAcceptance
    (inst : BoundedInstance) :
    encodeBoundedInstance inst ∈ EncodedBoundedAcceptance ↔
      AcceptsWithin inst.machine inst.input inst.time := by
  constructor
  · rintro ⟨decoded, hdecode, haccepts⟩
    rw [decodeBoundedInstance?_encode] at hdecode
    cases hdecode
    exact haccepts
  · intro haccepts
    exact ⟨inst, decodeBoundedInstance?_encode inst, haccepts⟩

theorem encode_mem_iff_tableau (inst : BoundedInstance) :
    encodeBoundedInstance inst ∈ EncodedBoundedAcceptance ↔
      ∃ rows, BoundedAcceptingTableau inst.machine inst.input
        inst.time rows := by
  rw [encode_mem_encodedBoundedAcceptance, acceptsWithin_iff_tableau]

/-- A direct size account for the valid provenance/source block. -/
theorem encodeBoundedInstance_length_le (inst : BoundedInstance) :
    (encodeBoundedInstance inst).length ≤
      machineWireSize inst.machine +
        3 * inst.input.length + inst.time + 2 := by
  simp only [encodeBoundedInstance, List.length_append]
  change machineWireSize inst.machine +
      (encodeNat inst.input.length).length + inst.input.length +
      (encodeUnaryTime inst.time).length ≤ _
  have hinput := length_encodeNat_le inst.input.length
  rw [encodeUnaryTime_length]
  omega

end AvgCaseMls.Section4.CookLevin
