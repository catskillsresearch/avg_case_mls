import AvgCaseMls.EMLS
import AvgCaseMls.Foundation.Codec

/-!
# A self-delimiting wire codec for elementary MLS

Natural variable names use the Foundation binary codec.  Consequently the
wire size below charges every bit used to represent every variable name.
-/

namespace AvgCaseMls.EMLSCodec

open AvgCaseMls.Foundation
open MLS.EMLS

def encodeBinOp : BinOp → Bitstring
  | .union => [false, false]
  | .inter => [false, true]
  | .diff => [true, false]

def decodeBinOp? : Bitstring → Option (BinOp × Bitstring)
  | false :: false :: rest => some (.union, rest)
  | false :: true :: rest => some (.inter, rest)
  | true :: false :: rest => some (.diff, rest)
  | _ => none

@[simp] theorem decodeBinOp?_suffix (op : BinOp) (rest : Bitstring) :
    decodeBinOp? (encodeBinOp op ++ rest) = some (op, rest) := by
  cases op <;> rfl

def encodeLiteral : Literal → Bitstring
  | .eqOp x y z op =>
      [false, false, false] ++ encodeNat x ++ encodeNat y ++ encodeNat z ++
        encodeBinOp op
  | .eqEmpty x => [false, false, true] ++ encodeNat x
  | .mem x y => [false, true, false] ++ encodeNat x ++ encodeNat y
  | .notMem x y => [false, true, true] ++ encodeNat x ++ encodeNat y
  | .neq x y => [true, false, false] ++ encodeNat x ++ encodeNat y

def decodeLiteral? : Bitstring → Option (Literal × Bitstring)
  | false :: false :: false :: bits => do
      let (x, bits) ← decodeNat? bits
      let (y, bits) ← decodeNat? bits
      let (z, bits) ← decodeNat? bits
      let (op, bits) ← decodeBinOp? bits
      some (.eqOp x y z op, bits)
  | false :: false :: true :: bits => do
      let (x, bits) ← decodeNat? bits
      some (.eqEmpty x, bits)
  | false :: true :: false :: bits => do
      let (x, bits) ← decodeNat? bits
      let (y, bits) ← decodeNat? bits
      some (.mem x y, bits)
  | false :: true :: true :: bits => do
      let (x, bits) ← decodeNat? bits
      let (y, bits) ← decodeNat? bits
      some (.notMem x y, bits)
  | true :: false :: false :: bits => do
      let (x, bits) ← decodeNat? bits
      let (y, bits) ← decodeNat? bits
      some (.neq x y, bits)
  | _ => none

@[simp] theorem decodeLiteral?_suffix (literal : Literal) (rest : Bitstring) :
    decodeLiteral? (encodeLiteral literal ++ rest) = some (literal, rest) := by
  cases literal with
  | eqOp x y z op =>
      simp [encodeLiteral, decodeLiteral?, decodeNat?_suffix,
        decodeBinOp?_suffix, List.append_assoc]
  | eqEmpty x =>
      simp [encodeLiteral, decodeLiteral?, decodeNat?_suffix]
  | mem x y | notMem x y | neq x y =>
      simp [encodeLiteral, decodeLiteral?, decodeNat?_suffix,
        List.append_assoc]

def literalWireSize : Literal → Nat
  | .eqOp x y z _ =>
      5 + (encodeNat x).length + (encodeNat y).length + (encodeNat z).length
  | .eqEmpty x => 3 + (encodeNat x).length
  | .mem x y | .notMem x y | .neq x y =>
      3 + (encodeNat x).length + (encodeNat y).length

@[simp] theorem encodeLiteral_length (literal : Literal) :
    (encodeLiteral literal).length = literalWireSize literal := by
  cases literal with
  | eqOp x y z op =>
      cases op <;> simp [encodeLiteral, literalWireSize, encodeBinOp] <;> omega
  | eqEmpty x => simp [encodeLiteral, literalWireSize] <;> omega
  | mem x y | notMem x y | neq x y =>
      simp [encodeLiteral, literalWireSize] <;> omega

def encodeLiterals : Conjunct → Bitstring
  | [] => []
  | literal :: literals => encodeLiteral literal ++ encodeLiterals literals

def decodeLiterals? : Nat → Bitstring → Option (Conjunct × Bitstring)
  | 0, bits => some ([], bits)
  | count + 1, bits => do
      let (literal, bits) ← decodeLiteral? bits
      let (literals, bits) ← decodeLiterals? count bits
      some (literal :: literals, bits)

@[simp] theorem decodeLiterals?_suffix (literals : Conjunct) (rest : Bitstring) :
    decodeLiterals? literals.length (encodeLiterals literals ++ rest) =
      some (literals, rest) := by
  induction literals with
  | nil => rfl
  | cons literal literals ih =>
      simp [encodeLiterals, decodeLiterals?, decodeLiteral?_suffix, ih]

def conjunctWireSize (conjunct : Conjunct) : Nat :=
  (encodeNat conjunct.length).length +
    (conjunct.map literalWireSize).sum

def encodeConjunct (conjunct : Conjunct) : Bitstring :=
  encodeNat conjunct.length ++ encodeLiterals conjunct

def decodeConjunct? (bits : Bitstring) : Option Conjunct := do
  let (count, bits) ← decodeNat? bits
  let (conjunct, rest) ← decodeLiterals? count bits
  if rest = [] then some conjunct else none

@[simp] theorem decodeConjunct?_encode (conjunct : Conjunct) :
    decodeConjunct? (encodeConjunct conjunct) = some conjunct := by
  unfold decodeConjunct? encodeConjunct
  rw [decodeNat?_suffix]
  have h :
      decodeLiterals? conjunct.length (encodeLiterals conjunct) =
        some (conjunct, []) := by
    simpa using decodeLiterals?_suffix conjunct []
  simp [h]

theorem encodeConjunct_injective : Function.Injective encodeConjunct := by
  intro first second h
  have := congrArg decodeConjunct? h
  simpa using this

private theorem encodeLiterals_length (literals : Conjunct) :
    (encodeLiterals literals).length =
      (literals.map literalWireSize).sum := by
  induction literals with
  | nil => rfl
  | cons literal literals ih =>
      simp [encodeLiterals, encodeLiteral_length, ih]

@[simp] theorem encodeConjunct_length (conjunct : Conjunct) :
    (encodeConjunct conjunct).length = conjunctWireSize conjunct := by
  simp [encodeConjunct, conjunctWireSize, encodeLiterals_length]

private theorem literalWireSize_pos (literal : Literal) :
    0 < literalWireSize literal := by
  cases literal <;> simp [literalWireSize]

theorem conjunct_length_le_wireSize (conjunct : Conjunct) :
    conjunct.length ≤ conjunctWireSize conjunct := by
  unfold conjunctWireSize
  have hbody :
      conjunct.length ≤ (conjunct.map literalWireSize).sum := by
    induction conjunct with
    | nil => simp
    | cons literal conjunct ih =>
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        have := literalWireSize_pos literal
        omega
  exact hbody.trans (Nat.le_add_left _ _)

theorem conjunct_length_le_encode (conjunct : Conjunct) :
    conjunct.length ≤ (encodeConjunct conjunct).length := by
  rw [encodeConjunct_length]
  exact conjunct_length_le_wireSize conjunct

/-- The standard language of well-formed serialized satisfiable EMLS conjuncts. -/
def EncodedEMLSSAT : Set Bitstring :=
  { bits | ∃ conjunct,
      decodeConjunct? bits = some conjunct ∧
      ∃ env : MLS.Env, ∀ literal ∈ conjunct, Literal.holds env literal }

@[simp] theorem encode_mem_encodedEMLSSAT (conjunct : Conjunct) :
    encodeConjunct conjunct ∈ EncodedEMLSSAT ↔
      ∃ env : MLS.Env, ∀ literal ∈ conjunct, Literal.holds env literal := by
  constructor
  · rintro ⟨decoded, hdecode, hsatisfiable⟩
    rw [decodeConjunct?_encode] at hdecode
    cases hdecode
    exact hsatisfiable
  · intro hsatisfiable
    exact ⟨conjunct, decodeConjunct?_encode conjunct, hsatisfiable⟩

end AvgCaseMls.EMLSCodec
