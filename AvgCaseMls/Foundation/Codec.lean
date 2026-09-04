/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.Foundation.Complexity
import Mathlib.Tactic

namespace AvgCaseMls.Foundation

/-- Interpret a least-significant-bit-first binary word. -/
def decodeBinaryPayload : Bitstring → Nat
  | [] => 0
  | b :: bits => Nat.bit b (decodeBinaryPayload bits)

theorem decodeBinaryPayload_bits (n : Nat) :
    decodeBinaryPayload (Nat.bits n) = n := by
  induction n using Nat.binaryRec with
  | zero => simp [Nat.bits, decodeBinaryPayload]
  | bit b n ih =>
      by_cases hn : n = 0
      · subst n
        cases b <;> simp [Nat.bits, Nat.bit, decodeBinaryPayload]
      · rw [Nat.bits, Nat.binaryRec_eq b n (Or.inr (fun h => (hn h).elim))]
        change Nat.bit b
          (decodeBinaryPayload (Nat.binaryRec [] (fun b _ ih => b :: ih) n)) =
          Nat.bit b n
        change decodeBinaryPayload
          (Nat.binaryRec [] (fun b _ ih => b :: ih) n) = n at ih
        exact congrArg (Nat.bit b) ih

theorem bits_length_le (n : Nat) : (Nat.bits n).length ≤ n := by
  induction n using Nat.binaryRec with
  | zero => simp [Nat.bits]
  | bit b n ih =>
      by_cases hn : n = 0
      · subst n
        cases b <;> simp [Nat.bits, Nat.bit]
      · rw [Nat.bits, Nat.binaryRec_eq b n (Or.inr (fun h => (hn h).elim))]
        change (Nat.binaryRec (motive := fun _ => List Bool) []
          (fun b _ ih => b :: ih) n).length + 1 ≤ Nat.bit b n
        change (Nat.binaryRec (motive := fun _ => List Bool) []
          (fun b _ ih => b :: ih) n).length ≤ n at ih
        cases b <;> simp [Nat.bit] <;> omega

private def decodeLengthPrefix : Bitstring → Nat → Option (Nat × Bitstring)
  | [], _ => none
  | false :: rest, count => some (count, rest)
  | true :: rest, count => decodeLengthPrefix rest (count + 1)

def decodeNat? (bits : Bitstring) : Option (Nat × Bitstring) := do
  let (width, rest) ← decodeLengthPrefix bits 0
  if width ≤ rest.length then
    some (decodeBinaryPayload (rest.take width), rest.drop width)
  else
    none

private theorem decodeLengthPrefix_replicate (width count : Nat)
    (payload rest : Bitstring) :
    decodeLengthPrefix
      (List.replicate width true ++ (false :: (payload ++ rest))) count =
      some (count + width, payload ++ rest) := by
  induction width generalizing count with
  | zero => simp [decodeLengthPrefix]
  | succ width ih =>
      simp only [List.replicate_succ, List.cons_append, decodeLengthPrefix]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (count + 1)

theorem decodeNat?_suffix (n : Nat) (rest : Bitstring) :
    decodeNat? (encodeNat n ++ rest) = some (n, rest) := by
  rw [encodeNat]
  simp only [List.append_assoc, List.cons_append]
  unfold decodeNat?
  rw [decodeLengthPrefix_replicate]
  simp [decodeBinaryPayload_bits]

@[simp] theorem decodeNat?_encodeNat (n : Nat) :
    decodeNat? (encodeNat n) = some (n, []) := by
  simpa using decodeNat?_suffix n []

theorem encodeNat_injective : Function.Injective encodeNat := by
  intro m n h
  have := congrArg decodeNat? h
  simpa using this

@[simp] theorem length_encodeNat (n : Nat) :
    (encodeNat n).length = 2 * (Nat.bits n).length + 1 := by
  simp [encodeNat]
  omega

theorem length_encodeNat_le (n : Nat) :
    (encodeNat n).length ≤ 2 * n + 1 := by
  rw [length_encodeNat]
  have := bits_length_le n
  omega

theorem len_encodeNat_le (n : Nat) :
    len (encodeNat n) ≤ 2 * n + 1 :=
  length_encodeNat_le n

end AvgCaseMls.Foundation
