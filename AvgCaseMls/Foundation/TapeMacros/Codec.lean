import AvgCaseMls.Foundation.TapeMacros.Scan
import AvgCaseMls.Foundation.Codec

/-!
# Block codecs used by tape macros

These are the mathematical specifications consumed by the low-level machines.
Pairs use the existing self-delimiting natural codec for the first block's
length, so no reserved bit pattern is needed inside either block.
-/

namespace AvgCaseMls.Foundation.TapeMacros

open AvgCaseMls.Foundation

def binaryIndexToUnary (bits : Bitstring) : Bitstring :=
  List.replicate (decodeBinaryPayload bits) false

def unaryToBinaryIndex (bits : Bitstring) : Bitstring :=
  Nat.bits bits.length

@[simp] theorem binaryIndexToUnary_length (bits : Bitstring) :
    (binaryIndexToUnary bits).length = decodeBinaryPayload bits := by
  simp [binaryIndexToUnary]

@[simp] theorem unaryToBinaryIndex_decode (bits : Bitstring) :
    decodeBinaryPayload (unaryToBinaryIndex bits) = bits.length := by
  simp [unaryToBinaryIndex, decodeBinaryPayload_bits]

theorem decodeBinaryPayload_lt_pow (bits : Bitstring) :
    decodeBinaryPayload bits < 2 ^ bits.length := by
  induction bits with
  | nil => simp [decodeBinaryPayload]
  | cons b bits ih =>
      cases b <;> simp [decodeBinaryPayload, Nat.bit, pow_succ] <;> omega

theorem binaryIndexToUnary_length_le_exp (bits : Bitstring) :
    (binaryIndexToUnary bits).length ≤ 2 ^ bits.length :=
  (binaryIndexToUnary_length bits).trans_lt
    (decodeBinaryPayload_lt_pow bits) |>.le

@[simp] theorem unary_binary_roundtrip (n : Nat) :
    unaryToBinaryIndex (List.replicate n false) = Nat.bits n := by
  simp [unaryToBinaryIndex]

@[simp] theorem binary_unary_roundtrip (n : Nat) :
    binaryIndexToUnary (Nat.bits n) = List.replicate n false := by
  simp [binaryIndexToUnary, decodeBinaryPayload_bits]

def pairBlocks (x y : Bitstring) : Bitstring :=
  encodeNat x.length ++ x ++ y

def unpairBlocks? (bits : Bitstring) : Option (Bitstring × Bitstring) := do
  let (width, rest) ← decodeNat? bits
  if width ≤ rest.length then
    some (rest.take width, rest.drop width)
  else
    none

@[simp] theorem unpairBlocks?_pairBlocks (x y : Bitstring) :
    unpairBlocks? (pairBlocks x y) = some (x, y) := by
  simp [pairBlocks, unpairBlocks?, decodeNat?_suffix]

theorem pairBlocks_injective :
    Function.Injective (fun p : Bitstring × Bitstring =>
      pairBlocks p.1 p.2) := by
  intro p q h
  have hu := congrArg unpairBlocks? h
  simpa using hu

@[simp] theorem pairBlocks_length (x y : Bitstring) :
    (pairBlocks x y).length =
      2 * (Nat.bits x.length).length + 1 + x.length + y.length := by
  simp [pairBlocks, length_encodeNat]
  omega

theorem pairBlocks_length_le (x y : Bitstring) :
    (pairBlocks x y).length ≤ 3 * x.length + y.length + 1 := by
  rw [pairBlocks_length]
  have h := bits_length_le x.length
  omega

end AvgCaseMls.Foundation.TapeMacros
