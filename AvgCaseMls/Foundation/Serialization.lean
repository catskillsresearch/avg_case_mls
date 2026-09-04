/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.Foundation.Codec

namespace AvgCaseMls.Foundation

def encodeTapeSymbol : TapeSymbol → Bitstring
  | none => [false, false]
  | some false => [false, true]
  | some true => [true, false]

def decodeTapeSymbol? : Bitstring → Option (TapeSymbol × Bitstring)
  | false :: false :: rest => some (none, rest)
  | false :: true :: rest => some (some false, rest)
  | true :: false :: rest => some (some true, rest)
  | _ => none

@[simp] theorem decodeTapeSymbol?_suffix (s : TapeSymbol) (rest : Bitstring) :
    decodeTapeSymbol? (encodeTapeSymbol s ++ rest) = some (s, rest) := by
  cases s with
  | none => rfl
  | some b => cases b <;> rfl

def encodeInstruction : Instruction → Bitstring
  | .halt accept => [false, false, false, accept]
  | .jump next => [false, false, true] ++ encodeNat next
  | .branch blank zero one =>
      [false, true, false] ++ encodeNat blank ++ encodeNat zero ++ encodeNat one
  | .write symbol next =>
      [false, true, true] ++ encodeTapeSymbol symbol ++ encodeNat next
  | .moveLeft next => [true, false, false] ++ encodeNat next
  | .moveRight next => [true, false, true] ++ encodeNat next

def decodeInstruction? : Bitstring → Option (Instruction × Bitstring)
  | false :: false :: false :: accept :: rest => some (.halt accept, rest)
  | false :: false :: true :: rest => do
      let (next, rest') ← decodeNat? rest
      some (.jump next, rest')
  | false :: true :: false :: rest => do
      let (blank, rest₁) ← decodeNat? rest
      let (zero, rest₂) ← decodeNat? rest₁
      let (one, rest₃) ← decodeNat? rest₂
      some (.branch blank zero one, rest₃)
  | false :: true :: true :: rest => do
      let (symbol, rest₁) ← decodeTapeSymbol? rest
      let (next, rest₂) ← decodeNat? rest₁
      some (.write symbol next, rest₂)
  | true :: false :: false :: rest => do
      let (next, rest') ← decodeNat? rest
      some (.moveLeft next, rest')
  | true :: false :: true :: rest => do
      let (next, rest') ← decodeNat? rest
      some (.moveRight next, rest')
  | _ => none

@[simp] theorem decodeInstruction?_suffix (i : Instruction) (rest : Bitstring) :
    decodeInstruction? (encodeInstruction i ++ rest) = some (i, rest) := by
  cases i <;> simp [encodeInstruction, decodeInstruction?, decodeNat?_suffix]

def encodeInstructions : List Instruction → Bitstring
  | [] => []
  | i :: is => encodeInstruction i ++ encodeInstructions is

def decodeInstructions? : Nat → Bitstring → Option (List Instruction × Bitstring)
  | 0, rest => some ([], rest)
  | n + 1, bits => do
      let (i, rest) ← decodeInstruction? bits
      let (is, rest') ← decodeInstructions? n rest
      some (i :: is, rest')

theorem decodeInstructions?_suffix (is : List Instruction) (rest : Bitstring) :
    decodeInstructions? is.length (encodeInstructions is ++ rest) =
      some (is, rest) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      simp [encodeInstructions, decodeInstructions?, ih]

def encodeMachine (M : Machine) : Bitstring :=
  encodeNat M.code.size ++ encodeInstructions M.code.toList

def decodeMachine? (bits : Bitstring) : Option (Machine × Bitstring) := do
  let (count, rest) ← decodeNat? bits
  let (code, rest') ← decodeInstructions? count rest
  some (⟨code.toArray⟩, rest')

@[simp] theorem decodeMachine?_suffix (M : Machine) (rest : Bitstring) :
    decodeMachine? (encodeMachine M ++ rest) = some (M, rest) := by
  cases M with
  | mk code =>
      unfold encodeMachine decodeMachine?
      rw [List.append_assoc, decodeNat?_suffix]
      have hdecode :
          decodeInstructions? code.size (encodeInstructions code.toList ++ rest) =
            some (code.toList, rest) := by
        simpa using decodeInstructions?_suffix code.toList rest
      change (decodeInstructions? code.size
        (encodeInstructions code.toList ++ rest)).bind
          (fun pair => some (({ code := pair.1.toArray } : Machine), pair.2)) =
        some (({ code := code } : Machine), rest)
      rw [hdecode]
      simp

def encodeTapeSymbols (xs : List TapeSymbol) : Bitstring :=
  encodeNat xs.length ++ xs.flatMap encodeTapeSymbol

def decodeTapeSymbolsBody? : Nat → Bitstring → Option (List TapeSymbol × Bitstring)
  | 0, rest => some ([], rest)
  | n + 1, bits => do
      let (x, rest) ← decodeTapeSymbol? bits
      let (xs, rest') ← decodeTapeSymbolsBody? n rest
      some (x :: xs, rest')

def decodeTapeSymbols? (bits : Bitstring) : Option (List TapeSymbol × Bitstring) := do
  let (count, rest) ← decodeNat? bits
  decodeTapeSymbolsBody? count rest

private theorem decodeTapeSymbolsBody?_suffix (xs : List TapeSymbol)
    (rest : Bitstring) :
    decodeTapeSymbolsBody? xs.length (xs.flatMap encodeTapeSymbol ++ rest) =
      some (xs, rest) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [decodeTapeSymbolsBody?, ih]

@[simp] theorem decodeTapeSymbols?_suffix (xs : List TapeSymbol)
    (rest : Bitstring) :
    decodeTapeSymbols? (encodeTapeSymbols xs ++ rest) = some (xs, rest) := by
  simp [encodeTapeSymbols, decodeTapeSymbols?, decodeNat?_suffix,
    decodeTapeSymbolsBody?_suffix]

def encodeConfig (c : Config) : Bitstring :=
  encodeNat c.pc ++ encodeTapeSymbols c.left ++ encodeTapeSymbol c.head ++
    encodeTapeSymbols c.right

def decodeConfig? (bits : Bitstring) : Option (Config × Bitstring) := do
  let (pc, rest₁) ← decodeNat? bits
  let (left, rest₂) ← decodeTapeSymbols? rest₁
  let (head, rest₃) ← decodeTapeSymbol? rest₂
  let (right, rest₄) ← decodeTapeSymbols? rest₃
  some (⟨pc, left, head, right⟩, rest₄)

@[simp] theorem decodeConfig?_suffix (c : Config) (rest : Bitstring) :
    decodeConfig? (encodeConfig c ++ rest) = some (c, rest) := by
  cases c
  simp [encodeConfig, decodeConfig?, decodeNat?_suffix,
    decodeTapeSymbols?_suffix, List.append_assoc]

def programDepth : Program → Nat
  | .machine _ | .constant _ _ | .encodeLength => 1
  | .compose p q => max (programDepth p) (programDepth q) + 1
  | .branch p q r =>
      max (programDepth p) (max (programDepth q) (programDepth r)) + 1

def encodeProgram : Program → Bitstring
  | .machine M => [false, false, false] ++ encodeMachine M
  | .constant accept output =>
      [false, false, true, accept] ++ encodeNat output.length ++ output
  | .encodeLength => [false, true, false]
  | .compose p q => [false, true, true] ++ encodeProgram p ++ encodeProgram q
  | .branch p q r =>
      [true, false, false] ++ encodeProgram p ++ encodeProgram q ++ encodeProgram r

def decodeProgramFuel : Nat → Bitstring → Option (Program × Bitstring)
  | 0, _ => none
  | fuel + 1, false :: false :: false :: rest => do
      let (M, rest') ← decodeMachine? rest
      some (.machine M, rest')
  | fuel + 1, false :: false :: true :: accept :: rest => do
      let (width, rest') ← decodeNat? rest
      if width ≤ rest'.length then
        some (.constant accept (rest'.take width), rest'.drop width)
      else none
  | _, false :: true :: false :: rest => some (.encodeLength, rest)
  | fuel + 1, false :: true :: true :: rest => do
      let (p, rest₁) ← decodeProgramFuel fuel rest
      let (q, rest₂) ← decodeProgramFuel fuel rest₁
      some (.compose p q, rest₂)
  | fuel + 1, true :: false :: false :: rest => do
      let (p, rest₁) ← decodeProgramFuel fuel rest
      let (q, rest₂) ← decodeProgramFuel fuel rest₁
      let (r, rest₃) ← decodeProgramFuel fuel rest₂
      some (.branch p q r, rest₃)
  | _, _ => none

theorem decodeProgramFuel_suffix (p : Program) (rest : Bitstring) (fuel : Nat)
    (h : programDepth p ≤ fuel) :
    decodeProgramFuel fuel (encodeProgram p ++ rest) = some (p, rest) := by
  induction p generalizing rest fuel with
  | machine M =>
      cases fuel with
      | zero => simp [programDepth] at h
      | succ fuel => simp [encodeProgram, decodeProgramFuel]
  | constant accept output =>
      cases fuel with
      | zero => simp [programDepth] at h
      | succ fuel =>
          simp [encodeProgram, decodeProgramFuel, decodeNat?_suffix]
  | encodeLength =>
      cases fuel with
      | zero => simp [programDepth] at h
      | succ fuel => rfl
  | compose p q ihp ihq =>
      cases fuel with
      | zero => simp [programDepth] at h
      | succ fuel =>
          have hp : programDepth p ≤ fuel := by
            simp [programDepth] at h
            omega
          have hq : programDepth q ≤ fuel := by
            simp [programDepth] at h
            omega
          simp [encodeProgram, decodeProgramFuel, ihp _ _ hp, ihq _ _ hq]
  | branch p q r ihp ihq ihr =>
      cases fuel with
      | zero => simp [programDepth] at h
      | succ fuel =>
          have hp : programDepth p ≤ fuel := by
            simp [programDepth] at h
            omega
          have hq : programDepth q ≤ fuel := by
            simp [programDepth] at h
            omega
          have hr : programDepth r ≤ fuel := by
            simp [programDepth] at h
            omega
          simp [encodeProgram, decodeProgramFuel, ihp _ _ hp,
            ihq _ _ hq, ihr _ _ hr, List.append_assoc]

def decodeProgram? (bits : Bitstring) : Option (Program × Bitstring) :=
  decodeProgramFuel (bits.length + 1) bits

theorem programDepth_le_length_encodeProgram (p : Program) :
    programDepth p ≤ (encodeProgram p).length := by
  induction p with
  | machine M => simp [programDepth, encodeProgram]
  | constant accept output => simp [programDepth, encodeProgram]
  | encodeLength => simp [programDepth, encodeProgram]
  | compose p q ihp ihq =>
      simp [programDepth, encodeProgram]
      omega
  | branch p q r ihp ihq ihr =>
      simp [programDepth, encodeProgram]
      omega

@[simp] theorem decodeProgram?_encodeProgram (p : Program) :
    decodeProgram? (encodeProgram p) = some (p, []) := by
  unfold decodeProgram?
  rw [show encodeProgram p = encodeProgram p ++ [] by simp]
  apply decodeProgramFuel_suffix
  simpa using (programDepth_le_length_encodeProgram p).trans
    (Nat.le_add_right (encodeProgram p).length 1)

def machineWireSize (M : Machine) : Nat := (encodeMachine M).length
def configWireSize (c : Config) : Nat := (encodeConfig c).length
def programWireSize (p : Program) : Nat := (encodeProgram p).length
def wireSizeBound (n : Nat) : Nat := n

theorem wireSizeBound_polynomial : IsPolynomial wireSizeBound :=
  IsPolynomial.id

@[simp] theorem encodeMachine_length (M : Machine) :
    (encodeMachine M).length = machineWireSize M := rfl

@[simp] theorem encodeConfig_length (c : Config) :
    (encodeConfig c).length = configWireSize c := rfl

@[simp] theorem encodeProgram_length (p : Program) :
    (encodeProgram p).length = programWireSize p := rfl

theorem encodeMachine_length_le (M : Machine) :
    (encodeMachine M).length ≤ wireSizeBound (machineWireSize M) := le_rfl

theorem encodeConfig_length_le (c : Config) :
    (encodeConfig c).length ≤ wireSizeBound (configWireSize c) := le_rfl

theorem encodeProgram_length_le (p : Program) :
    (encodeProgram p).length ≤ wireSizeBound (programWireSize p) := le_rfl

end AvgCaseMls.Foundation
