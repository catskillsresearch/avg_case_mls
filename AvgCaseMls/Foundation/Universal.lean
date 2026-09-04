/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.Foundation.Serialization
import AvgCaseMls.Foundation.Universal.Simulation

namespace AvgCaseMls.Foundation

def encodeInvocation (M : Machine) (fuel : Nat) (input : Bitstring) : Bitstring :=
  Universal.canonicalInvocation M fuel input

def decodeInvocation? (bits : Bitstring) :
    Option (Machine × Nat × Bitstring) := do
  let (M, rest) ← decodeMachine? bits
  let (fuel, rest) ← Universal.decodeInvocationFuel? rest
  let (width, payload) ← decodeNat? rest
  if width = payload.length then some (M, fuel, payload) else none

@[simp] theorem decodeInvocation?_encodeInvocation (M : Machine)
    (fuel : Nat) (input : Bitstring) :
    decodeInvocation? (encodeInvocation M fuel input) =
      some (M, fuel, input) := by
  simp [encodeInvocation, decodeInvocation?, decodeMachine?_suffix,
    Universal.decodeInvocationFuel?_suffix, decodeNat?_suffix,
    Universal.canonicalInvocation, List.append_assoc]

/--
Executable reference interpreter for serialized base machines.  This is the
specification to be implemented by a fixed low-level universal tape machine.
-/
def universalEval (bits : Bitstring) : Option Result := do
  let (M, fuel, input) ← decodeInvocation? bits
  eval M fuel input

theorem universalEval_simulates (M : Machine) (input : Bitstring) (fuel : Nat) :
    universalEval (encodeInvocation M fuel input) = eval M fuel input := by
  simp [universalEval]

@[simp] theorem decodeInvocation?_nil :
    decodeInvocation? [] = none := rfl

@[simp] theorem decodeInvocation?_singleton_true :
    decodeInvocation? [true] = none := rfl

@[simp] theorem decodeInvocation?_unterminatedFuel (M : Machine)
    (fuel : Nat) :
    decodeInvocation?
      (encodeMachine M ++ List.replicate fuel true) = none := by
  simp [decodeInvocation?, decodeMachine?_suffix,
    Universal.decodeInvocationFuel?_unterminated]

@[simp] theorem universalEval_rejects_nil :
    universalEval [] = none := rfl

@[simp] theorem universalEval_rejects_singleton_true :
    universalEval [true] = none := rfl

@[simp] theorem universalEval_rejects_unterminatedFuel (M : Machine)
    (fuel : Nat) :
    universalEval
      (encodeMachine M ++ List.replicate fuel true) = none := by
  simp [universalEval]

/-- Regression for output preservation by a serialized one-instruction halt. -/
theorem universalEval_single_halt (accept : Bool) (input : Bitstring)
    (fuel : Nat) :
    universalEval
      (encodeInvocation ⟨#[.halt accept]⟩ (fuel + 1) input) =
      some ⟨accept, input, 1⟩ := by
  rw [universalEval_simulates]
  cases input <;>
    simp [eval, evalFrom, initial, step, tapeOutput]

def fixedMachineSimulationBound (M : Machine) (n : Nat) : Nat :=
  n + machineWireSize M

theorem fixedMachineSimulationBound_polynomial (M : Machine) :
    IsPolynomial (fixedMachineSimulationBound M) :=
  IsPolynomial.add IsPolynomial.id (IsPolynomial.const (machineWireSize M))

theorem invocation_length_polynomial_bound (M : Machine) (fuel : Nat)
    (input : Bitstring) :
    (encodeInvocation M fuel input).length ≤
      machineWireSize M + (fuel + 1) +
        (2 * input.length + 1) + input.length := by
  unfold encodeInvocation Universal.canonicalInvocation
  simp only [List.length_append]
  change machineWireSize M + (Universal.encodeInvocationFuel fuel).length +
      (encodeNat input.length).length + input.length ≤ _
  have hfuel : (Universal.encodeInvocationFuel fuel).length = fuel + 1 := by
    simp [Universal.encodeInvocationFuel]
  have hinput := length_encodeNat_le input.length
  omega

end AvgCaseMls.Foundation
