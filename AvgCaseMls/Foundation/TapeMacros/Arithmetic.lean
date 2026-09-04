import AvgCaseMls.Foundation.TapeMacros.Assembler
import AvgCaseMls.Foundation.TapeMacros.Scan

/-!
# Executable binary arithmetic macros

Binary words are least-significant-bit first, matching `Nat.bits`.  Carry and
borrow therefore move only to the right.  The proofs below account for every
branch, write, move, and halt transition.
-/

namespace AvgCaseMls.Foundation.TapeMacros

open AvgCaseMls.Foundation

def incrementBits : Bitstring → Bitstring
  | [] => [true]
  | false :: rest => true :: rest
  | true :: rest => false :: incrementBits rest

def incrementSteps : Bitstring → Nat
  | [] => 3
  | false :: _ => 3
  | true :: rest => incrementSteps rest + 3

/-- Carry propagation over an LSB-first binary block. -/
def incrementFragment : Fragment :=
  [.branch (.local 4) (.local 1) (.local 2),
   .write (some true) (.local 5),
   .write (some false) (.local 3),
   .moveRight (.local 0),
   .write (some true) (.local 5),
   .halt true]

def incrementMachine : Machine := incrementFragment.machine

private theorem increment_true_step (left : List TapeSymbol)
    (rest : Bitstring) (fuel elapsed : Nat) :
    evalFrom incrementMachine (fuel + 3)
        (blockConfig left (true :: rest)) elapsed =
      evalFrom incrementMachine fuel
        (blockConfig (some false :: left) rest) (elapsed + 3) := by
  cases rest <;>
    simp [incrementMachine, incrementFragment, Fragment.machine,
      Fragment.compileAt, Asm.compile, Target.resolve, blockConfig,
      evalFrom, step, moveRight]

theorem increment_from (left : List TapeSymbol) (bits : Bitstring)
    (elapsed : Nat) :
    evalFrom incrementMachine (incrementSteps bits)
        (blockConfig left bits) elapsed =
      some ⟨true, left.reverse.filterMap id ++ incrementBits bits,
        elapsed + incrementSteps bits⟩ := by
  induction bits generalizing left elapsed with
  | nil =>
      simp [incrementMachine, incrementFragment, Fragment.machine,
        Fragment.compileAt, Asm.compile, Target.resolve, blockConfig,
        incrementSteps, incrementBits, evalFrom, step, tapeOutput]
  | cons bit rest ih =>
      cases bit with
      | false =>
          simp [incrementMachine, incrementFragment, Fragment.machine,
            Fragment.compileAt, Asm.compile, Target.resolve, blockConfig,
            incrementSteps, incrementBits, evalFrom, step, tapeOutput]
      | true =>
          rw [incrementSteps]
          rw [increment_true_step]
          rw [ih]
          congr 2
          · simp [incrementBits, List.filterMap_reverse, List.append_assoc]
          · omega

theorem increment_correct :
    ComputesExactly incrementMachine incrementBits incrementSteps := by
  intro bits
  change evalFrom incrementMachine (incrementSteps bits)
      (blockConfig [] bits) 0 =
    some ⟨true, incrementBits bits, incrementSteps bits⟩
  simpa using increment_from [] bits 0

theorem incrementSteps_le (bits : Bitstring) :
    incrementSteps bits ≤ 3 * bits.length + 3 := by
  induction bits with
  | nil => simp [incrementSteps]
  | cons bit rest ih =>
      cases bit <;> simp [incrementSteps] <;> omega

def decrementBits : Bitstring → Bitstring
  | [] => []
  | false :: rest => true :: decrementBits rest
  | true :: rest => false :: rest

def decrementSteps : Bitstring → Nat
  | [] => 2
  | false :: rest => decrementSteps rest + 3
  | true :: _ => 3

inductive ContainsOne : Bitstring → Prop
  | here (rest) : ContainsOne (true :: rest)
  | there (rest) : ContainsOne rest → ContainsOne (false :: rest)

/-- Borrow propagation; the all-zero/empty underflow path rejects. -/
def decrementFragment : Fragment :=
  [.branch (.local 5) (.local 1) (.local 2),
   .write (some true) (.local 3),
   .write (some false) (.local 4),
   .moveRight (.local 0),
   .halt true,
   .halt false]

def decrementMachine : Machine := decrementFragment.machine

private theorem decrement_false_step (left : List TapeSymbol)
    (rest : Bitstring) (fuel elapsed : Nat) :
    evalFrom decrementMachine (fuel + 3)
        (blockConfig left (false :: rest)) elapsed =
      evalFrom decrementMachine fuel
        (blockConfig (some true :: left) rest) (elapsed + 3) := by
  cases rest <;>
    simp [decrementMachine, decrementFragment, Fragment.machine,
      Fragment.compileAt, Asm.compile, Target.resolve, blockConfig,
      evalFrom, step, moveRight]

theorem decrement_from (left : List TapeSymbol) (bits : Bitstring)
    (elapsed : Nat) (valid : ContainsOne bits) :
    evalFrom decrementMachine (decrementSteps bits)
        (blockConfig left bits) elapsed =
      some ⟨true, left.reverse.filterMap id ++ decrementBits bits,
        elapsed + decrementSteps bits⟩ := by
  induction valid generalizing left elapsed with
  | here rest =>
      simp [decrementMachine, decrementFragment, Fragment.machine,
        Fragment.compileAt, Asm.compile, Target.resolve, blockConfig,
        decrementSteps, decrementBits, evalFrom, step, tapeOutput]
  | there rest valid ih =>
      rw [decrementSteps]
      rw [decrement_false_step]
      rw [ih]
      congr 2
      · simp [decrementBits, List.filterMap_reverse, List.append_assoc]
      · omega

theorem decrement_correct (bits : Bitstring) (valid : ContainsOne bits) :
    eval decrementMachine (decrementSteps bits) bits =
      some ⟨true, decrementBits bits, decrementSteps bits⟩ := by
  change evalFrom decrementMachine (decrementSteps bits)
      (blockConfig [] bits) 0 = _
  simpa using decrement_from [] bits 0 valid

theorem decrementSteps_le (bits : Bitstring) :
    decrementSteps bits ≤ 3 * bits.length + 2 := by
  induction bits with
  | nil => simp [decrementSteps]
  | cons bit rest ih =>
      cases bit <;> simp [decrementSteps] <;> omega

@[simp] theorem incrementFragment_wellFormed :
    incrementFragment.wellFormed := by
  simp [Fragment.wellFormed, incrementFragment, Asm.wellFormed,
    Target.wellFormed]

@[simp] theorem decrementFragment_wellFormed :
    decrementFragment.wellFormed := by
  simp [Fragment.wellFormed, decrementFragment, Asm.wellFormed,
    Target.wellFormed]

end AvgCaseMls.Foundation.TapeMacros
